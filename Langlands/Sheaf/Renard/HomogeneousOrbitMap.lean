import Langlands.Sheaf.Renard.HomogeneousSections
import Langlands.Sheaf.Renard.SmoothInverseImage
import Langlands.Group.LeftQuotientInversion

/-!
# The canonical orbit map in Renard's inverse-right quotient convention

The map uses the original left quotient and the published inversion
homeomorphism. Its pullback uses the actual equivariant inverse image.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.HomogeneousOrbitMap

open CategoryTheory
open Langlands.Induction
open Langlands.Sheaf.Renard.HomogeneousSections
open Langlands.Sheaf.Renard.SectionActions

universe uG uX

attribute [local instance] homogeneousAction

section Map

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : Type uX} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
variable (x : X)

/-- The canonical orbit map `Hg ↦ g⁻¹ • x` on the original inverse-right base. -/
def map : C(LeftQuotient (MulAction.stabilizer G x), X) where
  toFun := MulAction.ofQuotientStabilizer G x ∘
    quotientInversion (MulAction.stabilizer G x)
  continuous_toFun := by
    apply (Langlands.QuotientIntegration.leftQuotient_isOpenQuotientMap
      (MulAction.stabilizer G x)).isQuotientMap.continuous_iff.mpr
    change Continuous (fun g : G => g⁻¹ • x)
    exact continuous_inv.smul continuous_const

@[simp]
theorem map_quotientMap (g : G) :
    map x (quotientMap (MulAction.stabilizer G x) g) = g⁻¹ • x := rfl

@[simp]
theorem map_origin : map x (origin (MulAction.stabilizer G x)) = x := by
  change (1 : G)⁻¹ • x = x
  simp

/-- The chosen inverse converts right translation into the given left action. -/
theorem map_equivariant (g : G) (z : LeftQuotient (MulAction.stabilizer G x)) :
    map x (g • z) = g • map x z := by
  induction z using Quotient.inductionOn with
  | h k =>
    change (k * g⁻¹)⁻¹ • x = g • (k⁻¹ • x)
    simp only [mul_inv_rev, inv_inv, mul_smul]

/-- It is the original canonical orbit map after the published inversion homeomorphism. -/
theorem map_factor :
    (map x : LeftQuotient (MulAction.stabilizer G x) → X) =
      MulAction.ofQuotientStabilizer G x ∘
        quotientInversion (MulAction.stabilizer G x) := rfl

/-- Orbit-stabilizer injectivity concerns this exact map. -/
theorem map_injective : Function.Injective (map (G := G) x) :=
  (MulAction.injective_ofQuotientStabilizer G x).comp
    (quotientInversion (MulAction.stabilizer G x)).injective

/-- Transitivity makes the canonical map surjective without a topological conclusion. -/
theorem map_surjective [MulAction.IsPretransitive G X] :
    Function.Surjective (map (G := G) x) := by
  intro y
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  refine ⟨quotientMap (MulAction.stabilizer G x) g⁻¹, ?_⟩
  simpa only [map_quotientMap, inv_inv] using hg

/-- The underlying set equivalence of a transitive action, on the same quotient carrier. -/
def transitiveEquiv [MulAction.IsPretransitive G X] :
    LeftQuotient (MulAction.stabilizer G x) ≃ X :=
  Equiv.ofBijective (map (G := G) x)
    ⟨map_injective (G := G) x, map_surjective (G := G) x⟩

@[simp]
theorem transitiveEquiv_apply [MulAction.IsPretransitive G X]
    (z : LeftQuotient (MulAction.stabilizer G x)) :
    transitiveEquiv x z = map x z := rfl

omit [IsTopologicalGroup G] in
/-- Hausdorffness makes the actual point stabilizer closed. -/
theorem stabilizer_closed [T2Space X] :
    IsClosed (MulAction.stabilizer G x : Set G) := by
  exact isClosed_eq (continuous_id.smul continuous_const) continuous_const

/-- The original inverse-right homogeneous base retains the t.d. hypotheses. -/
theorem quotient_isLocallyProfinite
    (hG : Langlands.Topology.IsLocallyProfinite G)
    (hX : Langlands.Topology.IsLocallyProfinite X) :
    Langlands.Topology.IsLocallyProfinite
      (LeftQuotient (MulAction.stabilizer G x)) := by
  let := hX.t2Space
  exact HomogeneousSections.quotient_isLocallyProfinite _
    hG (stabilizer_closed x)

end Map

section Pullback

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
variable (x : X)

/-- Pull back along the actual orbit map; no homeomorphism is assumed. -/
def pullback :
    ActionSheaf G X ⥤ ActionSheaf G (LeftQuotient (MulAction.stabilizer G x)) :=
  actionInverseImage (map x) (map_equivariant x)

/-- The same actual inverse image on Renard smooth-action sheaves. -/
def smoothPullback
    (hG : Langlands.Topology.IsLocallyProfinite G)
    (hX : Langlands.Topology.IsLocallyProfinite X) :
    SmoothActionSheaf G X ⥤
      SmoothActionSheaf G (LeftQuotient (MulAction.stabilizer G x)) :=
  smoothActionInverseImage (map x) (map_equivariant x) hG hX

/-- Forgetting smoothness retains the original orbit inverse image and its maps. -/
def smoothPullbackToActionIso
    (hG : Langlands.Topology.IsLocallyProfinite G)
    (hX : Langlands.Topology.IsLocallyProfinite X) :
    smoothPullback x hG hX ⋙
        smoothActionInclusion G (LeftQuotient (MulAction.stabilizer G x)) ≅
      smoothActionInclusion G X ⋙ pullback x :=
  smoothActionInverseImageToActionIso (map x) (map_equivariant x) hG hX

end Pullback

end Langlands.Sheaf.Renard.HomogeneousOrbitMap
