import Langlands.GroupScheme.CentralIsogeny.SemisimpleKernel
import Langlands.GroupScheme.Lie.FieldExtension
import Langlands.GroupScheme.Reductive.CenterBaseChangeProof
import Langlands.GroupScheme.GeometricConnectedness

/-! # The exact centre-tangent kernel after field extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

section Ring

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A]
    [IsScalarTower k K A]

local notation "b" => algebraBaseMap k K
local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G
local notation "Q_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) Q

local instance geometricSemisimpleKernel_ringSource_isAffineHom : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

local instance geometricSemisimpleKernel_ringTarget_isAffineHom : IsAffineHom (Q_K).X.hom := by
  change IsAffineHom (pullback.snd Q.X.hom b)
  infer_instance

/-- Membership in any subgroup tangent submodule agrees under the actual
scheme-pullback tangent comparison. -/
theorem SubgroupFunctor.mem_lie_baseChange_iff
    (F : SubgroupFunctor G) (X : Additive (lieKernel G_K A)) :
    X ∈ (F.baseChange b).lie A ↔
      Lie.kernelBaseChangeLinearEquiv k K G A X ∈ F.lie A := by
  rw [SubgroupFunctor.mem_lie, SubgroupFunctor.mem_lie,
    SubgroupFunctor.mem_baseChange]
  change baseChangePointsEquiv b G _ X.toMul.val ∈ F.carrier _ ↔
    (Lie.affineBaseTestIso k K (DualNumber A)).inv ≫
      baseChangePointsEquiv b G _ X.toMul.val ∈ F.carrier _
  constructor
  · exact F.comp_mem _
  · intro h
    have hh := F.comp_mem (Lie.affineBaseTestIso k K (DualNumber A)).hom h
    simpa only [Iso.hom_inv_id_assoc] using hh

/-- The actual linear scheme-pullback comparison intertwines differentials. -/
theorem Lie.kernelBaseChangeLinearEquiv_target (q : G ⟶ Q)
    (X : Additive (lieKernel G_K A)) :
    Lie.kernelBaseChangeLinearEquiv k K Q A
        (Lie.targetMapLinear ((GroupScheme.baseChange b).map q) A X) =
      Lie.targetMapLinear q A (Lie.kernelBaseChangeLinearEquiv k K G A X) :=
  congrArg Additive.ofMul (Lie.kernelBaseChangeEquiv_target (k := k) (K := K) q X.toMul)

/-- Exact equality with the full-centre tangent kernel survives arbitrary
commutative extension of the scheme base. -/
theorem ker_targetMapLinear_baseChange_eq_center_lie
    (q : G ⟶ Q)
    (hker : LinearMap.ker (Lie.targetMapLinear q A) = (center G).lie A) :
    LinearMap.ker
        (Lie.targetMapLinear ((GroupScheme.baseChange b).map q) A) =
      (center G_K).lie A := by
  apply Submodule.ext
  intro X
  rw [center_baseChange, SubgroupFunctor.mem_lie_baseChange_iff,
    ← hker, LinearMap.mem_ker, LinearMap.mem_ker,
    ← Lie.kernelBaseChangeLinearEquiv_target k K A]
  exact (Lie.kernelBaseChangeLinearEquiv k K Q A).map_eq_zero_iff.symm

end Ring

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]

local notation "b" => algebraBaseMap k K
local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G
local notation "Q_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) Q

local instance geometricSemisimpleKernel_fieldSource_isAffineHom : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

local instance geometricSemisimpleKernel_fieldTarget_isAffineHom : IsAffineHom (Q_K).X.hom := by
  change IsAffineHom (pullback.snd Q.X.hom b)
  infer_instance

local instance geometricSemisimpleKernel_fieldSource_smooth : Smooth (G_K).X.hom := by
  change Smooth (pullback.snd G.X.hom b)
  infer_instance

local instance geometricSemisimpleKernel_fieldSource_connectedSpace : ConnectedSpace (G_K).X.left :=
  G.connectedSpace_baseChange_of_smooth_affine b

/-- The same base-field quotient detects full Lie centralizers of semisimple
vectors after any field extension, including algebraic closure. -/
theorem Lie.targetMap_baseChange_eq_one_iff_elementCentralizerLie_eq_top
    (q : G ⟶ Q)
    (hker : LinearMap.ker (Lie.targetMapLinear q K) = (center G).lie K)
    {X : lieKernel G_K K} (hX : Lie.IsSemisimpleElement G_K X) :
    Lie.targetMap ((GroupScheme.baseChange b).map q) K X = 1 ↔
      Lie.elementCentralizerLie G_K X = ⊤ :=
  Lie.targetMap_eq_one_iff_elementCentralizerLie_eq_top
    ((GroupScheme.baseChange b).map q)
    (ker_targetMapLinear_baseChange_eq_center_lie k K K q hker) hX

end Field

/-- Universal simultaneous field-extension version of the central semisimple
kernel construction. -/
def GeometricCentralSemisimpleKernelStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [ExpChar k p],
    1 < p →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q)
        (_ : Smooth Q.X.hom) (ha : IsAffineHom Q.X.hom)
        (_ : ConnectedSpace Q.X.left),
        letI : IsAffineHom Q.X.hom := ha
        IsCentralIsogeny q ∧
          (∀ (A : Type u) [CommRing A] [Algebra k A],
            LinearMap.ker (Lie.targetMapLinear q A) = (center G).lie A) ∧
          ∀ (K : Type u) [Field K] [Algebra k K],
            let G_K := (GroupScheme.baseChange (algebraBaseMap k K)).obj G
            letI : IsAffineHom (G_K).X.hom := by
              change IsAffineHom (pullback.snd G.X.hom _)
              infer_instance
            ∀ (X : lieKernel G_K K), Lie.IsSemisimpleElement G_K X →
              (Lie.targetMap
                ((GroupScheme.baseChange (algebraBaseMap k K)).map q) K X = 1 ↔
                  Lie.elementCentralizerLie G_K X = ⊤)

theorem geometricCentralSemisimpleKernel :
    GeometricCentralSemisimpleKernelStatement.{u} := by
  intro k _ p _ hp G _ _ _
  obtain ⟨Q, q, hs, ha, hc, hq, hker⟩ :=
    exists_connected_centralIsogeny_ker_targetMapLinear_eq_center_lie k p hp G
  refine ⟨Q, q, hs, ha, hc, hq, hker, ?_⟩
  intro K _ _
  dsimp only
  intro X hX
  exact Lie.targetMap_baseChange_eq_one_iff_elementCentralizerLie_eq_top q (hker K) hX

end Langlands.GroupScheme
