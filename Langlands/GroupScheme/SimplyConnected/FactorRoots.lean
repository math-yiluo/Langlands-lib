import Langlands.GroupScheme.SimplyConnected.FactorMaximalTorus
import Langlands.GroupScheme.SimplyConnected.RootFactorPlacement
import Langlands.GroupScheme.Lie.TargetCoefficients
import Langlands.GroupScheme.Rational.RootParabolicProper

/-! # Actual roots of compatible maximal tori in product factors -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : SimplyConnectedAlmostSimpleProduct G)

private instance factorRoots_factorAffine (i : D.Index) : IsAffineHom (D.factor i).X.hom :=
  (D.isSimplyConnected i).isSemisimple.isConnectedReductive.isAffineHom

private instance factorRoots_factorSmooth (i : D.Index) : Smooth (D.factor i).X.hom :=
  (D.isSimplyConnected i).isSemisimple.isConnectedReductive.smooth

/-- On actual tangent vectors, the original factor inclusion and projection
remain a retraction. -/
theorem lie_inclusion_projection (i : D.Index) (X : Additive (lieKernel (D.factor i) k)) :
    Lie.targetMapLinear (D.projection i) k (Lie.targetMapLinear (D.inclusion i) k X) = X := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact D.inclusion_projection_points_self i X.toMul.val

/-- Projection to another factor kills the whole differential image of a
factor, on the original dual-number tangent points. -/
theorem lie_projection_eq_zero_of_mem_other (i j : D.Index) (hji : j ≠ i)
    {X : Additive (lieKernel G k)}
    (hX : X ∈ LinearMap.range (Lie.targetMapLinear (D.inclusion j) k)) :
    Lie.targetMapLinear (D.projection i) k X = 0 := by
  obtain ⟨Y, rfl⟩ := hX
  apply Additive.toMul.injective
  apply Subtype.ext
  exact D.inclusion_projection_points_ne j i hji Y.toMul.val

/-- The differential of a factor projection is injective on the actual
Lie-image of its original factor inclusion. -/
theorem lie_projection_ne_zero_of_mem_factor (i : D.Index)
    {X : Additive (lieKernel G k)}
    (hX : X ∈ LinearMap.range (Lie.targetMapLinear (D.inclusion i) k)) (hX0 : X ≠ 0) :
    Lie.targetMapLinear (D.projection i) k X ≠ 0 := by
  obtain ⟨Y, rfl⟩ := hX
  rw [D.lie_inclusion_projection]
  intro h0
  apply hX0
  rw [h0, map_zero]

variable (hG : IsSemisimple G)
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)

/-- Every vector of an actual ambient root weight lies in the differential
image of the unique factor carrying that root subgroup. -/
theorem weightSpace_le_rootFactor_lieImage {α : characterLattice T} (hα : α ∈ roots t) :
    weightSpace t α ≤ LinearMap.range (Lie.targetMapLinear
      (D.inclusion (D.rootFactorIndex hG hT t ht hα)) k) := by
  let := hG.isConnectedReductive.smooth
  let i := D.rootFactorIndex hG hT t ht hα
  have : IsClosedImmersion (D.inclusion i).hom.hom.left := D.isClosedSubgroup_inclusion i
  have : Mono (D.inclusion i).hom.hom := Over.mono_of_mono_left _
  rw [← RelativeRoot.tangentSubmodule_range]
  exact (RelativeRoot.weightSpace_le_tangentSubmodule_subgroup t hT hα.1).trans
    (RelativeRoot.tangentSubmodule_mono (D.root_subgroup_le_rootFactorIndex hG hT t ht hα))

namespace FactorMaximalTorus

variable {D t} {i : D.Index} (F : D.FactorMaximalTorus t i)

/-- The actual split projection as a homomorphism of commutative group schemes. -/
def projectionHom : T ⟶ F.torus := Additive.ofMul F.projection

omit [IsAffineHom G.X.hom] in
/-- The ambient-torus insertion followed by its factor projection is the
identity on the actual factor torus. -/
theorem torusHom_projectionHom : F.torusHom ≫ F.projectionHom = 𝟙 F.torus :=
  congrArg Additive.ofMul F.projection_section

omit [IsAffineHom G.X.hom] in
/-- Character pullback from the factor torus is injective. -/
theorem characterPullback_injective :
    Function.Injective (fun β : characterLattice F.torus => F.projectionHom ≫ β) := by
  intro b c h
  have h' := congrArg (fun a => F.torusHom ≫ a) h
  simpa only [← Category.assoc, F.torusHom_projectionHom, Category.id_comp] using h'

/-- A factor root inflates to an actual ambient root carried by the same
original product factor. -/
theorem root_inflation (β : characterLattice F.torus) (hβ : β ∈ roots F.subgroupHom) :
    ∃ hα : F.projectionHom ≫ β ∈ roots t,
      D.rootFactorIndex hG hT t ht hα = i := by
  let := hG.isConnectedReductive.smooth
  have hα0 : F.projectionHom ≫ β ≠ 0 := by
    intro hz
    apply hβ.1
    apply F.characterPullback_injective
    simpa only [Limits.comp_zero] using hz
  obtain ⟨Y, hY, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hβ.2
  have hY' : Y ∈ weightSpace (t ≫ D.projection i) (F.projectionHom ≫ β) := by
    rw [← F.projection_comp]
    exact weightSpace_le_comp F.projectionHom F.subgroupHom β hY
  have hYrange : Y ∈ LinearMap.range (Lie.targetMapLinear (D.projection i) k) :=
    ⟨Lie.targetMapLinear (D.inclusion i) k Y, D.lie_inclusion_projection i Y⟩
  obtain ⟨X, hX, hXY⟩ := Lie.exists_weightSpace_preimage (D.projection i) t hT hY' hYrange
  have hα : F.projectionHom ≫ β ∈ roots t := by
    refine ⟨hα0, ?_⟩
    intro hbot
    rw [hbot, Submodule.mem_bot] at hX
    rw [hX, map_zero] at hXY
    exact hY0 hXY.symm
  refine ⟨hα, ?_⟩
  by_contra hne
  have hzero := D.lie_projection_eq_zero_of_mem_other i _ hne
    (D.weightSpace_le_rootFactor_lieImage hG hT t ht hα hX)
  rw [hXY] at hzero
  exact hY0 hzero

/-- Every ambient root carried by this factor is the pullback of an actual
root of the retained compatible factor torus. -/
theorem root_restriction {α : characterLattice T} (hα : α ∈ roots t)
    (hi : D.rootFactorIndex hG hT t ht hα = i) :
    ∃ β ∈ roots F.subgroupHom, F.projectionHom ≫ β = α := by
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  have hXrange : X ∈ LinearMap.range (Lie.targetMapLinear (D.inclusion i) k) := by
    rw [← hi]
    exact D.weightSpace_le_rootFactor_lieImage hG hT t ht hα hX
  have hY0 := D.lie_projection_ne_zero_of_mem_factor i hXrange hX0
  have hY := lieKernelHomLinear_mem_weightSpace (D.projection i) t α hX
  rw [← F.projection_comp] at hY
  change Lie.targetMapLinear (D.projection i) k X ∈
    weightSpace (CommGroupScheme.groupHom F.projectionHom ≫ F.subgroupHom) α at hY
  have hα' : α ∈ roots (CommGroupScheme.groupHom F.projectionHom ≫ F.subgroupHom) := by
    refine ⟨hα.1, ?_⟩
    intro hbot
    rw [hbot, Submodule.mem_bot] at hY
    exact hY0 hY
  exact ((mem_roots_comp_iff F.split hT F.projectionHom F.subgroupHom α).mp hα').2

/-- Literal character pullback identifies all roots of the actual factor
with all ambient roots assigned to it, without replacing the root supports. -/
def rootEquiv : roots F.subgroupHom ≃
    {α : roots t // D.rootFactorIndex hG hT t ht α.property = i} :=
  Equiv.ofBijective
    (fun β => ⟨⟨F.projectionHom ≫ β.val, (F.root_inflation hG hT ht β.val β.property).choose⟩,
      (F.root_inflation hG hT ht β.val β.property).choose_spec⟩)
    ⟨fun b c h => Subtype.ext (F.characterPullback_injective
      (congrArg (fun x => x.val.val) h)), by
      intro α
      obtain ⟨β, hβ, hβα⟩ := F.root_restriction hG hT ht α.val.property α.property
      exact ⟨⟨β, hβ⟩, Subtype.ext (Subtype.ext hβα)⟩⟩

@[simp] theorem rootEquiv_val (β : roots F.subgroupHom) :
    (F.rootEquiv hG hT ht β).val.val = F.projectionHom ≫ β.val := rfl

end FactorMaximalTorus
end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
