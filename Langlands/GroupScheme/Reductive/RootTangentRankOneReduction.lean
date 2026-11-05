import Langlands.GroupScheme.Reductive.RootReducednessReduction
import Langlands.GroupScheme.Rational.RootSubgroupLieImage

/-! # Full intrinsic root tangents and generic rank-one centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RootReducedness

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G L : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom L.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G) (ζ : cocharacterLattice T) {j : L ⟶ G}
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)

include hj

/-- For any character pairing to zero with the cocharacter, the actual
centralizer differential identifies its weight space with the ambient one. -/
theorem map_weightSpace_torusFactor {α : characterLattice T}
    (hα : latticePairing T α ζ = 0) :
    (weightSpace (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) α).map
      (Lie.targetMapLinear j k) = weightSpace i α := by
  have : Mono j.hom.hom := hj.1
  apply le_antisymm
  · rintro X ⟨Y, hY, rfl⟩
    have h := lieKernelHomLinear_mem_weightSpace j
      (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) α hY
    rwa [Dynamic.torusFactor_comp] at h
  · intro X hX
    obtain ⟨Y, hY⟩ := weightSpace_le_range_centralizer i ζ hj hα hX
    refine ⟨Y, ?_, hY⟩
    apply (lieKernelHomLinear_mem_weightSpace_iff j
      (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) α Y).mp
    rw [Dynamic.torusFactor_comp, hY]
    exact hX

/-- The same differential identifies the entire positive integral weight span,
including every positive multiple of the specified character. -/
theorem map_positiveWeightSpan_torusFactor {α : characterLattice T}
    (hα : latticePairing T α ζ = 0) :
    (RelativeRoot.positiveWeightSpan
      (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) α).map
      (Lie.targetMapLinear j k) = RelativeRoot.positiveWeightSpan i α := by
  rw [RelativeRoot.positiveWeightSpan, RelativeRoot.positiveWeightSpan, Submodule.map_iSup]
  apply iSup_congr
  intro n
  apply map_weightSpace_torusFactor i ζ hj
  rw [map_nsmul]
  change n.val • latticePairing T α ζ = 0
  rw [hα, nsmul_zero]

/-- The equivalence on the whole positive integral span is induced by the
actual centralizer inclusion, rather than an arbitrary vector-space choice. -/
def positiveWeightSpanTorusFactorEquiv {α : characterLattice T}
    (hα : latticePairing T α ζ = 0) :
    RelativeRoot.positiveWeightSpan
      (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) α ≃ₗ[k]
        RelativeRoot.positiveWeightSpan i α := by
  have : Mono j.hom.hom := hj.1
  exact (Submodule.equivMapOfInjective (Lie.targetMapLinear j k)
    (Lie.targetMapLinear_injective j k)
    (RelativeRoot.positiveWeightSpan
      (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) α)).trans
        (LinearEquiv.ofEq _ _ (map_positiveWeightSpan_torusFactor i ζ hj hα))

@[simp] theorem positiveWeightSpanTorusFactorEquiv_coe {α : characterLattice T}
    (hα : latticePairing T α ζ = 0)
    (X : RelativeRoot.positiveWeightSpan
      (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) α) :
    (positiveWeightSpanTorusFactorEquiv i ζ hj hα X : Additive (lieKernel G k)) =
      Lie.targetMapLinear j k X := rfl

/-- The actual centralizer differential identifies the full intrinsic root
tangent when the character vanishes on its cocharacter. -/
theorem map_rootTangent_torusFactor [Smooth G.X.hom] [Smooth L.X.hom]
    (hT : IsSplitTorus T.toGrp) {α : characterLattice T} (hα : α ≠ 0)
    (hαζ : latticePairing T α ζ = 0) :
    (RelativeRoot.tangentSubmodule (RelativeRoot.subgroup
      (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) α)).map
      (Lie.targetMapLinear j k) =
        RelativeRoot.tangentSubmodule (RelativeRoot.subgroup i α) := by
  rw [RelativeRoot.tangentSubmodule_subgroup _ _ hT hα,
    RelativeRoot.tangentSubmodule_subgroup _ _ hT hα,
    RelativeRoot.semigroupWeightSpan, RelativeRoot.semigroupWeightSpan, Submodule.map_iSup]
  apply iSup_congr
  intro χ
  rw [RelativeRoot.actionWeightSpace_conjugation, RelativeRoot.actionWeightSpace_conjugation]
  apply map_weightSpace_torusFactor i ζ hj
  obtain ⟨n, _, _, hχ⟩ := χ.property
  rw [← hχ, map_nsmul]
  change n • latticePairing T α ζ = 0
  rw [hαζ, nsmul_zero]

/-- Canonical equivalence of the unchanged intrinsic root tangents through
the actual centralizer differential. No root reducedness is assumed. -/
def rootTangentTorusFactorEquiv [Smooth G.X.hom] [Smooth L.X.hom]
    (hT : IsSplitTorus T.toGrp) {α : characterLattice T} (hα : α ≠ 0)
    (hαζ : latticePairing T α ζ = 0) :
    RelativeRoot.tangentSubmodule (RelativeRoot.subgroup
      (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) α) ≃ₗ[k]
        RelativeRoot.tangentSubmodule (RelativeRoot.subgroup i α) := by
  have : Mono j.hom.hom := hj.1
  exact (Submodule.equivMapOfInjective (Lie.targetMapLinear j k)
    (Lie.targetMapLinear_injective j k)
    (RelativeRoot.tangentSubmodule (RelativeRoot.subgroup
      (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) α))).trans
        (LinearEquiv.ofEq _ _ (map_rootTangent_torusFactor i ζ hj hT hα hαζ))

@[simp] theorem rootTangentTorusFactorEquiv_coe [Smooth G.X.hom] [Smooth L.X.hom]
    (hT : IsSplitTorus T.toGrp) {α : characterLattice T} (hα : α ≠ 0)
    (hαζ : latticePairing T α ζ = 0)
    (X : RelativeRoot.tangentSubmodule (RelativeRoot.subgroup
      (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) α)) :
    (rootTangentTorusFactorEquiv i ζ hj hT hα hαζ X : Additive (lieKernel G k)) =
      Lie.targetMapLinear j k X := rfl

end RootReducedness

open RootReducedness in
/-- A bound for the full intrinsic root tangent in every proportional-root
centralizer implies the general bound. Centralizer reductivity and the
rank-one bound are retained as explicit inputs. -/
theorem finrank_rootTangent_le_one_of_rankOne
    (hcent : DynamicCentralizerReductiveStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (hrank : ∀ (L : GroupScheme (Spec (CommRingCat.of k))) (hL : IsConnectedReductive L)
      (iL : T.toGrp ⟶ L), IsMaximalTorus iL →
      haveI := hL.isAffineHom
      (∀ β ∈ roots iL, ∀ γ ∈ roots iL, ¬ LinearIndependent ℤ ![β, γ]) →
      ∀ α ∈ roots iL, Module.finrank k
        (RelativeRoot.tangentSubmodule (RelativeRoot.subgroup iL α)) ≤ 1)
    {α : characterLattice T}
    (hα : haveI := hG.isAffineHom
      α ∈ roots i) :
    haveI := hG.isAffineHom
    Module.finrank k (RelativeRoot.tangentSubmodule (RelativeRoot.subgroup i α)) ≤ 1 := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  have hαζ := latticePairing_kernelCocharacter hT hα.1 (hT.finite_relativeRoots i)
  have hζ := fun γ (hγ : γ ∈ roots i) =>
    not_linearIndependent_of_latticePairing_kernelCocharacter hT hα.1
      (hT.finite_relativeRoots i) hγ
  generalize kernelCocharacter hT hα.1 (hT.finite_relativeRoots i) = ζ at hαζ hζ
  have hj := Dynamic.Affine.isRepresentedBy_centralizerHom (CommGroupScheme.groupHom ζ ≫ i)
  have hjc := Dynamic.Affine.isClosedSubgroup_centralizerHom (CommGroupScheme.groupHom ζ ≫ i)
  have hL := hcent k G hG _ _ _ hjc hj
  have : IsAffineHom (Dynamic.Affine.centralizerScheme
    (CommGroupScheme.groupHom ζ ≫ i)).X.hom := hL.isAffineHom
  have := hL.smooth
  have hiL : IsMaximalTorus (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj) :=
    IsMaximalTorus.of_comp hjc (by rwa [Dynamic.torusFactor_comp])
  have hdep : ∀ β ∈ roots (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj),
      ∀ γ ∈ roots (Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hj),
      ¬ LinearIndependent ℤ ![β, γ] := by
    intro β hβ γ hγ
    obtain ⟨hβ', hβζ⟩ := mem_roots_of_mem_roots_torusFactor i ζ hj hβ
    obtain ⟨hγ', hγζ⟩ := mem_roots_of_mem_roots_torusFactor i ζ hj hγ
    exact not_linearIndependent_of_not_linearIndependent hT hα.1 hγ'.1
      (hζ β hβ' hβζ) (hζ γ hγ' hγζ)
  have hdim := hrank _ hL _ hiL hdep α (mem_roots_torusFactor i ζ hj hα hαζ)
  rw [← (rootTangentTorusFactorEquiv i ζ hj hT hα.1 hαζ).finrank_eq]
  exact hdim

end Langlands.GroupScheme
