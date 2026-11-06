import Langlands.GroupScheme.Reductive.SplitIsomorphismReduction
import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleGeneration
import Langlands.GroupScheme.Rational.RootFactorPairTransport
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Root data of the centralizers of cocharacters

The roots of a root pairing annihilated by a fixed coweight, with their coroots and the
restricted reflection permutations, form a root pairing. For a root datum `P` of a split maximal
torus `i : T ⟶ G` and a cocharacter `ν` of `T`, this restriction is a root datum of `T` in a
closed representative of the centralizer of `ν`. Hence the Isomorphism Theorem for a common split
maximal torus follows from the rank-one case and the gluing step alone. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.LinearAlgebra

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- The indices of the roots of `P` annihilated by `y`. -/
def orthogonalIndices (P : RootPairing ι R M N) (y : N) : Set ι :=
  {j | P.toLinearMap (P.root j) y = 0}

/-- A reflection in a root annihilated by `y` preserves the roots annihilated by `y`. -/
theorem reflectionPerm_mem_orthogonalIndices_iff (P : RootPairing ι R M N) (y : N) {i : ι}
    (hi : i ∈ orthogonalIndices P y) (j : ι) :
    P.reflectionPerm i j ∈ orthogonalIndices P y ↔ j ∈ orthogonalIndices P y := by
  simp only [orthogonalIndices, Set.mem_ofPred_eq] at hi ⊢
  rw [← P.reflectionPerm_root i j, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, hi, smul_zero, sub_zero]

/-- The root pairing formed by the roots of `P` annihilated by `y`, their coroots, and the
restrictions of their reflection permutations. -/
def orthogonalRootPairing (P : RootPairing ι R M N) (y : N) :
    RootPairing (orthogonalIndices P y) R M N where
  toLinearMap := P.toLinearMap
  root := (Function.Embedding.subtype _).trans P.root
  coroot := (Function.Embedding.subtype _).trans P.coroot
  root_coroot_two j := P.root_coroot_two j
  reflectionPerm i := (P.reflectionPerm i).subtypeEquiv fun j =>
    (reflectionPerm_mem_orthogonalIndices_iff P y i.2 j).symm
  reflectionPerm_root i j := P.reflectionPerm_root i j
  reflectionPerm_coroot i j := P.reflectionPerm_coroot i j

@[simp] theorem orthogonalRootPairing_toLinearMap (P : RootPairing ι R M N) (y : N) :
    (orthogonalRootPairing P y).toLinearMap = P.toLinearMap := rfl

@[simp] theorem orthogonalRootPairing_root (P : RootPairing ι R M N) (y : N)
    (j : orthogonalIndices P y) : (orthogonalRootPairing P y).root j = P.root j := rfl

@[simp] theorem orthogonalRootPairing_coroot (P : RootPairing ι R M N) (y : N)
    (j : orthogonalIndices P y) : (orthogonalRootPairing P y).coroot j = P.coroot j := rfl

@[simp] theorem orthogonalRootPairing_reflection (P : RootPairing ι R M N) (y : N)
    (j : orthogonalIndices P y) :
    (orthogonalRootPairing P y).reflection j = P.reflection j := rfl

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

open Langlands.LinearAlgebra

section CentralizerRootDatum

variable {k : Type u} [Field k] {G Z : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom Z.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G} {J : Type v}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}

/-- **Root datum of the centralizer of a cocharacter.** Let `z : Z ⟶ G` represent the
centralizer of `ν ≫ i`, with `t ≫ z = i`, and suppose that the roots of `t` are the roots of `i`
orthogonal to `ν`. Then the restriction of a root datum `P` of `i` to the roots orthogonal to `ν`
is a root datum of `t`: each of its reflections is realized in `G` by a point which centralizes
`ν`, hence lies in `Z`. -/
theorem IsRootDatumOf.orthogonalRootPairing (hP : IsRootDatumOf i P)
    (ν : cocharacterLattice T) (z : Z ⟶ G)
    (hrep : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy z)
    (t : T.toGrp ⟶ Z) (ht : t ≫ z = i)
    (hroots : roots t = {α | α ∈ roots i ∧ latticePairing T α ν = 0}) :
    IsRootDatumOf t (orthogonalRootPairing P ν) := by
  refine ⟨hP.1, ?_, ?_⟩
  · rw [hroots]
    ext α
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨hP.2.1 ▸ ⟨j.1, rfl⟩, ?_⟩
      have hj := j.2
      simp only [orthogonalIndices, Set.mem_ofPred_eq, hP.1] at hj
      exact hj
    · rintro ⟨hα, hαν⟩
      rw [← hP.2.1] at hα
      obtain ⟨j, rfl⟩ := hα
      refine ⟨⟨j, ?_⟩, rfl⟩
      simp only [orthogonalIndices, Set.mem_ofPred_eq, hP.1]
      exact hαν
  · rintro ⟨j, hj⟩
    obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 j
    have hjν : latticePairing T (P.root j) ν = 0 := by
      simp only [orthogonalIndices, Set.mem_ofPred_eq, hP.1] at hj
      exact hj
    have hfix := LeviGluing.cocharacter_comp_eq_of_reflection hP hσ hjν
    have hmem := LeviGluing.constantPoint_mem_centralizer hn hfix
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    rw [constantPoint_self, ← hrep.2] at hmem
    obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.1 hmem
    have : Mono z.hom.hom := hrep.1
    refine ⟨m, σ, ?_, hσ⟩
    apply IsNormalizingPoint.of_comp z
    rw [ht, hm]
    exact hn

end CentralizerRootDatum

/-- **Isomorphism Theorem from semisimple rank at most one, without root-datum existence.**
The Isomorphism Theorem for two connected reductive groups sharing a split maximal torus follows
from the Isomorphism Theorem in semisimple rank at most one and the gluing step. The centralizers
of cocharacters are connected reductive by `dynamicCentralizerReductive`, their roots are given by
`dynamicCentralizerRoots`, and their root data are the restrictions of the given root data to the
roots orthogonal to the cocharacter. -/
theorem splitCommonTorusIsomorphism_of_rankOne_of_leviGluing
    (hA : SplitRankOneCommonTorusIsomorphismStatement.{u})
    (hC : SplitCommonTorusLeviGluingStatement.{u}) :
    SplitCommonTorusIsomorphismStatement.{u} := by
  have hB := dynamicCentralizerRoots.{u}
  have hCent := dynamicCentralizerReductive.{u}
  intro k _ G₁ G₂ hG₁ hG₂ T hT i₁ i₂ hi₁ hi₂ J₁ J₂ P₁ P₂ hP₁ hP₂ e hroot hcoroot
  refine hC k G₁ G₂ hG₁ hG₂ T hT i₁ i₂ hi₁ hi₂ J₁ J₂ P₁ P₂ hP₁ hP₂ e hroot hcoroot ?_
  intro ν hrank Z₁ Z₂ z₁ z₂ hz₁ hz₂ hrep₁ hrep₂ t₁ t₂ ht₁ ht₂
  -- The centralizers are connected reductive, with maximal tori `t₁` and `t₂`.
  have hZ₁ := hCent k G₁ hG₁ _ Z₁ z₁ hz₁ hrep₁
  have hZ₂ := hCent k G₂ hG₂ _ Z₂ z₂ hz₂ hrep₂
  have hti₁ : IsMaximalTorus t₁ := IsMaximalTorus.of_comp hz₁ (ht₁ ▸ hi₁)
  have hti₂ : IsMaximalTorus t₂ := IsMaximalTorus.of_comp hz₂ (ht₂ ▸ hi₂)
  have := hG₁.isAffineHom
  have := hG₂.isAffineHom
  have := hZ₁.isAffineHom
  have := hZ₂.isAffineHom
  -- Their roots, and their root data restricted from `P₁` and `P₂`.
  have hB₁ := hB k G₁ hG₁ T hT i₁ hi₁ ν Z₁ z₁ hz₁ hrep₁ hZ₁ t₁ ht₁
  have hB₂ := hB k G₂ hG₂ T hT i₂ hi₂ ν Z₂ z₂ hz₂ hrep₂ hZ₂ t₂ ht₂
  have hQ₁ := hP₁.orthogonalRootPairing ν z₁ hrep₁ t₁ ht₁ hB₁
  have hQ₂ := hP₂.orthogonalRootPairing ν z₂ hrep₂ t₂ ht₂ hB₂
  -- The reindexing `e` restricts to the roots orthogonal to `ν`.
  have hmem (j : J₁) :
      j ∈ orthogonalIndices P₁ ν ↔ e j ∈ orthogonalIndices P₂ ν := by
    simp only [orthogonalIndices, Set.mem_ofPred_eq, hP₁.1, hP₂.1]
    rw [← congrFun hroot j]
    rfl
  let e' : orthogonalIndices P₁ ν ≃ orthogonalIndices P₂ ν := e.subtypeEquiv hmem
  -- The rank-one case applies to the centralizers.
  have hrank' : ∀ α ∈ roots t₁, ∀ β ∈ roots t₁, ¬ LinearIndependent ℤ ![α, β] := by
    intro α hα β hβ
    rw [hB₁] at hα hβ
    exact hrank α hα.1 β hβ.1 hα.2 hβ.2
  exact hA k Z₁ Z₂ hZ₁ hZ₂ T hT t₁ t₂ hti₁ hti₂ _ _ (orthogonalRootPairing P₁ ν)
    (orthogonalRootPairing P₂ ν) hQ₁ hQ₂ e' (funext fun j => congrFun hroot j.1)
    (funext fun j => congrFun hcoroot j.1) hrank'

end Langlands.GroupScheme
