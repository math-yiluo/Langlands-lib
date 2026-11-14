import Langlands.GroupScheme.Rational.KernelSubgroupMultiplication
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Torus.SplitPartCharacterTrace
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Torus.CharacterFinite
import Langlands.GroupScheme.Rational.LeviCocenterRootModelStatement
import Langlands.GroupScheme.Rational.SplitTorusCharacterRestriction
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.GroupScheme.Rational.TorusAnisotropicPartLattice

/-! # The largest split part maps isogenously onto the invariant quotient -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace Langlands.GroupScheme
namespace TorusAnisotropicPart

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The pullback identifies quotient characters with the full invariant lattice. -/
def IsInvariantQuotient (q : T ⟶ Q) : Prop :=
  Function.Injective (characterLattice.baseChangePullback k E q) ∧
    (characterLattice.baseChangePullback k E q).range =
      (characterLattice.galoisRepresentation k E T).invariants

private theorem torsionFree_characterLattice
    {F : Type u} [Field F] {P : CommGroupScheme (Spec (CommRingCat.of F))}
    (hP : IsSplitTorus P.toGrp) : Module.IsTorsionFree ℤ (characterLattice P) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hP
  let c := (characterLattice.congr (CommGroupScheme.isoOfGroupIso e)).trans
    (splitTorus.characterLatticeEquiv F I)
  exact c.injective.moduleIsTorsionFree c.toIntLinearEquiv
    (fun n x => c.toIntLinearEquiv.map_smul n x)

variable [FiniteDimensional k E] [IsGalois k E] [Fintype (E ≃ₐ[k] E)]
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A ⟶ T} {q : T ⟶ Q}

local notation "B" => CommGroupScheme.baseChange (algebraBaseMap k E)
local notation "n" => (Fintype.card (E ≃ₐ[k] E) : ℤ)

/-- A character of the invariant quotient vanishing on the largest split part is zero. -/
theorem invariantQuotient_splitPart_character_injective
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hT : IsTorus T.toGrp) (hTE : IsSplitTorus ((B).obj T).toGrp)
    (ha : IsLargestSplitSubtorus (CommGroupScheme.groupHom a))
    (hQ : IsSplitTorus Q.toGrp) (hq : IsInvariantQuotient k E q) :
    Function.Injective (characterLattice.comapHom (CommGroupScheme.groupHom (a ≫ q))) := by
  classical
  have := torsionFree_characterLattice hTE
  rw [injective_iff_map_eq_zero]
  intro β hβ
  let βE := characterLattice.baseChange (algebraBaseMap k E) Q β
  let χ := characterLattice.baseChangePullback k E q βE
  have hχ : (B).map a ≫ χ = 0 := by
    have hb := congrArg (characterLattice.baseChange (algebraBaseMap k E) A) hβ
    change characterLattice.baseChange (algebraBaseMap k E) A ((a ≫ q) ≫ β) = _ at hb
    change (B).map a ≫ ((B).map q ≫ βE) = 0
    simpa only [characterLattice.baseChange_precomp, Functor.map_comp,
      Category.assoc, map_zero, βE] using hb
  have htrace := ha.galoisOrbitSum_character_eq_zero E hT χ hχ
  have hfixed (σ : E ≃ₐ[k] E) :
      characterLattice.galoisRepresentation k E T σ χ = χ := by
    change characterLattice.galoisRepresentation k E T σ
      ((B).map q ≫ βE) = (B).map q ≫ βE
    rw [characterLattice.galoisRepresentation_precompose,
      characterLattice.galoisRepresentation_baseChange]
  have hnx : n • χ = 0 := by
    simpa only [CharacterAveraging.galoisOrbitSum, CocharacterAveraging.orbitSum,
      hfixed, Finset.sum_const, Finset.card_univ, natCast_zsmul] using htrace
  have hn : n ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hz : χ = 0 := (smul_right_injective (characterLattice ((B).obj T)) hn)
    (hnx.trans (smul_zero n).symm)
  have hβE : βE = 0 := hq.1 (hz.trans (map_zero _).symm)
  apply (hQ.characterLattice_baseChange_bijective (algebraBaseMap k E) Q).injective
  exact hβE.trans (map_zero _).symm

omit [FiniteDimensional k E] [IsGalois k E] in
/-- The order of the Galois group kills the cokernel of restriction to the split part. -/
theorem invariantQuotient_splitPart_character_multiple
    (hTE : IsSplitTorus ((B).obj T).toGrp)
    (ha : IsLargestSplitSubtorus (CommGroupScheme.groupHom a))
    (hQ : IsSplitTorus Q.toGrp) (hq : IsInvariantQuotient k E q)
    (α : characterLattice A) :
    ∃ β : characterLattice Q,
      characterLattice.comapHom (CommGroupScheme.groupHom (a ≫ q)) β = n • α := by
  classical
  have hA := ha.1.1
  have : IsClosedImmersion (CommGroupScheme.groupHom a).hom.hom.left := ha.1.2
  have : IsClosedImmersion (CommGroupScheme.groupHom ((B).map a)).hom.hom.left :=
    IsClosedSubgroup.baseChange (algebraBaseMap k E) ha.1.2
  let αE := characterLattice.baseChange (algebraBaseMap k E) A α
  obtain ⟨χ, hχ⟩ := (hA.baseChange (algebraBaseMap k E)).characterRestrict_surjective_of_mono
    hTE (CommGroupScheme.groupHom ((B).map a)) αE
  change (B).map a ≫ χ = αE at hχ
  have hsum : (∑ σ : E ≃ₐ[k] E,
      characterLattice.galoisRepresentation k E T σ χ) ∈
      (characterLattice.baseChangePullback k E q).range := by
    rw [hq.2]
    exact sum_mem_invariants _ χ
  obtain ⟨βE, hβE⟩ := hsum
  obtain ⟨β, hβ⟩ := (hQ.characterLattice_baseChange_bijective
    (algebraBaseMap k E) Q).surjective βE
  refine ⟨β, ?_⟩
  apply (hA.characterLattice_baseChange_bijective (algebraBaseMap k E) A).injective
  change characterLattice.baseChange (algebraBaseMap k E) A
    ((a ≫ q) ≫ β) = characterLattice.baseChange (algebraBaseMap k E) A (n • α)
  rw [characterLattice.baseChange_precomp, Functor.map_comp, Category.assoc, hβ]
  change (B).map a ≫ characterLattice.baseChangePullback k E q βE = _
  rw [hβE]
  change characterLattice.precompose ((B).map a)
    (∑ σ : E ≃ₐ[k] E, characterLattice.galoisRepresentation k E T σ χ) = _
  rw [map_sum]
  have hrestrict (σ : E ≃ₐ[k] E) : characterLattice.precompose ((B).map a)
      (characterLattice.galoisRepresentation k E T σ χ) = αE := by
    change (B).map a ≫ characterLattice.galoisRepresentation k E T σ χ = αE
    rw [← characterLattice.galoisRepresentation_precompose]
    rw [hχ, characterLattice.galoisRepresentation_baseChange]
  simp only [hrestrict, Finset.sum_const, Finset.card_univ, natCast_zsmul, αE, map_nsmul]

/-- The largest split subtorus maps finitely and surjectively onto an invariant quotient. -/
theorem invariantQuotient_splitPart_finite_surjective
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hT : IsTorus T.toGrp) (hTE : IsSplitTorus ((B).obj T).toGrp)
    (ha : IsLargestSplitSubtorus (CommGroupScheme.groupHom a))
    (hQ : IsSplitTorus Q.toGrp) (hq : IsInvariantQuotient k E q) :
    IsFinite (CommGroupScheme.groupHom (a ≫ q)).hom.hom.left ∧
      Surjective (CommGroupScheme.groupHom (a ≫ q)).hom.hom.left := by
  have hA := ha.1.1
  have hi := invariantQuotient_splitPart_character_injective k E hT hTE ha hQ hq
  have := hA.finite_characterLattice
  have hfin : Finite (characterLattice.pullbackCokernel
      (CommGroupScheme.groupHom (a ≫ q))) := by
    let f := (characterLattice.comapHom (CommGroupScheme.groupHom (a ≫ q))).toIntLinearMap
    change Finite (characterLattice A ⧸ f.range)
    apply Module.finite_of_fg_torsion
    intro x
    have hn : n ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    refine ⟨⟨n, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩, ?_⟩
    obtain ⟨α, rfl⟩ := f.range.mkQ_surjective x
    change f.range.mkQ (n • α) = 0
    apply (Submodule.Quotient.mk_eq_zero f.range).mpr
    exact invariantQuotient_splitPart_character_multiple k E hTE ha hQ hq α
  exact ⟨hA.isFinite_of_injective_characterPullback hQ _ hi,
    (hA.flat_and_surjective_of_injective_characterPullback hQ _ hi).2⟩

/-- Multiplication of the split part and the full invariant-quotient kernel is finite
and surjective on the actual schemes. -/
theorem invariantQuotient_splitPart_kernelMultiplication
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hT : IsTorus T.toGrp) (hTE : IsSplitTorus ((B).obj T).toGrp)
    (ha : IsLargestSplitSubtorus (CommGroupScheme.groupHom a))
    (hQ : IsSplitTorus Q.toGrp) (hq : IsInvariantQuotient k E q) :
    Surjective (subgroupMultiplication (CommGroupScheme.groupHom a)
      (kernelι (CommGroupScheme.groupHom q))).left ∧
      IsFinite (subgroupMultiplication (CommGroupScheme.groupHom a)
        (kernelι (CommGroupScheme.groupHom q))).left := by
  obtain ⟨hf, hs⟩ := invariantQuotient_splitPart_finite_surjective k E hT hTE ha hQ hq
  have : IsFinite ((CommGroupScheme.groupHom a) ≫
      (CommGroupScheme.groupHom q)).hom.hom.left := by
    change IsFinite (CommGroupScheme.groupHom (a ≫ q)).hom.hom.left
    exact hf
  have : Surjective ((CommGroupScheme.groupHom a) ≫
      (CommGroupScheme.groupHom q)).hom.hom.left := by
    change Surjective (CommGroupScheme.groupHom (a ≫ q)).hom.hom.left
    exact hs
  exact (KernelSubgroupMultiplication.finite_surjective
    (CommGroupScheme.groupHom a) (CommGroupScheme.groupHom q)).symm

end TorusAnisotropicPart
end Langlands.GroupScheme
