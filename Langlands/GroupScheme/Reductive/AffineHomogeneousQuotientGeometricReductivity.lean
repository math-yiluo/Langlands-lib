import Langlands.GroupScheme.Reductive.AffineHomogeneousQuotientStatement
import Langlands.GroupScheme.Reductive.AffineUnipotentQuotientCore
import Langlands.GroupScheme.HomogeneousQuotientTower
import Langlands.GroupScheme.HomogeneousQuotientAdditiveCocycle
import Langlands.GroupScheme.HomogeneousQuotientBaseChange
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Reductive.ToPseudoReductive

/-! # Reductivity from an affine homogeneous quotient, conditional on geometric reductivity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, Haboush's theorem implies that a smooth closed subgroup
of a pseudo-reductive group with an affine homogeneous quotient has identity component with
trivial unipotent radical. -/
theorem hasTrivialUnipotentRadical_identityComponent_of_geometricReductivity
    (hHab : ReductiveGeometricReductivityStatement.{u})
    {K : Type u} [Field K] [IsAlgClosed K] {G H : GroupScheme (Spec (CommRingCat.of K))}
    (hG : IsPseudoReductive G) (i : H ⟶ G) (hi : IsClosedSubgroup i)
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i)
    (hQ : IsAffineHom Q.scheme.hom) :
    HasTrivialUnipotentRadical (identityComponent H) := by
  intro N i' hi' hNs hNc hNu hnorm
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth N.X.hom := hNs
  have : IsClosedImmersion i.hom.hom.left := hi
  let j : N ⟶ G := i' ≫ identityComponentι H ≫ i
  have hj : IsClosedSubgroup j := by
    have : IsClosedImmersion (identityComponentι H).hom.hom.left :=
      IdentityComponent.isClosedSubgroup_identityComponentι H
    have : IsClosedImmersion i'.hom.hom.left := hi'
    change IsClosedImmersion (i'.hom.hom.left ≫ (identityComponentι H).hom.hom.left ≫
      i.hom.hom.left)
    infer_instance
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffine N.X.left := isAffine_of_isAffineHom j.hom.hom.left
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  obtain ⟨QN, qN, hsep, hft, hqc, hsm, hsurj, hqqc, hfib⟩ :=
    smoothSubgroupQuotientExistence K G N j hj hNs
  let QN' : HomogeneousQuotientFromEmbedding.HomogeneousQuotient j :=
    ⟨QN, qN, hsep, hft, hqc, hsm, hsurj, hqqc, hfib⟩
  have hQN : IsAffineHom QN'.scheme.hom :=
    HomogeneousQuotientTower.isAffineHom_of_normal_identityComponent i hi Q hQ i' hi' hNs
      hnorm QN'
  by_contra hne
  have hnt : ∃ (T : Over (Spec (CommRingCat.of K))) (n : T ⟶ N.X), n ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hne
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      change y ≫ i'.hom.hom ∈ (⊥ : Subgroup _)
      rw [hall T y, MonObj.one_comp]
      exact Subgroup.one_mem _
    · intro hx
      have hx1 : x = 1 := hx
      exact ⟨1, by rw [hx1]; exact map_one _⟩
  refine AdditiveShift.false_of_shift_functions hHab hG hNu j hnt fun χ hχ hadd => ?_
  obtain ⟨f, hf⟩ :=
    HomogeneousQuotientAdditiveCocycle.exists_leftTranslate_of_isAffineHom QN' hQN χ hχ hadd
  exact ⟨f, fun T n x => hf n x⟩

set_option linter.defProp false in
/-- Haboush's theorem implies the affine-quotient reductivity criterion over every field, by
base change of the subgroup and its actual quotient to an algebraic closure. -/
def affineHomogeneousQuotientReductive_of_geometricReductivity
    (hHab : ReductiveGeometricReductivityStatement.{u}) :
    AffineHomogeneousQuotientReductiveStatement.{u} := by
  intro k _ G hG H i hi hH
  have : Smooth H.X.hom := hH
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom H.X.hom := by
    have hc : IsAffineHom (i.hom.hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using hc
  intro Q hQ
  have hGK : IsPseudoReductive ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G) :=
    hG.baseChange_toAlgebraicClosure.isPseudoReductive
  have : Smooth ((GroupScheme.baseChange (toAlgebraicClosure k)).obj H).X.hom :=
    IdentityComponent.smooth_baseChange H (algebraMap k (AlgebraicClosure k))
  have : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj H).X.hom := by
    have : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom :=
      hGK.isAffineHom
    have : IsClosedImmersion ((GroupScheme.baseChange (toAlgebraicClosure k)).map i).hom.hom.left :=
      hi.baseChange (toAlgebraicClosure k)
    have hc : IsAffineHom (((GroupScheme.baseChange (toAlgebraicClosure k)).map i).hom.hom.left ≫
        ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom) := inferInstance
    simpa only [Over.w] using hc
  have hcore := hasTrivialUnipotentRadical_identityComponent_of_geometricReductivity hHab hGK
    _ (hi.baseChange (toAlgebraicClosure k)) (Q.baseChange (toAlgebraicClosure k))
    (Q.baseChange_isAffineHom _ hQ)
  exact ⟨inferInstance, inferInstance, inferInstance, HasTrivialUnipotentRadical.of_iso
    (IdentityComponent.baseChangeIso H (algebraMap k (AlgebraicClosure k))) hcore⟩

end Langlands.GroupScheme
