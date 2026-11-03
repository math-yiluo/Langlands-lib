import Langlands.Representation.Aubert.General.SubrepresentationInducingExponents
import Langlands.Representation.Aubert.General.TwoJacquetLengthBound

/-! # Actual factors and asymmetric Jacquet modules of reducible induction -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General

universe uG uV

open CategoryTheory SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U Q L V : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U)
  (hO : IsSemidirectDecomposition Q L V) (hV : IsClosed (V : Set G))
  (hVc : Jacquet.Localization.IsLimitOfCompactSubgroups V)
  (σ : SmoothRep.{0, uG, uV} ℂ M)

/-- The actual two factors, together with the full asymmetric pattern for the
two normalized Jacquet functors. The second Levi need not equal the first. -/
structure InductionTwoJacquetFactors where
  subspace : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation
  ne_bot : subspace ≠ ⊥
  ne_top : subspace ≠ ⊤
  subspace_irreducible :
    (subrepresentation ((normalizedInductionFunctor h hU).obj σ) subspace).IsIrreducible
  quotient_irreducible :
    (quotient ((normalizedInductionFunctor h hU).obj σ) subspace).IsIrreducible
  inducing_equiv :
    ((jacquetFunctor.{uG, max uG uV} h hU).obj
      (subrepresentation ((normalizedInductionFunctor h hU).obj σ) subspace)).representation.Equiv
      σ.representation
  first_quotient_zero :
    Subsingleton ((jacquetFunctor.{uG, max uG uV} h hU).obj
      (quotient ((normalizedInductionFunctor h hU).obj σ) subspace))
  second_subspace_zero :
    Subsingleton ((jacquetFunctor.{uG, max uG uV} hO hV).obj
      (subrepresentation ((normalizedInductionFunctor h hU).obj σ) subspace))
  second_quotient_equiv :
    ((jacquetFunctor.{uG, max uG uV} hO hV).obj
      ((normalizedInductionFunctor h hU).obj σ)).representation.Equiv
      ((jacquetFunctor.{uG, max uG uV} hO hV).obj
        (quotient ((normalizedInductionFunctor h hU).obj σ) subspace)).representation

variable
  (hJac : ((jacquetFunctor.{uG, max uG uV} h hU).obj
    ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
  (hJacO : ((jacquetFunctor.{uG, max uG uV} hO hV).obj
    ((normalizedInductionFunctor h hU).obj σ)).IsIrreducible)
  (hdetect : ∀ D : SmoothRep.{0, uG, max uG uV} ℂ G,
    D.IsIrreducible →
    IsSubquotient D ((normalizedInductionFunctor h hU).obj σ) →
    Nontrivial ((jacquetFunctor.{uG, max uG uV} h hU).obj D) ∨
      Nontrivial ((jacquetFunctor.{uG, max uG uV} hO hV).obj D))

include hUc hVc hJac hJacO hdetect

/-- Irreducible-subquotient detection supplies the quotient detector needed
for the second Jacquet module to vanish on a proper nonzero subspace. -/
theorem two_jacquet_second_subrepresentation_subsingleton
    (S : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation)
    (hS0 : S ≠ ⊥) (hS1 : S ≠ ⊤) :
    Subsingleton ((jacquetFunctor.{uG, max uG uV} hO hV).obj
      (subrepresentation ((normalizedInductionFunctor h hU).obj σ) S)) := by
  let A := (normalizedInductionFunctor h hU).obj σ
  have hq := (two_jacquet_proper_subrepresentation_irreducible
    h hU hUc hO hV hVc A hJac hJacO hdetect S hS0 hS1).2
  apply proper_subrepresentation_second_jacquet_subsingleton
    h hU hUc σ hO hV hVc hJac hJacO S hS0 hS1
  intro hr hrO
  have hQA : IsSubquotient (quotient A S) A :=
    IsQuotient.isSubquotient ⟨mkQ A S, mkQ_surjective A S⟩
  rcases hdetect (quotient A S) hq hQA with hn | hn
  · exact False.elim (not_subsingleton_iff_nontrivial.mpr hn hr)
  · exact False.elim (not_subsingleton_iff_nontrivial.mpr hn hrO)

/-- The second Jacquet module of the actual induction maps isomorphically
onto that of its quotient by any proper nonzero invariant subspace. -/
def quotientSecondJacquetEquiv
    (S : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation)
    (hS0 : S ≠ ⊥) (hS1 : S ≠ ⊤) :
    ((jacquetFunctor.{uG, max uG uV} hO hV).obj
      ((normalizedInductionFunctor h hU).obj σ)).representation.Equiv
      ((jacquetFunctor.{uG, max uG uV} hO hV).obj
        (quotient ((normalizedInductionFunctor h hU).obj σ) S)).representation := by
  let A := (normalizedInductionFunctor h hU).obj σ
  let rO := jacquetFunctor.{uG, max uG uV} hO hV
  have hz := two_jacquet_second_subrepresentation_subsingleton
    h hU hUc hO hV hVc σ hJac hJacO hdetect S hS0 hS1
  have hex := jacquetFunctor_map_isShortExact hO hV hVc
    (subtype A S) (mkQ A S) (subtype_mkQ_isShortExact A S)
  let p := hom (rO.map (mkQ A S))
  refine p.ofBijective ⟨?_, hex.2.1⟩
  intro x y hxy
  apply sub_eq_zero.mp
  have hker : x - y ∈ LinearMap.ker p.toLinearMap := by
    change p (x - y) = 0
    rw [map_sub, hxy, sub_self]
  rw [← hex.2.2] at hker
  obtain ⟨v, hv⟩ := hker
  rw [hz.elim v 0, map_zero] at hv
  exact hv.symm

@[simp]
theorem quotientSecondJacquetEquiv_apply
    (S : Subrepresentation ((normalizedInductionFunctor h hU).obj σ).representation)
    (hS0 : S ≠ ⊥) (hS1 : S ≠ ⊤)
    (v : (jacquetFunctor.{uG, max uG uV} hO hV).obj
      ((normalizedInductionFunctor h hU).obj σ)) :
    quotientSecondJacquetEquiv h hU hUc hO hV hVc σ hJac hJacO hdetect S hS0 hS1 v =
      hom ((jacquetFunctor.{uG, max uG uV} hO hV).map
        (mkQ ((normalizedInductionFunctor h hU).obj σ) S)) v := rfl

/-- Choose the two actual irreducible factors of a reducible induction with
two simple detecting Jacquet images. No finite-length premise is supplied. -/
def inductionTwoJacquetFactors
    (hσ : σ.IsIrreducible)
    (hred : ¬ ((normalizedInductionFunctor h hU).obj σ).IsIrreducible) :
    InductionTwoJacquetFactors h hU hO hV σ := by
  let A := (normalizedInductionFunctor h hU).obj σ
  have hnonzero : Nontrivial ((jacquetFunctor.{uG, max uG uV} h hU).obj A) :=
    repLength_pos_iff.mp (by
      rw [repLength_eq_one_iff.mpr hJac]
      exact zero_lt_one)
  let : Nontrivial (Jacquet.Localization.Coinvariants A.representation U 1) := hnonzero
  let : Nontrivial A :=
    (Jacquet.Localization.mk_surjective A.representation U 1).nontrivial
  let S := Classical.choose (exists_proper_subrepresentation_of_not_irreducible A hred)
  have hS := Classical.choose_spec
    (exists_proper_subrepresentation_of_not_irreducible A hred)
  have hirr := two_jacquet_proper_subrepresentation_irreducible
    h hU hUc hO hV hVc A hJac hJacO hdetect S hS.1 hS.2
  exact
    { subspace := S
      ne_bot := hS.1
      ne_top := hS.2
      subspace_irreducible := hirr.1
      quotient_irreducible := hirr.2
      inducing_equiv :=
        subrepresentationJacquetInducingEquiv h hU hUc σ hJac hσ S hS.1
      first_quotient_zero :=
        quotient_jacquet_subsingleton_of_irreducible_induction_jacquet
          h hU hUc σ hJac S hS.1
      second_subspace_zero :=
        two_jacquet_second_subrepresentation_subsingleton
          h hU hUc hO hV hVc σ hJac hJacO hdetect S hS.1 hS.2
      second_quotient_equiv :=
        quotientSecondJacquetEquiv h hU hUc hO hV hVc σ
          hJac hJacO hdetect S hS.1 hS.2 }

end Langlands.Aubert.General
