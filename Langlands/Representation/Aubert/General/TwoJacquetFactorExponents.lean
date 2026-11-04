import Langlands.Representation.Aubert.General.TwoJacquetSupportDeduction
import Langlands.Representation.Aubert.General.RationalSquareIntegrabilityStatement

/-! # Full-center exponents of the two actual induction factors -/

noncomputable section

namespace Langlands

universe uG uV

variable {H : Type uG} [Group H] [TopologicalSpace H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A zero representation has no full-center exponents. -/
theorem not_isCentralExponent_of_subsingleton
    (ρ : Representation ℂ H V) (hzero : Subsingleton V)
    (χ : Subgroup.center H →* ℂˣ) :
    ¬ IsCentralExponent ρ χ := by
  intro hχ
  apply hχ.2
  apply le_antisymm _ bot_le
  intro v _
  change v = 0
  exact hzero.elim v 0

namespace Aubert.General

open CategoryTheory SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U Q L O : Subgroup G}
  {h : IsSemidirectDecomposition P M U} {hU : IsClosed (U : Set G)}
  {hO : IsSemidirectDecomposition Q L O} {hOc : IsClosed (O : Set G)}
  {σ : SmoothRep.{0, uG, uV} ℂ M}

/-- Scalar full-center characters for the two surviving Jacquet modules.
The first acts on the inducing representation, and the second on the other
Jacquet module of its actual normalized induction. -/
structure InductionTwoJacquetScalarCharacters
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hO : IsSemidirectDecomposition Q L O) (hOc : IsClosed (O : Set G))
    (σ : SmoothRep.{0, uG, uV} ℂ M) where
  first : Subgroup.center M →* ℂˣ
  first_scalar : ∀ (z : Subgroup.center M) (v : σ),
    σ.representation (z : M) v = (first z : ℂ) • v
  second : Subgroup.center L →* ℂˣ
  second_scalar : ∀ (z : Subgroup.center L)
    (v : (jacquetFunctor.{uG, max uG uV} hO hOc).obj
      ((normalizedInductionFunctor h hU).obj σ)),
    ((jacquetFunctor.{uG, max uG uV} hO hOc).obj
      ((normalizedInductionFunctor h hU).obj σ)).representation (z : L) v =
        (second z : ℂ) • v

/-- The first surviving Jacquet module of the literal subspace has precisely
the inducing scalar character as its only possible full-center exponent. -/
theorem InductionTwoJacquetFactors.subspace_centralExponent_eq
    (F : InductionTwoJacquetFactors h hU hO hOc σ)
    (χ₀ : Subgroup.center M →* ℂˣ)
    (hscalar : ∀ (z : Subgroup.center M) (v : σ),
      σ.representation (z : M) v = (χ₀ z : ℂ) • v)
    (χ : Subgroup.center M →* ℂˣ)
    (hχ : IsCentralExponent
      ((jacquetFunctor.{uG, max uG uV} h hU).obj
        (subrepresentation ((normalizedInductionFunctor h hU).obj σ)
          F.subspace)).representation χ) :
    χ = χ₀ :=
  centralExponent_eq_of_scalar_injective
    F.inducing_equiv.toIntertwiningMap F.inducing_equiv.injective χ₀ hscalar χ hχ

/-- The second surviving Jacquet module of the literal quotient has the
same scalar full-center exponent as that of the whole induction. -/
theorem InductionTwoJacquetFactors.quotient_centralExponent_eq
    (F : InductionTwoJacquetFactors h hU hO hOc σ)
    (χ₀ : Subgroup.center L →* ℂˣ)
    (hscalar : ∀ (z : Subgroup.center L)
      (v : (jacquetFunctor.{uG, max uG uV} hO hOc).obj
        ((normalizedInductionFunctor h hU).obj σ)),
      ((jacquetFunctor.{uG, max uG uV} hO hOc).obj
        ((normalizedInductionFunctor h hU).obj σ)).representation (z : L) v =
          (χ₀ z : ℂ) • v)
    (χ : Subgroup.center L →* ℂˣ)
    (hχ : IsCentralExponent
      ((jacquetFunctor.{uG, max uG uV} hO hOc).obj
        (quotient ((normalizedInductionFunctor h hU).obj σ)
          F.subspace)).representation χ) :
    χ = χ₀ :=
  centralExponent_eq_of_scalar_injective
    F.second_quotient_equiv.symm.toIntertwiningMap
    F.second_quotient_equiv.symm.injective χ₀ hscalar χ hχ

end Aubert.General
end Langlands

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

universe u v

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance twoJacquetFactorExponentsPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  [Fintype (SimpleRoot i ν)]
  {h : ∀ K : Finset (SimpleRoot i ν),
    IsSemidirectDecomposition (parabolic i ν K) (levi i ν K) (unipotent i ν K)}
  {hU : ∀ K : Finset (SimpleRoot i ν),
    IsClosed (unipotent i ν K : Set (RationalPoint k G.X))}
  {I J : Finset (SimpleRoot i ν)}
  {σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)}
  (F : InductionTwoJacquetFactors (h I) (hU I) (h J) (hU J) σ)
  (hUc : ∀ K, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν K))
  (hzero : ∀ K : Finset (SimpleRoot i ν),
    K ≠ I → K ≠ J → K ≠ Finset.univ →
      Subsingleton ((jacquetFunctor (h K) (hU K)).obj
        ((normalizedInductionFunctor (h I) (hU I)).obj σ)))
  (hfull : ∀ (t : RationalPoint k T.X)
    (z : Subgroup.center (levi i ν Finset.univ)),
    ((z : levi i ν Finset.univ) : RationalPoint k G.X) = t ≫ i.hom.hom →
      ¬ IsNoncentralNegativeTorusPoint i ν t)

include hUc hzero hfull in
/-- For the actual subspace factor, all strict exponent tests reduce to the
inducing scalar character at the first index. Proper outside-index Jacquet
vanishing and exclusion of noncentral full-index tests remain explicit. -/
theorem InductionTwoJacquetFactors.subspace_hasStrictNormalizedJacquetExponents
    (C : InductionTwoJacquetScalarCharacters (h I) (hU I) (h J) (hU J) σ)
    (hbound : ∀ (t : RationalPoint k T.X)
      (z : Subgroup.center (levi i ν I)),
      ((z : levi i ν I) : RationalPoint k G.X) = t ≫ i.hom.hom →
      IsNoncentralNegativeTorusPoint i ν t → ‖(C.first z : ℂ)‖ < 1) :
    HasStrictNormalizedJacquetExponents i ν h hU
      (subrepresentation ((normalizedInductionFunctor (h I) (hU I)).obj σ)
        F.subspace) := by
  intro K χ hχ t z hz ht
  by_cases hKI : K = I
  · subst K
    rw [F.subspace_centralExponent_eq C.first C.first_scalar χ hχ]
    exact hbound t z hz ht
  by_cases hKJ : K = J
  · subst K
    exact False.elim (not_isCentralExponent_of_subsingleton _
      F.second_subspace_zero χ hχ)
  by_cases hKfull : K = Finset.univ
  · subst K
    exact False.elim (hfull t z hz ht)
  have hzK := (Langlands.Aubert.General.InductionTwoJacquetFactors.other_jacquet_subsingleton.{u, u, max (u + 1) v}
    F K (hUc K)
    (hzero K hKI hKJ hKfull)).1
  exact False.elim (not_isCentralExponent_of_subsingleton _ hzK χ hχ)

include hUc hzero hfull in
/-- For the actual quotient factor, the strict tests reduce instead to the
scalar character of the second Jacquet module of the whole induction. -/
theorem InductionTwoJacquetFactors.quotient_hasStrictNormalizedJacquetExponents
    (C : InductionTwoJacquetScalarCharacters (h I) (hU I) (h J) (hU J) σ)
    (hbound : ∀ (t : RationalPoint k T.X)
      (z : Subgroup.center (levi i ν J)),
      ((z : levi i ν J) : RationalPoint k G.X) = t ≫ i.hom.hom →
      IsNoncentralNegativeTorusPoint i ν t → ‖(C.second z : ℂ)‖ < 1) :
    HasStrictNormalizedJacquetExponents i ν h hU
      (quotient ((normalizedInductionFunctor (h I) (hU I)).obj σ)
        F.subspace) := by
  intro K χ hχ t z hz ht
  by_cases hKJ : K = J
  · subst K
    rw [F.quotient_centralExponent_eq C.second C.second_scalar χ hχ]
    exact hbound t z hz ht
  by_cases hKI : K = I
  · subst K
    exact False.elim (not_isCentralExponent_of_subsingleton _
      F.first_quotient_zero χ hχ)
  by_cases hKfull : K = Finset.univ
  · subst K
    exact False.elim (hfull t z hz ht)
  have hzK := (Langlands.Aubert.General.InductionTwoJacquetFactors.other_jacquet_subsingleton.{u, u, max (u + 1) v}
    F K (hUc K)
    (hzero K hKI hKJ hKfull)).2
  exact False.elim (not_isCentralExponent_of_subsingleton _ hzK χ hχ)

end Langlands.Aubert.General.RationalPointFamily
