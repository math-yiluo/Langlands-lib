import Langlands.Representation.Classification.HeadDetectingCount
import Langlands.Representation.Classification.RelativePositiveTotalHeadProof
import Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessProof
import Langlands.Representation.Parabolic.FlattenedOppositeJacquetComparisonProof
import Langlands.Representation.Parabolic.IrreducibleOppositeJacquetFiniteLengthProof
import Langlands.Representation.Filtration.MultiplicityTransportProof
import Langlands.Representation.Filtration.IrreducibleMultiplicityProof
import Langlands.Representation.Exponents.WeylBranchExcessMultiplicity

/-!
# Opposite Jacquet counts along a flattened shape

Counts in the composed opposite Jacquet module along a refinement are counts in
the opposite Jacquet module along the flattened shape. Every irreducible quotient
of a normalized induction has, along the flattened shape, at least the common
inner and ambient count (second adjointness, as in
`glRelativePositiveTotalHead`). An irreducible subquotient of a finite-length
representation has a positive count.
-/

noncomputable section

namespace Langlands.Classification.A6ii

open CategoryTheory GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW uT uA

section Functor

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The opposite Jacquet functor maps injections to injections. -/
theorem oppositeFunctor_map_injective {n : ℕ} (C : BlockShape n) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} (f : A ⟶ B),
      Function.Injective (SmoothRep.hom f) →
        Function.Injective ((CuspidalJacquetMultiplicity.oppositeFunctor T C).map f).hom := by
  let := T.topology
  intro A B f hf
  have : Mono f := (SmoothRep.mono_iff_injective f).mpr hf
  exact (Rep.mono_iff_injective _).mp inferInstance

/-- The opposite Jacquet functor maps surjections to surjections. -/
theorem oppositeFunctor_map_surjective {n : ℕ} (C : BlockShape n) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} (f : A ⟶ B),
      Function.Surjective (SmoothRep.hom f) →
        Function.Surjective ((CuspidalJacquetMultiplicity.oppositeFunctor T C).map f).hom := by
  let := T.topology
  intro A B f hf
  have : Epi f := (SmoothRep.epi_iff_surjective f).mpr hf
  exact (Rep.epi_iff_surjective _).mp inferInstance

end Functor

section Transport

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Counts in the composed opposite Jacquet module are counts in the opposite
Jacquet module along the flattened shape. -/
theorem count_flattened {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (τ : Rep.{uT} ℂ (refinedLevi F.Carrier B S)) {m : ℕ}
    (h : HasJordanHolderMultiplicity
      (Rep.of (T.normalizedComposedOppositeJacquet B S A.ρ)) τ m) :
    HasJordanHolderMultiplicity
      (CuspidalJacquetMultiplicity.oppositeJacquet T (B.flatten S) A)
      (Rep.of (τ.ρ.comp (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) m := by
  obtain ⟨E, -⟩ := Parabolic.flattenedOppositeJacquetComparison.{uF, uF, uV}.2 p F T n B S A
  have h1 := (groupEquivJordanHolderMultiplicityTransport ℂ (refinedLevi F.Carrier B S)
    ((B.flatten S).Levi F.Carrier) (flattenedLeviEquiv F.Carrier B S) _ τ m).mp h
  exact (equivJordanHolderMultiplicityTransport ℂ _ _ _ _ _ E
    (Representation.Equiv.refl _) m).mp h1

/-- Every irreducible quotient of the normalized induction of an admissible
Levi representation has, along the flattened shape, at least the common inner
and ambient count. -/
theorem quotient_count_ge {n : ℕ} (hn : 0 < n) (B : BlockShape n) (S : BlockRefinement B)
    (τ : Rep.{uT} ℂ (refinedLevi F.Carrier B S)) (μ : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hμi : Representation.IsIrreducible μ.ρ)
    (hμa : letI := T.topology; IsAdmissible μ.ρ) (m : ℕ)
    (hinner : HasJordanHolderMultiplicity (innerJacquet T B S μ) τ m)
    (hambient : HasJordanHolderMultiplicity (ambientJacquet T B S μ) τ m) :
    letI := T.topology
    ∀ (P : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear n F.Carrier)), P.IsIrreducible →
      ∀ q : (CuspidalJacquetMultiplicity.induced T B μ).ρ.IntertwiningMap
          P.representation, Function.Surjective q →
        ∃ c, m ≤ c ∧ HasJordanHolderMultiplicity
          (CuspidalJacquetMultiplicity.oppositeJacquet T (B.flatten S) P.obj)
          (Rep.of (τ.ρ.comp (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) c := by
  let := T.topology
  intro P hP q hq
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  let I := CuspidalJacquetMultiplicity.induced T B μ
  have hIa : IsAdmissible I.ρ :=
    Parabolic.normalizedInductionAdmissibility F T B μ μ.ρ hμa
  have hPa : IsAdmissible P.representation := by
    apply Unramified.SphericalExistence.isAdmissible_of_surjective ?_ q hq hIa
    intro H
    obtain ⟨K, hK, hKH, -⟩ :=
      B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization T
        (H.isOpen.mem_nhds H.one_mem)
    exact ⟨K, hK, hKH⟩
  let := hP
  let := hμi
  let : Nontrivial P := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) P.representation.asModule
  have hq0 : q ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := exists_ne (0 : P)
    obtain ⟨w, hw⟩ := hq v
    apply hv
    simpa [hz] using hw.symm
  obtain ⟨E, -, -⟩ :=
    Parabolic.normalizedSecondAdjointness.{uF, uW, max uF uW}.1 p F T n hn B
  let i := E μ P.obj hμa hPa q
  have hi0 : i ≠ 0 := by
    intro hz
    exact hq0 ((E μ P.obj hμa hPa).injective (hz.trans (map_zero _).symm))
  have hi : Function.Injective i :=
    (Representation.IsIrreducible.injective_or_eq_zero i).resolve_right hi0
  let O := CuspidalJacquetMultiplicity.oppositeJacquet T B P.obj
  have hOa : IsAdmissible O.ρ :=
    Parabolic.isAdmissible_standardOppositeJacquet F T B P P.representation hPa
  have hiq : Function.Injective (T.normalizedRefinedOppositeJacquetMap B S i) :=
    T.normalizedRefinedOppositeJacquetMap_injective B S i hOa.1 hi
  obtain ⟨Etrans, -⟩ :=
    Parabolic.normalizedOppositeRefinementTransitivity p F T n B S P.obj
  let j : (innerJacquet T B S μ).ρ.IntertwiningMap
      (Rep.of (T.normalizedComposedOppositeJacquet B S P.representation)).ρ :=
    Etrans.toIntertwiningMap.comp (T.normalizedRefinedOppositeJacquetMap B S i)
  have hj : Function.Injective j := Etrans.toLinearEquiv.injective.comp hiq
  let f : (ambientJacquet T B S μ).ρ.IntertwiningMap
      (Rep.of (T.normalizedComposedOppositeJacquet B S P.representation)).ρ :=
    T.normalizedComposedOppositeJacquetMap B S q
  have hf : Function.Surjective f := by
    change Function.Surjective (Representation.Coinvariants.map _ _
      (Jacquet.restrictMap q (Parabolic.composedOppositeUnipotent F.Carrier B S)))
    exact coinvariants_map_surjective _ hq
  obtain ⟨c, hc, -⟩ := HeadDetectingCount.exists_count_le_of_surjective τ f hf hambient
  exact ⟨c, jordanHolderInjectiveMonotonicity ℂ (refinedLevi F.Carrier B S)
    (innerJacquet T B S μ) _ τ j hj m c hinner hc, count_flattened T B S P.obj τ hc⟩

end Transport

section Positive

variable {G : Type*} [Group G]

/-- An irreducible subquotient of a finite-length representation has a positive
count. -/
theorem count_pos_of_isSubquotient {A : Rep.{uA} ℂ G} {τ : Rep.{uT} ℂ G}
    (hτ : Representation.IsIrreducible τ.ρ)
    (hA : IsFiniteLength (MonoidAlgebra ℂ G) A.ρ.asModule)
    (hsub : WeylBranchPieces.IsSubquotient A.ρ τ.ρ) :
    ∃ c, 0 < c ∧ HasJordanHolderMultiplicity A τ c := by
  obtain ⟨r, s, hs⟩ := MultiplicityAdditivityProof.exists_series hA
  have hA' : HasJordanHolderMultiplicity A τ (s.factorMultiplicity τ) := ⟨r, s, hs, rfl⟩
  obtain ⟨U, q, hq⟩ := hsub
  let iU : (Rep.of U.toRepresentation).ρ.IntertwiningMap A.ρ :=
    { toLinearMap := U.toSubmodule.subtype
      isIntertwining' _ := rfl }
  obtain ⟨mU, hU, hmU⟩ := HeadDetectingCount.exists_count_le_of_injective τ iU
    (Submodule.injective_subtype _) hA'
  let K : Rep.{uA} ℂ G := Rep.of (q.ker.toRepresentation)
  let iK : K.ρ.IntertwiningMap (Rep.of U.toRepresentation).ρ :=
    { toLinearMap := q.ker.toSubmodule.subtype
      isIntertwining' _ := rfl }
  obtain ⟨a, c₁, -, hc₁, hac⟩ :=
    jordanHolderShortExactDecomposition ℂ G K (Rep.of U.toRepresentation) τ τ iK q
      (Submodule.injective_subtype _) hq (Submodule.range_subtype _) mU hU
  have h1 : HasJordanHolderMultiplicity τ τ 1 :=
    (irreducibleMultiplicity.2 ℂ G τ τ hτ 1).mpr (Or.inl ⟨⟨Representation.Equiv.refl _⟩, rfl⟩)
  have := HasJordanHolderMultiplicity.unique hc₁ h1
  exact ⟨s.factorMultiplicity τ, by omega, hA'⟩

end Positive

end Langlands.Classification.A6ii
