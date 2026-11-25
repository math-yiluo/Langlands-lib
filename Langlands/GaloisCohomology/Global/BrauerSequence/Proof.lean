import Langlands.GaloisCohomology.Global.BrauerSequence.Restriction

/-!
# The fundamental exact sequence of the Brauer group: assembly

`BrauerSequenceData K Ω ι` is proved field by field from the Library's class field theory:

* finiteness of the support and the reciprocity law: `localInvariant_finite_support_and_sum_eq_zero`
  (`Hasse.lean`); injectivity: `eq_zero_of_brauerLocalization_eq_zero'` (`Hasse.lean`); existence and
  uniqueness: `existsUnique_brauerLocalization_eq'` (`Existence.lean`);
* restriction to extensions with large local degrees: `brauerRestriction_eq_zero'`
  (`Restriction.lean`);
* cyclic extensions with prescribed local degrees: `exists_isCyclic_dvd_localDegree`
  (`CyclicLayers.lean`).

The two fields on the degrees above two, the vanishing of `H³(Gal(Ω/K), Ωˣ)` and the isomorphism
onto the real places in degrees `r ≥ 4`, are stated as one proposition,
`UnitsCohomologyHigherDegreesStatement`, and this file proves the Brauer sequence from it
(`brauerSequenceStatement_of_higherDegrees`). The proposition is proved in
`Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees` (`unitsCohomologyHigherDegreesStatement`,
whence `brauerSequenceStatement`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

/-- **The degrees above two.** For every number field `K`, separable closure `Ω` and choice of
embeddings `ι`: `H³(Gal(Ω/K), Ωˣ) = 0`, and for `r ≥ 4` the localization of `Hʳ(Gal(Ω/K), Ωˣ)` to the
real places is an isomorphism onto the product of the local groups. Proved as
`unitsCohomologyHigherDegreesStatement` in `Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees`. -/
def UnitsCohomologyHigherDegreesStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ι : PlaceEmbeddings K Ω),
    Subsingleton (cohomology (unitsModule K Ω) 3) ∧
      ∀ r : ℕ, 4 ≤ r → Function.Bijective fun (x : cohomology (unitsModule K Ω) r)
        (w : {w : InfinitePlace K // w.IsReal}) => realBrauerLocalization ι w.1 r x

section Data

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω)

/-- A global Brauer class is nonzero at only finitely many finite places (the field `finite_support`
of `BrauerSequenceData`). -/
theorem brauerLocalization_finite_support (x : cohomology (unitsModule K Ω) 2) :
    {v : HeightOneSpectrum (𝓞 K) | brauerLocalization ι v 2 x ≠ 0}.Finite :=
  (localInvariant_finite_support_and_sum_eq_zero ι x).1.subset fun v hv => by
    rw [Function.mem_support, ne_eq, localInvariant_eq_zero_iff]
    exact hv

/-- **The Brauer sequence from the degrees above two.** Given the degrees `≥ 3`, all of
`BrauerSequenceData` holds. -/
theorem brauerSequenceData_of_higherDegrees
    (h3 : Subsingleton (cohomology (unitsModule K Ω) 3))
    (h4 : ∀ r : ℕ, 4 ≤ r → Function.Bijective fun (x : cohomology (unitsModule K Ω) r)
      (w : {w : InfinitePlace K // w.IsReal}) => realBrauerLocalization ι w.1 r x) :
    BrauerSequenceData K Ω ι where
  finite_support := brauerLocalization_finite_support ι
  eq_zero_of_brauerLocalization_eq_zero := eq_zero_of_brauerLocalization_eq_zero' ι
  sum_localInvariant_eq_zero x := (localInvariant_finite_support_and_sum_eq_zero ι x).2
  existsUnique_brauerLocalization_eq := existsUnique_brauerLocalization_eq' ι
  subsingleton_cohomology_three := h3
  bijective_realBrauerLocalization := h4
  brauerRestriction_eq_zero E _ x m hm hreal hloc :=
    brauerRestriction_eq_zero' ι E x m hm (fun _ _ => hreal _) hloc
  exists_isCyclic_dvd_localDegree := exists_isCyclic_dvd_localDegree K Ω

end Data

/-- **The fundamental exact sequence of the Brauer group**, for every number field, separable closure
and choice of embeddings, from `UnitsCohomologyHigherDegreesStatement`. -/
theorem brauerSequenceStatement_of_higherDegrees (h : UnitsCohomologyHigherDegreesStatement.{u}) :
    BrauerSequenceStatement.{u} := fun K _ _ Ω _ _ _ ι =>
  brauerSequenceData_of_higherDegrees ι (h K Ω ι).1 (h K Ω ι).2

end Langlands.GaloisCohomology
