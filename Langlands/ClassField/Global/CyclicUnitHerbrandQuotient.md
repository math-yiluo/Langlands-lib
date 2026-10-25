# The cyclic Herbrand quotient of ordinary units

`Langlands.ClassField.Global.cyclicUnitHerbrandQuotient.{u,v}` proves exactly
`Langlands.ClassField.Global.CyclicUnitHerbrandQuotient.{u,v}` from
`CyclicUnitHerbrandQuotientStatement`. For number fields `F : Type u` and
`E : Type v`, with `Algebra F E`, `IsGalois F E` and cyclic
`G = E ≃ₐ[F] E`, it proves that the actual ordinary cohomology groups
`H¹(G,U)` and `H²(G,U)` are finite and that

\[
 [E:F]\,|H^2(G,U)|=D_\infty\,|H^1(G,U)|.
\]

Here `U` is precisely `ringIntegerUnitsRepresentation F E`, whose carrier
is the additive form of `(𝓞 E)ˣ`, including its torsion, and
`D∞ = archimedeanHerbrandFactor F E`. All representations retain the
published arithmetic actions and lifted integer coefficient ring
`NormalizedTwoCocycle.CoefficientScalars.{v} = ULift.{v} ℤ`.
The field universes remain independent.

Write `HasHerbrandQuotient A q` for the published predicate asserting
finiteness of ordinary `H¹(G,A)` and `H²(G,A)`, together with
`(Nat.card H² : ℚ) = q * Nat.card H¹`. The proof uses this predicate to
carry both finiteness conclusions through every comparison and exact
sequence. It never infers finiteness from a bare cardinal identity.

The implemented proof uses the following published results.

1. `hasHerbrandQuotient_ofMulAction`, specialized to the actual action
   of `G` on `InfinitePlace E`, gives quotient `D∞` for
   `infinitePlaceLatticeRepresentation F E`. Its generic orbit-stabilizer
   product is definitionally the target's archimedean factor. This reuses
   the general permutation calculation underlying the separately proved
   infinite-place lattice formula.
2. Put `V = InfinitePlace E → ℝ`,
   `N = infinitePlaceCoordinateLattice E` and
   `M = augmentedFullLogUnitLattice E`. Both are actual discrete full
   integer lattices in the same finite-dimensional real space. Apply
   `hasHerbrandQuotient_iff_of_isZLattice` with real action
   `(fullLogPermutation F E g).toLinearMap`, with the additive realization
   `infinitePlaceLatticeRealization F E` on `N`, and the identity on `M`.
   Equivariance of the first realization is
   `infinitePlaceLatticeRealization_equivariant`; equivariance of the
   second is definitional from the restricted arithmetic action.
   This proves that the augmented lattice has quotient `D∞`.
   Fullness and equivariance supply the comparison; equal ranks alone
   would not suffice, and no commensurability assumption is used.
3. The actual short exact sequence `fullLogLatticeSequence F E` has
   terms `M₀ → M → ULift ℤ`, where
   `M₀ = fullLogUnitLattice E` is the image of the multiplicity-weighted
   full unit logarithm in the sum-zero hyperplane. Its quotient is the
   trivial lifted-integer representation, constructed using the
   equivariant integral splitting. The theorem
   `hasHerbrandQuotient_trivialIntegers` gives this representation
   Herbrand quotient `Nat.card G`. The identity
   `IsGalois.card_aut_eq_finrank F E` changes this to
   `n = Module.finrank F E`. Apply
   `HasHerbrandQuotient.of_shortExact_left` and
   `fullLogLatticeSequence_shortExact` to obtain quotient `D∞ / n` for
   `M₀`, together with finiteness of its first and second cohomology.
4. The inverse cohomology isomorphisms
   `fullLogEmbeddingCohomologyIso F E 1` and
   `fullLogEmbeddingCohomologyIso F E 2` transfer this result to
   `unitsModuloTorsionRepresentation F E`, using
   `HasHerbrandQuotient.of_linearEquiv`. These isomorphisms come from
   the published equivariant logarithmic representation isomorphism.
5. The coefficient module `unitTorsionRepresentation F E` is finite by
   `unitTorsionRepresentation_finite F E`; hence
   `hasHerbrandQuotient_of_finite` gives it quotient one and finite
   cohomology. Apply `HasHerbrandQuotient.of_shortExact` to the actual
   sequence `unitTorsionSequence F E`, using
   `unitTorsionSequence_shortExact`. Its middle term is the unchanged
   ordinary unit representation, so this proves its quotient is `D∞ / n`
   and supplies the two required finiteness conclusions.

Every cohomology group used in a quotient is a finite additive group
and contains zero, so its natural cardinality is positive. The imported
Herbrand calculus uses these nonzero orders when dividing and cancelling
in rational numbers. The local final step separately proves
`(n : ℚ) ≠ 0` from `Module.finrank_pos`, substitutes the rational identity
for `H²(G,U)`, clears the denominator with `field_simp`, and uses
`exact_mod_cast` to obtain the target equality of natural numbers.
Thus neither finite-cardinality cancellation nor division by the
extension degree relies on an unproved nonvanishing assertion.

The proof introduces exactly the hypotheses of the target. In particular,
there is no nontriviality condition on `G` or positivity condition on the
unit rank. Degree-one extensions and rank-zero unit groups are included.
The imported generic cohomology calculus, full-lattice comparison and
permutation calculation are already published; no further arithmetic
premise is assumed. The parent idele-class theorem and idele-class
`H¹` vanishing are not inputs.

This proves the derived all-infinite-places specialization of
Milne, *Class Field Theory*, v4.03 (2020), Chapter VII Proposition 3.1,
printed pp.207–209 (PDF pp.216–218), especially the two-lattice argument
on p.209 and Lemma 3.5. The implementation follows that assembly using
the published generic proofs and arithmetic representations. The
permutation calculation uses the published direct cyclic norm argument.
Registered source: `milne-2020-class-field-theory`,
`/home/taskhub/central-library/Milne--Class Field Theory (v4.03)--2020.pdf`,
SHA256 `50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.
The proof was supplied in a public draft by Worker 343 and checked and
documented for submission by Worker 406.
