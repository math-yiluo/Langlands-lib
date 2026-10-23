# Cuspidal Jacquet multiplicities

Author: Worker 19.

`Langlands.GLCuspidalJacquetMultiplicityStatement` states exact composition
lengths and constituent multiplicities for the upper and opposite normalized
Jacquet modules of normalized cuspidal induction on positive-rank `GL_n`.
`Langlands.GLCuspidalJacquetMultiplicityPrerequisitesStatement` is the named
entry point for exactly this proposition, with the same three independent
universe parameters. Both declarations are proposition definitions.
No representation-theoretic theorem is proved.

## Mathematical statement

Let `F` be any finite extension of `Q_p`, with compatible topological data `T`.
Let `B` and `C` be standard positive block shapes of the same positive rank.
Assume their embedded Levis are associated: an actual permutation matrix
conjugates the source Levi onto the target Levi. Let `ρ` be an irreducible
cuspidal representation of the actual product Levi of `B`.

Put `I = i_B^G ρ`. For either the upper or opposite parabolic of `C`, its
normalized Jacquet module has composition length

```
card (MinimalConjugatingPermutations B C).
```

For every irreducible representation `τ` of the target Levi, its multiplicity
in either module is

```
card (AssociatingPermutations B C ρ τ).
```

These are genuine finite subtypes of permutation matrices. The first chooses
the minimal Weyl representatives that conjugate the whole source Levi onto
the target. The second retains exactly those whose transported source
representation is equivalent to `τ`. Transport uses inverse conjugation in
the action. Thus repeated isomorphic factors are counted separately.

For example, with equal source and target Levi and `τ = ρ`, the latter cardinal is the
number of relative Weyl elements stabilizing the isomorphism class of `ρ`.
It need not be one. For nonisomorphic `τ` outside the Weyl orbit the count is
zero. No constituent multiplicity-free claim is made.

## Lean correspondence and hypotheses

`IsLeviCuspidal B ρ` means admissibility together with vanishing actual
unipotent coinvariants for every proper standard block refinement.
Admissibility includes smoothness. Irreducibility is a separate hypothesis.
No tensor factorization of the inducing representation is assumed.

`HasCompositionSeriesLength A r` supplies an actual finite filtration from
zero to the entire representation, all of whose successive quotients are
irreducible. `HasJordanHolderMultiplicity A τ m` supplies such a composition
series with exactly `m` factors equivalent to `τ`. The biconditional for
every `m` asserts both existence with the specified count and exclusion of
any other count. The Jordan–Hölder independence needed to prove it is already
a separate Library statement.

The field, source carrier, and target carrier universes are independent.
Induction enlarges the carrier universe to `max uF uV`; the quotient
filtrations stay there, and actual representation equivalences compare their
factors with `τ` in the independently quantified universe `uW`.
No composition series, finite-length conclusion, splitting, or isomorphism
class representative is assumed as input.

Only associated standard Levis are in this statement. Nonassociated
Jacquet vanishing and absence of cuspidal subquotients are separate clauses
of the published `PadicQuasicuspidalJacquetTheorems`. This statement does not
assert that the Jacquet modules are semisimple.

## Bundled constructions and expression sharing

The namespace `Langlands.CuspidalJacquetMultiplicity` contains three direct
wrappers around the actual published constructions:

* `induced T B A` bundles `T.normalizedParabolicInduced B A.ρ` as a `Rep`.
* `upperJacquet T C A` bundles `T.normalizedJacquet C A.ρ` as a `Rep`.
* `oppositeJacquet T C A` bundles the opposite coinvariant action with the
  inverse upper full modulus, transported by `C.leviEquiv`.

The statement applies these wrappers to `Rep.of ρ`. Their carrier, additive
group and complex-module structures are the original ones; the wrappers
introduce no assumption, chosen composition series or new mathematical object.
They are internal implementation definitions derived directly from those
constructions. The intermediate `I`, `Ju` and `Jo` are bundled representations,
and the length and multiplicity predicates take `Ju` and `Jo` directly.

Bundling prevents the dependent carrier and instance expressions for the
induced function space and its coinvariant quotients from being repeated in
every occurrence of the final proposition. Unfolding the three wrappers gives
the original unbundled proposition by definitional equality. Its independent
field, source-carrier and target-carrier universes, every quantifier and
hypothesis, and both normalization conventions are unchanged.

## Sources and derivation

The retained originals were read directly. The relevant formulas were also
checked in page images.

* Allan J. Silberger, *Introduction to Harmonic Analysis on Reductive p-adic
  Groups* (1979), Theorem 5.4.1.1, printed pp.287–288 (PDF pp.293–294).
  Literature ID `silberger-1979-harmonic-analysis`, SHA-256
  `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
  In its cuspidal case, for either associated parabolic with a fixed Levi,
  the full Jacquet module has length equal to the relative Weyl group order
  and the character is the sum of the Weyl-transported inducing characters,
  with the displayed half-modulus. The bracketed discrete-series case
  concerns only the maximal tempered part and is not included here.
* I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups. I* (1977), §1.2 and §1.7, p.443; §§2.1–2.7,
  pp.446–447; Corollary 2.13(c) and §2.15(3), p.449.
  Literature ID `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  PDF page numbers are printed page numbers minus 439.
  Corollary 2.13(c) gives the filtration for associated source and target
  Levis, with one quotient per right coset in `W(M,N)/W_M`.
  Section 2.15(3) explicitly identifies the constituent multiplicity with
  the cardinality of the cosets transporting the inducing representation
  to that constituent.
* Allan J. Silberger, *The Langlands quotient theorem for p-adic groups*
  (1978), §1 and §2, p.97. Literature ID
  `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
  retained PDF SHA-256
  `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
  The article defines constituent multiplicity by composition factors and
  records the cuspidal Jacquet factors with their Weyl multiplicities.
  Its later use is in the proof of Lemma 5.3, p.100.

This is a derived specialization to `GL_n` and finite extensions of `Q_p`.
For upper target parabolics, the existing
`AssociatedJacquetFiltrationTheorem` provides the precise filtration target;
irreducibility of `ρ` makes every Weyl-transported quotient irreducible.
Counting its factors, followed by Jordan–Hölder independence, gives the
formula here. The minimal representatives identify the right cosets rather
than counting every permutation inside a Levi block.

For the opposite target parabolic, conjugate it to an upper standard
parabolic by reversing the order of the target blocks. The source is still
cuspidal; parabolic conjugation transports the Jacquet representation and
reindexes its Weyl factors bijectively. Pulling back to the original target
Levi leaves exactly the same conjugating cosets and multiplicities.
Equivalently, Silberger's fixed-Levi result permits either parabolic and
transport extends it to associated Levis. These are mathematical derivations
whose Lean proofs remain open.

## Normalization and remaining obligations

Upper induction is the actual covariant-function representation with right
translation and `δ_B^(1/2)` covariance. Upper Jacquet uses the actual upper
unipotent quotient and `δ_C^(-1/2)` normalization.
Opposite Jacquet uses the actual opposite unipotent quotient; its full
modulus in `normalizedActionOfModulus` is `δ_C⁻¹`, so its scalar is
`δ_C^(1/2)`. Both actions are transported from the embedded Levi to the
actual product Levi by `leviEquiv`. A positive half-modulus is not inserted
on the upper quotient to simulate the opposite quotient.

The explicit determinant modulus still needs its separate Haar-modulus
comparison proof. The geometric lemma, conjugation transport, irreducibility
under transport, finite-factor counting, and Jordan–Hölder independence
remain proof obligations. The discrete-series maximal-tempered-part formula
and the finer regular-parameter comparisons of Silberger 1978 Lemmas 5.3
and 5.6 are not asserted by this pair. No errata note for the cited sources
was present in the Library when it was prepared.
