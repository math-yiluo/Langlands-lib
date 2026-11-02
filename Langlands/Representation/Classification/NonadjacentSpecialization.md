# Invariant forms between supercuspidal pieces

Author: Worker 745. Helper module of the proof of Ze80 Proposition 1.11(a),
first conjunct (task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`).

This module supplies the separation step of BZ77 §4.8 (Bernstein and
Zelevinsky 1977, `bernstein-zelevinsky-1977-induced-i`, proof of Lemma 4.7(b),
printed pp.455–456): "From the existence of non-zero pairing of `σ` and
`π̄^(k)` it follows that `σ̄ ∈ JH(π̄^(k))`." For supercuspidal pieces this
becomes: a nonzero invariant form between `A` and `ν B~` forces `B ≅ ν A`.

## Declarations

Namespace `Langlands.Classification.NonadjacentAssembly`.

Section `Separation`. `G` is a topological group, and the forms have
covariance `1`.

- `leftKernel B`: the left kernel of an invariant form is an invariant
  subspace.
- `left_nondegenerate hρ B hB`: a nonzero invariant form on an irreducible
  first argument is left-nondegenerate.
- `nonempty_equiv_of_forms_ne_zero hcof hρ hσ hρi hσi B hB`: for `G` with
  cofinal compact open subgroups, irreducible admissible `ρ`, irreducible
  smooth `σ`, and a nonzero invariant form `B` on `ρ × σ`, `σ` is equivalent to
  the smooth contragredient of `ρ`. Both sides of `B` are nondegenerate by
  `left_nondegenerate` (for the flipped form via the published `flipEquiv`).
  The published `smoothInvariantPairingDuality` then gives the equivalence.

Section `Classes` (`F : PadicField.{uF} p`, `T` explicit):

- `twist_class_eq_of_length_ne_zero' A B' hB`: for supercuspidal `A`, `B'` of
  `GL_a`, a nonzero `length` of forms between `A` and `dualTwist B' = ν B'~`
  forces `[B'] = ν[A]` (`T.supercuspidalClassRealPowerTwist a 1`). The proof
  takes a nonzero form and gets `ν B'~ ≅ A~` from
  `nonempty_equiv_of_forms_ne_zero`. Supercuspidal representations are
  irreducible and admissible. The published closure of supercuspidality under
  contragredients (`supercuspidalContragredient`) and the published class laws
  (`SupercuspidalClass.contragredient_isoClass_eq_isoClass_iff`,
  `contragredient_contragredient`, `contragredient_twist`, `twist_congr`,
  `realPowerCharacter_neg`, `supercuspidalClassRealPowerTwist_add` and `_zero`)
  then turn this into `[B'] = ν[A]`.
- `twist_class_eq_of_length_ne_zero h1 h2 hB`: the same after rank casts
  `a = m`, `b = m`, stated for rank-indexed classes in
  `Σ d, SupercuspidalClass (n := d)`.
- `sigma_ne_twist ha A`: for `a > 0`, `[A] ≠ ν[A]` as rank-indexed classes.
  The proof is the published `cuspidalIntegralTwistFreeness` (module
  `Classification.CuspidalIntegralTwistFreenessProof`) at exponent `1`. This
  is BZ77 4.2, Remark 1: "`ρ ≇ νρ` since `ρ` and `νρ` differ on the center".

The universes `uF` (field) and `uV` (supercuspidal carriers) are independent.

## Provenance and dependency audit

All proofs here are original to this module; published results are used only
by import. Direct imports: `NonadjacentAssembly`,
`Classification.TwoSupercuspidalProductDualTwist` (my published module),
`Classification.CuspidalIntegralTwistFreenessProof`,
`Smooth.Contragredient.InvariantPairingProof`, `Filtration.ObjectTransport`
and `HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof`.

`CuspidalIntegralTwistFreenessProof` imports only its statement,
`Smooth.Schur.Proof` and `LocalField.Uniformizer`. Its proof compares central
characters at a scalar uniformizer, using Schur's lemma. Its statement module
imports `Classification.Segments`, and through it `ConstituentRelations`, for
the `CuspidalDatum` type. `ConstituentRelations` contains definitions only.
`Segments` contains definitions (cuspidal data, segments, multisegments,
linkage, segment products, and the socle/head predicates) and elementary
laws: equivalence invariance of these predicates, twist and rank arithmetic,
and linkage symmetry. Neither module states or proves any result excluded by
task `3c9849a4` (segment socle or head existence, Jacquet formulas,
classification, exhaustion or product irreducibility).
