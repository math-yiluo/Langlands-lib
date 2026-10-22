# Actual standalone transport of common-closure Weil–Deligne pairs

Worker 40 authored this derived arithmetic attachment of the published
group-equivalence factor transport. Its namespace is
`Langlands.LocalFactor.CommonClosureWeilDeligne.Transport`.

## Actual arithmetic inputs

Fix a prime `p`, fields `F : PadicField.{uF} p` and
`E : PadicField.{uE} p`, and an actual algebra homomorphism
`f : F.Carrier →ₐ[Padic p] E.Carrier`. The field universes are independent.
Write `J = LocalClassField.extensionFiniteIntermediate F E f`. This is the
existing finite intermediate image field in the chosen algebraic closure of
`F`, with the choices retained from the published closure lift.

Let `H` be its common-closure Weil subgroup, and put
`e = LocalClassField.extensionImageWeilEquiv F E f : W_E ≃ₜ* H`.
The comparison is this published topological group equivalence onto the
actual fixing subgroup. It is not the generally non-surjective inclusion
`W_E → W_F`. The common-closure inertia `I_J` is the kernel of the
base-field degree restricted to `H`; the standalone inertia is
`I_E = Weil.Local.localInertia E`.

`normCharacter_comp` proves that the common-closure covariance character
pulls back along `e` to the actual standalone `localNormCharacter E`.
It is monoid-homomorphism extensionality applied to the published
`extensionImageWeilEquiv_normCharacter`. `inertia_comap` proves the subgroup
equality `I_J.comap e.toMonoidHom = I_E`, by subgroup extensionality and
`Weil.Local.extensionWeilMap_mem_localInertia`. Thus the construction
identifies the actual inertia groups without requiring a supplied subgroup
comparison or a supplied norm equality.

## The standalone pair and representation comparisons

For `A : CommonClosureWeilDeligne.Pair F J`, `standalonePair F E f A`
has the exact type `Weil.Local.LocalWeilDeligneRepresentation E`.
It first forms the existing `WeilDeligneRepresentation.restrict e.toMonoidHom A`.
The vector space, action, monodromy and nilpotence proof are retained. The
covariance proof is expressed using the actual standalone norm through the
proved norm identity. In formulas its data are
\[
 r_E(w)=r_A(e(w)),\qquad N_E=N_A,\qquad
 r_E(w)N_Er_E(w)^{-1}=|w|_E N_E.
\]
`standalonePair_representation` and `standalonePair_monodromy` expose the
first two identities by reflexivity. The carrier universe is `max uF uV`,
as in the existing restriction construction; the standalone Weil group
remains in the independent field universe `uE`.

The pair constructor itself is algebraic. Given ordinary finite-dimensional
complex continuity of `A.toFiniteRepresentation`,
`standalonePair_isContinuous` retains it by restricting along the actual
continuous comparison. No continuity proof is fabricated or built into a
stronger parameter predicate. `standalonePairEquiv` restricts an equivalence
of common-closure pairs, retaining its linear intertwiner and its
monodromy-commutation law.

`invariantsEquiv`, `kernelEquiv` and `quotientEquiv` have, respectively,
the following meanings as equivalences of representations of `W_E`:
\[
 (V_{A_E})^{I_E}\simeq (V_A)^{I_J},\qquad
 (\ker N_E)^{I_E}\simeq(\ker N_A)^{I_J},\qquad
 (V_{A_E})^{I_E}/(\ker N_E)^{I_E}
   \simeq (V_A)^{I_J}/(\ker N_A)^{I_J}.
\]
On the right each original representation is restricted along `e`.
These are specializations of the published
`LocalFactor.WeilDeligne.Transport` equivalences using `inertia_comap`.
The invariant and kernel comparisons retain the underlying vectors;
the quotient comparison is induced by the invariant comparison.
Two private reflexive lemmas identify the kernel and quotient
representations before and after changing the covariance proof. They
allow Lean to recognize the actual dependent carriers and their actions.

## Factor and regular-domain identities

Every factor comparison holds for an arbitrary `w : W_E`. The standalone
side uses `(A_E,I_E,w)`, and the common-closure side uses `(A,I_J,e(w))`.
The proved identities are:

- `conductorCorrection_standalonePair`: equality of the invariant-quotient
  dimensions.
- `eulerPolynomial_standalonePair`: equality of
  `det(1 - X r(w) | (ker N)^I)`.
- `rationalLFactor_standalonePair`: equality of the reciprocal Euler
  polynomials in `RatFunc ℂ`.
- `quotientDeterminant_standalonePair`: equality of
  `det(-r(w) | V^I/(ker N)^I)`.
- `quotientCorrectionPolynomial_standalonePair` and
  `quotientCorrection_standalonePair`: equality of the correction monomial
  `det(-r(w) | Q) X^(dim Q)` and its image in the rational-function field.
- `quotientConstantCorrection_standalonePair` and
  `quotientCorrectionValue_standalonePair`: equality of the constant
  determinant units and of the unit-valued corrections at every
  `z : ℂˣ`, with the same scalar on both sides.

The dimension proof uses the quotient linear equivalence. The Euler and
negative-determinant proofs use conjugacy by the kernel and quotient
equivalences. The reciprocal, polynomial, rational and unit equalities
then follow from those identities and the published factor definitions.
The negative sign in the quotient determinant is preserved.

`regularPointEquiv` identifies the actual domains of regular scalar
evaluation. Both maps retain `z : ℂ`; the Euler-polynomial identity
transports the certificate that its evaluation at `z` is nonzero.
`regularPointEquiv_val` gives this coordinate identity, and
`regularLValue_standalonePair` proves equality of the corresponding
unit-valued reciprocal evaluations. The construction assigns no finite
value at a zero of the Euler denominator.

## Provenance and scope

The retained original for the underlying pair and factor conventions is
Tate, “Number theoretic background,” Corvallis proceedings (1979),
§4.1.2, printed page 20 (Part II PDF page 29), for the covariance relation,
and §4.1.6, printed pages 20–21 (PDF pages 29–30), for the fixed monodromy
kernel, reciprocal Euler determinant, conductor correction and negative
determinant on the invariant quotient. Source ID:
`tate-1979-number-theoretic-background`; PDF SHA-256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
These pages were read directly during this unit's development.

This attachment is a derived compatibility of existing Library
constructions, not a separately attributed theorem of Tate.
Its internal dependencies are `CommonClosureWeilDeligne` for the
common-closure pair and inertia; `WeilDeligneTransport` for the actual
invariant, kernel and quotient comparisons; `WeilDeligne.Restriction`
for restriction; `ClassFieldTheory.Local.ReciprocityTransport` and
`Weil.Local.ExtensionWeil` for the actual Weil equivalence, norm identity
and inertia preimage law; `Weil.Local.Parameters` for the standalone pair;
and `Weil.Representation.InductionContinuity` for continuity of restriction.

The comparison is unconditional on reciprocity or epsilon-system existence.
Its pair is an algebraic Weil–Deligne pair, with continuity preserved only
when supplied. It does not claim the open-inertia hypotheses of Tate's
arithmetic parameter category for every algebraic input.

The identities use corresponding arbitrary Weil elements. This unit does
not identify the geometric Frobenius subtype or prove equality of the
intrinsic residue cardinalities needed for spectral coordinates `q^(-s)`.
It does not transport a full ordinary epsilon system, additive characters
or Haar measures, and proves no system existence or functional equation.
The quotient determinant is only the monodromy correction to a full
epsilon factor. Choice-independence and composition coherence for the
existing closure lift are not asserted. The broad host task remains open.
