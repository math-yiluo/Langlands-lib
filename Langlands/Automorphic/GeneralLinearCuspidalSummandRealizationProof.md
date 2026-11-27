# Irreducible cuspidal `L²` summands of `GL_n` come from cuspidal operator realizations

Module `Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationProof`. The theorem
`Langlands.Automorphic.GroupSchemeFunctions.generalLinearCuspidalSummandRealization` proves the
unchanged proposition `GeneralLinearCuspidalSummandRealizationStatement.{u}` (module
`Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationStatement`).

## Statement

Let `F` be a number field whose adele quotient `𝔸_F / F` is compact, let `r` be a natural
number, and assume `ParabolicDynamicStatement`. Let `T → GL_{r+1}` be a central homomorphism
from a split torus (identified with `splitTorus` on a finite type `I` by `e`) whose character
restriction is injective with image of finite index; the centre `G_m` is the basic example.
Haar measure on the norm-one subgroup of `GL_{r+1}(𝔸_F)` is right invariant. Let `S` be the
full almost-everywhere cuspidal subspace of `L²` of the positive-central rational quotient
(`fullAEL2CuspidalSubmodule`), with its right action `πc`
(`fullAEL2CuspidalBoundedRightAction`).

For every submodule `P` of `S` that is nonzero, closed, `πc`-invariant and has no closed
`πc`-invariant submodules other than `0` and itself, the theorem gives a cuspidal operator
realization `R : CuspidalOperatorRealization F r` and a `ℂ`-linear map `Φ : R.Space → S` such
that

- every vector `f` of `R` satisfies `IsGeneralLinearFormClass F r T i (Φ f) (R.realization.toContinuous f)`:
  the class `Φ f` has a continuous representative on the quotient whose pullback to
  `GL_{r+1}(𝔸_F)`, in the matrix model, is the form `f`; and
- the closure of the range of `Φ` is `P`.

The conventions for the Library's forms (smoothness at each finite coordinate, finite level,
`K∞`-finiteness, finiteness under the centre of the enveloping algebra, growth on each finite
slice) are those explained in `GeneralLinearCuspidalSummandRealizationStatement.md`, section
"Conventions: smoothness and growth".

## Implemented proof

The proof is a single application:

`generalLinearCuspidalSummandRealizationFromDensity generalLinearSummandFormsDense`.

- `generalLinearCuspidalSummandRealizationFromDensity` (module
  `Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationFromDensity`) proves
  `GeneralLinearSummandFormsDenseStatement.{u} → GeneralLinearCuspidalSummandRealizationStatement.{u}`.
  It applies `generalLinearCuspidalSummandRealizationReduction` (module
  `Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationReduction`) to the density
  premise and two proved inputs: differential stability `generalLinearSummandFormsEnveloping`
  and algebraic irreducibility `generalLinearSummandFormsIrreducible`. The reduction takes for
  `R` the stable cuspidal forms attached to `P` (`summandForms`, the stable automorphic
  functions whose matrix-model function is cuspidal and has a class in `P`), shows that they
  form an operator realization, takes for `Φ` the map sending a form to its class
  (`summandClassMap`), and uses density to identify the closure of the range of `Φ` with `P`
  and to see that `R` is nonzero.
- `generalLinearSummandFormsDense` (module
  `Langlands.Automorphic.GeneralLinearSummandFormsDenseProof`) proves the density premise: every
  vector of such a `P` lies in the closure, in `S`, of the classes of the stable cuspidal forms
  attached to `P`. Its own Markdown describes how nonzero forms with classes in `P` are built
  (convolution, averaging over a compact open subgroup of the finite adelic points, `K∞`-finite
  averaging and archimedean smoothing) and how minimality of `P` upgrades their existence to
  density.

The paired Markdown files of these modules describe the three inputs in detail. The theorem
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The statement is the summand-to-realization direction of Theorem 9.7.3 in J. R. Getz and
H. Hahn, *An Introduction to Automorphic Representations*, Graduate Texts in Mathematics 300,
Springer, 2024 (literature ID `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`): Theorem 9.7.3, printed
p. 265 (PDF p. 277), proof printed pp. 265–267 (PDF pp. 277–279), in particular display (9.40);
together with Theorem 9.7.1, printed p. 264 (PDF p. 276), and Lemma 9.7.2, printed p. 264
(PDF p. 276). The `L²_cusp` space and discrete cuspidal automorphic representations are those
of §6.5, printed pp. 168–169 (PDF pp. 182–183). The Library's form conventions follow
A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*, Proc. Sympos.
Pure Math. 33, part 1, 1979, pp. 189–202 (literature ID `borel-jacquet-1979-automorphic`),
§4.1–4.2, printed pp. 194–195 (PDF pp. 189–190).

In the book, the `K`-finite vectors of the summand are shown to be cusp forms (9.40), dense in
the summand (Lemma 9.7.2), and irreducible as a `(𝔤, K∞) × G(𝔸_F^∞)`-module (Theorem 6.6.2).
The Lean proof assembles analogous facts in the Library's form model: the realization `R` is
the space of stable cuspidal forms attached to `P`, its classes are dense in `P`, and it is
algebraically irreducible under the Library's finite adelic, archimedean compact and
enveloping operators. The proof does not identify the range of `Φ` with the `K`-finite vectors
of `P`. The proofs of the three inputs follow internal routes, described in the Markdown of the
modules named above, rather than the book's sequence of steps.
