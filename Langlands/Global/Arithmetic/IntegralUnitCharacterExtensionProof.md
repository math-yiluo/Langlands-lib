# Finite-order extension from the actual integral units

Authors: Worker 55 and Worker 450.

The theorem `Langlands.Global.integralUnitCharacterExtension` proves the
existing proposition
`Langlands.Global.IntegralUnitCharacterExtensionStatement.{u}`. For every
number field `K : Type u`, every finite place `w`, and every continuous
character
`η : (w.adicCompletionIntegers K)ˣ →ₜ* ℂˣ`, it constructs a continuous
character on `(FiniteCompletion K w)ˣ`, a positive natural exponent that
annihilates that character, and the required equality on all actual integral
units. The universe `u` remains arbitrary.

This is the local ingredient used at the start of Henniart's proof of
Section 3.6, Lemma 3, printed p.451. It applies to every number field and
does not require a CM hypothesis. Global Hecke-character prescription and
infinity-type realization remain separate results.

## Actual arithmetic objects and topologies

Write `F = FiniteCompletion K w` and `O = w.adicCompletionIntegers K`.
Here `F` is the actual adic completion, and `O` is its actual valuation
subring, with its subspace topology. Mathlib's
`mem_adicCompletionIntegers` identifies membership in `O` with
`Valued.v x ≤ 1`, where the completion valuation takes values in
`WithZero (Multiplicative ℤ)`. Its theorem
`adicCompletionIntegers.isUnit_iff_valued_eq_one` identifies the units of
`O` with elements of valuation exactly one.

The inclusion used throughout the proof is exactly
`Units.map O.subtype.toMonoidHom`. Its continuity follows by applying the
units-map continuity theorem to the continuous subring inclusion. Thus the
restriction asserted by the final theorem uses the map in the published
statement.

The unit groups carry Mathlib's units topology. This topology records both
an element and its inverse through `Units.embedProduct`; continuity of a
map into a unit group is checked in both coordinates by
`Units.continuous_iff`. The proof uses this criterion for the constructed
retraction, including its inverse coordinate.

The imported theorem `Langlands.Global.isCompact_adicCompletionIntegers`
establishes compactness of this same `O`. Its local-field comparison uses
`CompletionPadic.topologicalData w`, whose topology is the completion's
original topology. The comparison
`CompletionPadic.topologicalData_vle` identifies its valuative order with
the completion valuation order. These results supply compactness and the
local-field structure without replacing the target completion by another
topological field.

## Finite order on the integral units

The helper `compact_units` upgrades compactness of `O` to compactness of
`Oˣ` using Mathlib's compact-units instance. The underlying argument is
the closed embedding `Units.isClosedEmbedding_embedProduct`: its image
consists of pairs `(a,b)` satisfying `ab = ba = 1`. These equations define
a closed subset of the compact product `O × Oᵐᵒᵖ`, since multiplication is
continuous and `O` is Hausdorff. This supplies the unit-group compactness
needed below.

The actual completion is totally disconnected by its nonarchimedean
local-field structure. The continuous injective map
`Oˣ → F`, obtained by forgetting first the unit structure and then the
subtype structure, transfers total disconnectedness to `Oˣ`. Together
with compactness and Hausdorffness, this gives
`Langlands.Topology.isLocallyProfinite_of_mathlib`. The published theorem
`Langlands.Topology.LocallyProfiniteProof.vanDantzig` then provides an open
subgroup inside every identity neighborhood. The helper
`nonarchimedean_units` packages this conclusion as
`NonarchimedeanGroup Oˣ`.

Apply the published theorem
`Langlands.isOpen_ker_of_continuous_complex_character` to `η`. Its
no-small-subgroups argument for complex units proves that the kernel is
open. Compactness now gives a finite quotient by the kernel, through
`Subgroup.quotient_finite_of_isOpen`.

Let `N = ker η` and choose `n = N.index`. The quotient is nonempty and
finite, so `n > 0`. The theorem `Subgroup.pow_index_mem` gives
`a ^ n ∈ N` for every integral unit `a`. Consequently
`η a ^ n = η (a ^ n) = 1`. Extensionality for continuous monoid
homomorphisms proves `η ^ n = 1`, as required by the helper
`finite_order`. No unitary assumption on the input character is needed.

## A continuous retraction to the integral units

The construction uses the completion valuation directly. For
`a : Fˣ`, put

\[
  \ell(a)=\operatorname{WithZero.log}(v(a))\in\mathbb Z.
\]

The valuation of a nonzero element is nonzero, so `WithZero.log_mul`
proves `ℓ(ab) = ℓ(a) + ℓ(b)`. The theorem `Valued.locally_const`
shows that valuation is locally constant away from zero. Pulling these
neighborhoods back along the continuous value map `Fˣ → F` proves that
`ℓ` is locally constant and hence continuous into discrete `ℤ`.

Mathlib's `valuedAdicCompletion_surjective` supplies an element of
valuation `WithZero.exp (1 : ℤ)`. This value is nonzero, so the chosen
element defines a field unit `t`, called `splittingUnit` in Lean. In this
multiplicative valuation convention, the corresponding additive order is
`-log v`; therefore `t⁻¹` has additive order one. This choice is the
inverse-uniformizer version of the usual decomposition.

Define the field-unit part by

\[
  P_F(a)=a\,t^{-\ell(a)}.
\]

The identity `v(t) = exp(1)`, the valuation power law, and
`exp(log(v(a))) = v(a)` give `v(P_F(a)) = 1`. Both `P_F(a)` and its inverse
therefore belong to `O`. The helper `unitPart` equips these two elements
with their inverse identities to construct an actual element
`P(a) : Oˣ`.

Additivity of `ℓ` and commutativity of `Fˣ` prove
`P(ab) = P(a)P(b)`. Since `ℤ` is discrete, the map
`m ↦ t^(-m)` is continuous. Composing with `ℓ` and multiplying by `a`
proves continuity of `P_F`. The two-coordinate criterion
`Units.continuous_iff` then proves continuity of `P` into `Oˣ`.

For `b : Oˣ`, the actual inclusion has valuation one, so its logarithm
is zero. Substituting in the formula gives
`P (Units.map O.subtype.toMonoidHom b) = b`. This is
`unitPart_inclusion`, the retraction identity. Applying it to one also
supplies the identity-preservation field when assembling `P` as a
continuous monoid homomorphism.

## Extension and source correspondence

The final proof takes `χ = η.comp P`. Composition supplies both the
homomorphism and continuity. If `η ^ n = 1`, evaluation at `P(a)` proves
`χ(a)^n = 1` for every `a : Fˣ`, and extensionality gives `χ ^ n = 1`
with the same positive exponent. The retraction identity proves the
stated pointwise agreement with `η` after the exact integral-unit
inclusion.

Henniart chooses a finite-order extension of a local unit character at
the beginning of Lemma 3. The present proof supplies that local choice
using compactness, an open kernel, and a valuation splitting. Serre's
uniformizer decomposition is implemented by removing the valuation
logarithm. The needed open-subgroup basis comes from total disconnectedness
and Van Dantzig, followed by the proved complex no-small-subgroups
argument. Serre's explicit principal-unit filtration supplies source
context for that neighborhood property. These are alternative proof
details for the same derived local step.

The construction makes one choice of splitting element; the target asks
only for existence of an extension. Henniart's later assembly prescribes
local characters on units, allowing the unramified infinity-realization
factor to affect values on uniformizers. This local theorem imposes no
uniformizer-value requirement on that later global assembly.

## Original sources

- Guy Henniart, *Une preuve simple des conjectures de Langlands pour
  GL(n) sur un corps p-adique*, Invent. Math. 139 (2000), 439–455:
  Section 3.6, Lemma 3 and the beginning of its proof, printed p.451
  (retained PDF page 13). Registered source
  `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- Jean-Pierre Serre, *Local Fields*, English translation by Marvin Jay
  Greenberg, GTM 67, Springer (1979): Chapter I, Section 1, printed p.5
  (PDF page 13), the valuation and uniformizer decomposition; Chapter II,
  Section 1, Proposition 1, printed p.27 (PDF page 35), compactness of
  the valuation ring; Chapter IV, Section 2, printed p.66 (PDF page 73),
  the principal-unit neighborhood basis. Registered source
  `serre-1979-local-fields`, SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
- Jean-Pierre Serre, *Corrections to J-P. Serre's books* (2019),
  complete *Local Fields* entries on PDF pages 2–3. Registered source
  `serre-book-corrections-2019`, SHA-256
  `b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`.
  None of these entries changes the three passages cited above.

These original passages and the specified errata entries were read
directly. The finite-order character-extension formulation is a derived
local result; it is not attributed to a separately numbered theorem in
Serre.
