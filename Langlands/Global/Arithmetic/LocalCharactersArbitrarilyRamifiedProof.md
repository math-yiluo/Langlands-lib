# Finite-order characters detecting actual principal units

Author: Worker 455.

The theorem `Langlands.Global.localCharactersArbitrarilyRamified` proves
the existing proposition
`Langlands.Global.LocalCharactersArbitrarilyRamifiedStatement.{u}` from
`Langlands.Global.Arithmetic.CharacterPrescriptionStatement`. For every
number field `K : Type u`, finite place `v`, and natural number `r`, it
constructs a continuous character of the actual local multiplicative group,
a positive natural exponent annihilating that character, and an actual
integral unit witnessing nontriviality at depth `r`. The field universe
remains arbitrary.

This is a derived local ingredient in the choice of highly ramified
finite-order characters in Henniart (1986), Section 4.3, printed
pp.158–159. The implementation constructs a deep unit, separates it in an
open finite quotient, and invokes the published theorem
`Langlands.Global.integralUnitCharacterExtension`. Serre's unit filtration
supplies the source convention. The proof does not need an identification
of successive filtration quotients.

## Exact arithmetic objects

Write `F = FiniteCompletion K v`, `O = v.adicCompletionIntegers K`,
and `m = IsLocalRing.maximalIdeal O`. These are the actual adic completion
and its valuation ring and maximal ideal from the target. The integral-unit
inclusion is exactly

```lean
Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom
```

from `Oˣ` to `Fˣ`. The asserted witness is `a : Oˣ` with
`(a : O) - 1 ∈ m ^ r` and character value different from one after this
inclusion. At depth zero, `m ^ 0` is the whole ring; at positive depth the
condition is the usual membership in `1 + m^r`.

All topologies are the existing completion, subtype and units topologies.
The proof does not transport characters from a different presentation of
the local field.

## Separating a point of a compact abelian group

The private helper `compact_character_separates` treats a compact Hausdorff
totally disconnected commutative topological group `G`. Given `a ≠ 1`,
the complement of the singleton `{a}` is an open neighborhood of one.
The published Van Dantzig theorem
`Langlands.Topology.LocallyProfiniteProof.vanDantzig`, applied using
`Langlands.Topology.isLocallyProfinite_of_mathlib`, gives an open subgroup
`H` contained in that neighborhood. Thus `a ∉ H`.

Commutativity makes `H` normal. Set `Q = G ⧸ H` and let `q` be the
continuous quotient homomorphism. Mathlib's
`Subgroup.quotient_finite_of_isOpen` makes `Q` finite, and
`QuotientGroup.discreteTopology` makes its quotient topology discrete.
The coset `q a` is different from one, since the identity coset consists
of `H`.

Apply Mathlib's `AddChar.exists_apply_ne_zero` from
`Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality` to the nonzero
element `Additive.ofMul (q a)`. It supplies an additive character
`ψ : AddChar (Additive Q) ℂ` whose value at that element is different from
one. Here an additive character takes sums to products and zero to one.
Consequently `b ↦ ψ (Additive.ofMul b)` is a multiplicative homomorphism
`φ : Q →* ℂ`.

`MonoidHom.toHomUnits` promotes `φ` to a homomorphism to `ℂˣ`, since
images of group elements are invertible. The map is continuous because
`Q` is discrete. Its composition with `q` is a continuous character
`η : G →ₜ* ℂˣ` with `η a ≠ 1`; applying `Units.val` to a hypothetical
equality would contradict the choice of `ψ`. This helper proves
separation. The final proof obtains its explicit finite-order assertion
from the extension theorem described below.

## Compactness and total disconnectedness of the actual integral units

The imported theorem `Langlands.Global.isCompact_adicCompletionIntegers`
provides compactness of `O`. Mathlib's compact-units instance then
provides compactness of `Oˣ`. The units topology embeds `Oˣ` into
`O × Oᵐᵒᵖ` by recording an element and its inverse.

The private helper `integral_units_totallyDisconnected` installs the
valuative relation and nonarchimedean local-field structure from
`CompletionPadic.topologicalData v` on the same `F`. Its local-field
instance supplies total disconnectedness of `F`. This passes to the
subtype `O`, then to `Oᵐᵒᵖ` using the opposite homeomorphism. The product
is totally disconnected, and `Units.isEmbedding_embedProduct` transfers
that property to `Oˣ`. Together with its existing Hausdorff topological
group structure and compactness, this supplies the hypotheses of the
separation helper.

## A nonidentity unit at every requested depth

The private helper `deep_nonidentity_unit` uses the completion valuation,
whose values lie in `WithZero (Multiplicative ℤ)`.
`valuedAdicCompletion_surjective K v` supplies `x : F` with
`Valued.v x = WithZero.exp (-1 : ℤ)`. This value is nonzero and less than
one, so `x` defines a nonzero element `π : O`.

The criterion `adicCompletionIntegers.isUnit_iff_valued_eq_one`,
together with the local-ring description of the maximal ideal as the
nonunits, gives `π ∈ m`. For the requested `r`, set `b = π^(r+1)`.
Ideal-power membership gives `b ∈ m^(r+1)`, and the inclusions
`m^(r+1) ≤ m` and `m^(r+1) ≤ m^r` give both `b ∈ m` and `b ∈ m^r`.

Since `-b ∈ m`, the local-ring theorem
`IsLocalRing.isUnit_one_sub_self_of_mem_nonunits` applied to `-b`
proves that `1 + b` is a unit. Its associated element `a : Oˣ` satisfies
`(a : O) - 1 = b ∈ m^r`. If `a = 1`, its value in `O` would give
`b = 0`, contradicting `pow_ne_zero` for the nonzero `π`.

The choice of exponent `r+1` handles `r = 0` in the same proof: the witness
already belongs to the first principal units. Nothing in this argument
excludes residue characteristic two or imposes a condition on the
residue-field size.

## Finite order, extension and final assembly

Apply the separation helper to the constructed `a` in `G = Oˣ`, obtaining
`η : Oˣ →ₜ* ℂˣ` with `η a ≠ 1`. The imported theorem
`Langlands.Global.integralUnitCharacterExtension` then supplies
`χ : Fˣ →ₜ* ℂˣ`, a natural number `n > 0` with `χ ^ n = 1`, and
pointwise equality

```text
χ (Units.map O.subtype.toMonoidHom b) = η b
```

for every `b : Oˣ`.

That dependency proves finite order of continuous integral-unit characters
using an open kernel and its finite index. It constructs a continuous
multiplicative retraction `P : Fˣ → Oˣ` by removing the valuation with a
chosen splitting element, and extends by `η.comp P`. The retraction is the
identity after the actual inclusion, and composition preserves the positive
annihilating exponent. These facts are proved in the imported
`IntegralUnitCharacterExtensionProof` module.

The final theorem retains the supplied finite-order assertion and uses
the same `a` and ideal-power membership. Rewriting the extension equality
at `a` turns the required nontrivial character value into `η a ≠ 1`.
This proves the exact target predicate. The period may depend on `K`, `v`
and `r`; the target imposes no uniform period.

## Original sources and provenance

- Guy Henniart, *On the Local Langlands Conjecture for GL(n): The Cyclic
  Case* (1986), Section 4.3, printed pp.158–159 (one-based PDF
  pp.15–16). Registered source `henniart-1986-cyclic`, SHA-256
  `096fba993b7368b1af9f7cc1f0c053e5436ba447f291c2acd402f058eb44b0ba`.
  This is the motivation for choosing finite-order characters with large
  ramification, rather than a claim that the present construction is a
  separately stated theorem there.
- Jean-Pierre Serre, *Local Fields*, English translation (1979),
  Chapter IV, Section 2, unit filtration and Proposition 6, printed p.66
  (PDF p.73), read in context pp.65–67 (PDF pp.72–74).
  Registered source `serre-1979-local-fields`, SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
  This identifies the principal-unit convention. The implementation uses
  an arbitrary separating open finite quotient in place of the explicit
  successive quotients.
- Jean-Pierre Serre, *Corrections to J-P. Serre's books* (2019),
  complete *Local Fields* entries on PDF pp.2–3. Registered source
  `serre-book-corrections-2019`, SHA-256
  `b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`.
  These entries contain no correction to the cited p.66 passage.

The cited passages and correction entries were read directly. The
finite-quotient separation and the assembly with the published extension
are the internal derived proof explained above. The only public theorem
added by this module is `localCharactersArbitrarilyRamified`; its three
auxiliary lemmas are private.
