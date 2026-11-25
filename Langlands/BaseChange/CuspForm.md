# Cusp forms on `GL_n`: vanishing constant terms and split tensor products

Lean module: `Langlands.BaseChange.CuspForm` (`Langlands/BaseChange/CuspForm.lean`), namespace
`Langlands.BaseChange`.

The module contains two definitions, `HasVanishingConstantTerms` (Harish-Chandra's cusp forms on
`GL_n(R)`) and `splitTensor` (the tensor product `φ_0 ⊗ … ⊗ φ_{l-1}` on `GL_n(F^l)`), and the
small lemmas listed below, all proved. It states no theorem of the literature; the statements
built on these definitions are in the modules `CuspFormConvolutionStatement`,
`SplitTensorCuspFormStatement`, `SupercuspidalExistenceStatement` and
`SupercuspidalCuspFormStatement`.

## Conventions

- `GL_n(R)` is the Library's `GeneralLinear n R`, which is Mathlib's
  `Matrix.GeneralLinearGroup (Fin n) R`, the units of the matrix ring, with Mathlib's topology
  on units (induced by `g ↦ (g, g⁻¹)` from the product topology on matrices).
- For `B : GeneralLinear.BlockShape n` (an ordered list of `B.length` positive block sizes with
  sum `n`), `B.parabolic R` is the Library's standard upper block triangular parabolic subgroup
  of `GL_n(R)` and `B.unipotentSubgroup R` is its unipotent radical (block upper triangular
  matrices whose diagonal blocks are identity matrices), a subgroup of `GL_n(R)` with the
  subspace topology (`Langlands/Group/GL/Blocks.lean`).
- `GL_n(R)` carries its Borel σ-algebra, introduced inside the definition by
  `letI : MeasurableSpace (GeneralLinear n R) := borel _`, as in the Library's
  `HasCharacterValue`. The subgroup `B.unipotentSubgroup R` carries the induced subtype
  σ-algebra, which is the Borel σ-algebra of its subspace topology.
- A Haar measure is Mathlib's `Measure.IsHaarMeasure`: left invariant, finite on compact sets
  and positive on nonempty open sets. No measure is chosen or normalized in this module.

## Definition 1: `HasVanishingConstantTerms`

For a commutative ring `R` with `[TopologicalSpace R] [IsTopologicalRing R]`, `n : ℕ` and
`f : GL_n(R) → ℂ`, `HasVanishingConstantTerms f` holds when for every block shape `B` with
`2 ≤ B.length` and every Haar measure `μ` on `B.unipotentSubgroup R`:

1. for all `x y : GL_n(R)`, the function `u ↦ f (x * u * y)` on `B.unipotentSubgroup R` is
   `Integrable` for `μ`; and
2. `Langlands.HarishChandraSchwartz.IsUnipotentCuspidal μ f`, that is,
   `∫ u, f (x * u * y) ∂μ = 0` for all `x y : GL_n(R)`.

The vanishing integral is not restated: clause 2 is the Library's predicate
`IsUnipotentCuspidal` (`Langlands/HarmonicAnalysis/HarishChandraSchwartz/CuspidalConvolution.lean`),
which needs only a group with a σ-algebra and a measure on a subgroup `U`. In the Library it
expresses one of the conditions defining Harish-Chandra's space of cusp forms `°𝒞(G)` in
Waldspurger 2003 (Lemma VIII.2.1, printed p. 321: `f ∈ °𝒞(G)` if and only if
`f^{(P),Ind} = 0` for every proper semi-standard parabolic `P`; the proof of Lemma VIII.2.3,
printed p. 322), where it is used on Harish-Chandra Schwartz functions. Definition 1 applies it to the
unipotent radical of every proper standard block parabolic subgroup of `GL_n(R)` and to every
Haar measure on it, and adds integrability. The `[IsTopologicalRing R]` argument is part of the
signature, although the body only uses the topology of `GL_n(R)`.

Mathematical meaning. For `P = M U` a parabolic subgroup, the constant term of `f` along `P` at
`m` is `∫_U f(m u) du` (up to the modulus character, which does not affect vanishing). Definition
1 asks that all constant terms of all two-sided translates `g ↦ f (x * g * y)` vanish along every
proper standard block parabolic. Since `∫_U f(x u y) du = ∫_{x U x⁻¹} f(v x y) dv'`, where `dv'` is
the image of `du` under `u ↦ x u x⁻¹`, quantifying over `x` and `y` also covers every conjugate
`x P x⁻¹` of a standard block parabolic and both left and right translations of `f`. Every
parabolic subgroup of `GL_n` over a field is conjugate to a standard block parabolic, so this is
Harish-Chandra's notion of a cusp form: all constant terms of `f` along proper parabolic
subgroups vanish. This is the property of the functions in Henniart-Lemaire's condition
`c_{v₁}(f)` (HL 2011, II.6.3, printed p. 120: `f_{v₁}` vanishes off the regular elliptic elements
and is a linear combination of coefficients of irreducible smooth cuspidal representations) that
the simple trace formula uses. The coefficients of a supercuspidal representation have vanishing
constant terms because its Jacquet modules vanish (Casselman 1995, §5.1, printed p. 46).

Why `Integrable` is part of the definition. Mathlib's Bochner integral of a non-integrable
function is `0` by convention, so clause 2 alone would hold trivially for such functions, and the
sum of two functions satisfying clause 2 need not satisfy it. With clause 1 the integral is
additive (`integral_add`), so sums of cusp forms are cusp forms
(`HasVanishingConstantTerms.add`). For a locally constant compactly supported `f` on `GL_n(F)`
(`F` a nonarchimedean local field), clause 1 holds automatically for every Haar measure on the
closed subgroup `B.unipotentSubgroup F` (this is not proved here).

Why every Haar measure is allowed. Over a nonarchimedean local field `F`, `GL_n(F)` is locally
compact and `B.unipotentSubgroup F` is closed in it (the Library's `isClosed_unipotentSubgroup`),
hence locally compact, so a Haar measure on it exists and the quantifier over `μ` is not
vacuous. Any two Haar measures on it differ by a positive scalar, so the conditions for one Haar
measure and for all Haar measures are equivalent there; quantifying over all of them avoids
choosing or normalizing one. Over a general topological ring a Haar measure need not exist, and
then the condition for that `B` is empty; the statements that use definition 1 work over
nonarchimedean local fields.

Why `2 ≤ B.length`. A block shape with one block gives the whole group (`B.parabolic R = ⊤`),
and the unique block shape of `n = 0` has no block. With at least two blocks the parabolic is
proper as soon as `1 ≠ 0` in `R` (a matrix unit below the diagonal blocks gives an element
outside it), so over a field the condition `2 ≤ B.length` is equivalent to the condition
`B.parabolic F ≠ ⊤` used in the Library's `GeneralLinear.IsSupercuspidal`. This equivalence is
explained here and not formalized. For `n ≤ 1` no block shape has two blocks
(`BlockShape.length_le : B.length ≤ n`), so every function is a cusp form
(`hasVanishingConstantTerms_of_le_one`), as it should: `GL_1` and `GL_0` have no proper
parabolic subgroup.

Block parabolics over `R = Fin l → F`. The definition is stated for a commutative topological
ring so that it applies to `GL_n(F^l)`, `F^l = Fin l → F` with the product topology. A matrix
over `F^l` is an `l`-tuple of matrices over `F`, so `B.parabolic (Fin l → F)` consists of the
`g` whose `l` coordinates `g_i` all lie in `B.parabolic F`, and similarly for
`B.unipotentSubgroup`. Thus the block parabolics of `GL_n(F^l)` are the products
`P(F) × … × P(F)` of one block parabolic `P` of `GL_n(F)` with itself, not arbitrary products
`P_0(F) × … × P_{l-1}(F)`. These are the local points of the parabolic subgroups of `GL_n` over
a cyclic extension `E` of a number field at a place of the base field that splits completely in
`E` (where `E ⊗ F_v = F_v^l`): a parabolic subgroup of `GL_n` over `E` gives the same block
parabolic in each factor. This is all that the twisted trace formula needs. The description of
the parabolics of `GL_n(F^l)` is explained here and not formalized.

## Definition 2: `splitTensor`

For a commutative ring `F`, `l n : ℕ` and `φ : Fin l → GL_n(F) → ℂ`,
`splitTensor φ : GL_n(Fin l → F) → ℂ` is the function

```text
g ↦ ∏ i, φ i (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : Fin l => F) i) g),
```

where `Matrix.GeneralLinearGroup.map (Pi.evalRingHom _ i)` takes the `i`-th coordinate of every
matrix entry, giving `g_i ∈ GL_n(F)`. Under the identification `GL_n(F^l) = GL_n(F)^l`,
`g ↦ (g_0, …, g_{l-1})`, it is the tensor product `φ_0 ⊗ … ⊗ φ_{l-1}`. This is the shape of the
test function at a place that splits completely in a cyclic extension of degree `l`
(Arthur-Clozel 1989, Chapter 1, §5, printed pp. 48-49, where the σ-twisted orbital integrals of
`φ_1 ⊗ … ⊗ φ_m` are computed through the convolution `φ_1 ∗ … ∗ φ_m`). For `l = 0`, `Fin 0 → F`
is the zero ring and `splitTensor φ` is the constant function `1` (empty product) on the
one-element group `GL_n(Fin 0 → F)`.

## Lemmas (proved)

- `hasVanishingConstantTerms_zero`: the zero function satisfies definition 1.
- `HasVanishingConstantTerms.add`, `.neg`, `.sub`: if `f` and `g` satisfy definition 1, so do
  `fun x => f x + g x`, `fun x => -f x` and `fun x => f x - g x`.
- `HasVanishingConstantTerms.const_mul`: if `f` satisfies definition 1, so does
  `fun x => c * f x` for every `c : ℂ`.
- `hasVanishingConstantTerms_sum`: for a `Finset` `s` and functions `f i` each satisfying
  definition 1 (for `i ∈ s`), `fun x => ∑ i ∈ s, f i x` satisfies definition 1.
- `HasVanishingConstantTerms.comp_mul_left` and `.comp_mul_right`: if `f` satisfies definition
  1, so do `fun g => f (a * g)` and `fun g => f (g * a)`, for every `a : GL_n(R)`. The proofs
  apply the hypothesis to `(a * x, y)` and to `(x, y * a)`.
- `hasVanishingConstantTerms_of_le_one`: if `n ≤ 1`, every `f : GL_n(R) → ℂ` satisfies
  definition 1, because `BlockShape.length_le` gives `B.length ≤ n ≤ 1 < 2`.
- `splitTensor_apply`: the defining formula of definition 2 (by `rfl`).

The proofs of the closure lemmas use Mathlib's `integral_add`, `integral_neg` and
`integral_const_mul` together with clause 1 of the hypotheses, and `Finset.induction_on` for
sums.

## Sources

- Henniart-Lemaire 2011 (`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`),
  Chapter II, §II.6.3, printed p. 120 (PDF p. 128): the condition `c_{v₁}(f)` of the simple
  trace formula.
- Casselman 1995 (`casselman-1995-admissible-representations`), §5.1, printed p. 46:
  absolutely cuspidal (supercuspidal) representations have zero Jacquet modules along every
  proper parabolic subgroup.
- Waldspurger 2003 (`waldspurger-2003-plancherel`), Lemma VIII.2.1 (printed p. 321) and the
  proof of Lemma VIII.2.3 (printed p. 322): the condition `IsUnipotentCuspidal` reused in
  definition 1.
- Arthur-Clozel 1989 (`arthur-clozel-1989-base-change`), Chapter 1, §5, printed pp. 48-49
  (PDF pp. 62-63): tensor-product test functions at a place that splits in the extension.

## Provenance

Definition 1 formalizes Harish-Chandra's cusp-form condition as it is used in HL's condition
`c_{v₁}(f)`; the restriction to standard block parabolics with all two-sided translations, the
quantifier over Haar measures and the integrability clause are formalization choices explained
above. Definition 2 is the tensor-product test function of Arthur-Clozel, Chapter 1, §5, written
through the coordinate projections of `F^l`.
