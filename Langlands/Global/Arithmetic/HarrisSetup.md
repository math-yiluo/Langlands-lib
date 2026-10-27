# The arithmetic hypotheses of Harris's Proposition 4.8

Author: Worker 35. Definition contribution to task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1.
The declarations are proposition definitions, a structure of data, and two
proved lemmas about `IsAlgebraicAfterTwist` (with two private helper lemmas).
Nothing is assumed. No automorphic representation, no weak automorphic
induction and no existence theorem appears here. The conclusion of
Proposition 4.8 is a separate statement.

This version corrects the infinity-type condition of the datum; see
[Correction](#correction).

## Mathematical content

The namespace is `Langlands.Global.Harris`. Number fields are Mathlib's
`NumberField` types. Finite places are the Library's `FinitePlace K`, the
nonzero primes of `𝓞 K` (`HeightOneSpectrum`), with the actual adic
completions `FiniteCompletion K v`. Archimedean places are Mathlib's
`InfinitePlace K`, with completions `InfiniteCompletion K τ`. A Hecke
character is the Library's `HeckeCharacter K`, a continuous homomorphism
from the actual idele-class group to `ℂˣ`. Its components
`finiteComponent v` and `infiniteComponent τ` are its restrictions to
the local multiplicative groups.

### Conditions on a Hecke character

- `IsAlgebraic χ`, for a totally complex `K`: there is an integral
  infinity type `a : InfinityType K` (an integer for every complex
  embedding `σ : K → ℂ`) such that the archimedean part of `χ` equals the
  Library's character `InfinityType.toCharacter a`. At a place `τ`, with
  coordinate `z` through Mathlib's chosen embedding `σ_τ`, this character
  is

  \[
    z \longmapsto z^{a(\sigma_\tau)}\,\overline z^{\,a(\overline{\sigma_\tau})}.
  \]

  Every pair of integers occurs at every place. The condition therefore
  says that `χ_∞(x) = ∏_σ σ(x)^{a(σ)}` with integral exponents
  (Weil's type `A₀`).
- `IsAlgebraicAfterTwist a χ`, for a totally complex `K` and `a : ℕ`:
  there is an integral infinity type `t` such that, for every archimedean
  idele `x` with coordinates `z_τ`,

  \[
    \chi_\infty(x) \cdot \prod_\tau |z_\tau|^{a} = \mathrm{toCharacter}(t)(x).
  \]

  Every place `τ` is complex, and its normalized absolute value is
  `‖z‖_τ = |z|²`, so `∏_τ |z_τ|^a` is the archimedean part of the idele
  norm `‖·‖^{a/2}`. The condition is therefore Harris's "`χ · ‖·‖^{a/2}` is
  of type `A₀`" (p.195). Only the archimedean part matters: the finite part
  of `‖·‖^{a/2}` does not affect the infinity type. Two lemmas are proved:
  - `isAlgebraicAfterTwist_zero_iff`: for `a = 0` the condition is
    `IsAlgebraic χ`;
  - `isAlgebraicAfterTwist_add_two_iff`: the conditions for `a + 2` and
    `a` are equivalent, because `∏_τ |z_τ|² = ∏_τ z_τ z̄_τ` is the
    character of the infinity type with all exponents `1`. So the
    condition depends only on the parity of `a`, as Harris says ("if `a` is
    any integer congruent to `a(ν) (mod 2)`").
- `IsConjugateInverse χ`, for a CM field `K`: `χ(c x) = χ(x)⁻¹` for every
  idele class `x`. Here `c` is the Library's
  `AdelicFunctoriality.ideleClassComplexConj`, the action of Mathlib's
  `IsCMField.complexConj K` on the actual idele-class group. This is
  Harris's `χ = χ⁻¹ ∘ c`. It is the same condition as in the published
  `CMCharacterStatement`.
- `IsRelativelyRegular E χ`, for a totally complex `E` and a Hecke
  character `χ` of a finite extension `E'`: for every archimedean place
  `τ` of `E` and all places `w ≠ w'` of `E'` above `τ`, there is
  `x ∈ E_τˣ` with

  \[
    \chi_w(\iota_w(x)) \ne \chi_{w'}(\iota_{w'}(x)).
  \]

  Here `ι_w : E_τ → E'_w` is Mathlib's completion map
  `NumberField.LiesOver.completionMap`, the continuous extension of
  `E → E'`. So the components of `χ` at the distinct places above `τ`
  are pairwise distinct as characters of `E_τˣ`.

### Fields and places

- `IsSplitImaginaryQuadratic p K₀`: `[K₀ : ℚ] = 2`, `K₀` is totally
  complex, and two distinct primes of `𝓞 K₀` contain `p`. In a quadratic
  field this says that `p` splits.
- `HasUniquePlaceAbove L v`, for a finite place `v` of `E` and an
  `E`-algebra `L`: any two finite places of `L` lying over `v` are equal.
  (Existence of a place above `v` is automatic.)
- `PlaceDatum F F' E E' L` is the data Harris attaches to one place. Here
  `F` is a p-adic field (`PadicField p`), `F'` is a finite extension of
  `F` inside the common algebraic closure (`Extension F`), and
  `F̃ = galoisClosure F F'` is its normal closure there (Library,
  `GeneralPositionStatement`). The data are:
  - finite places `v` of `E`, `v'` of `E'` and `ṽ` (`vTilde`) of `L`, with
    `v' | v`, `ṽ | v'` and `ṽ | v` (instance fields of the structure);
  - a ring isomorphism `iso : E_v ≅ F`;
  - a ring isomorphism `isoTilde : L_ṽ ≅ F̃`.
- `PlaceDatum.IsCompatible P` has two parts. First, `isoTilde` extends
  `iso`: for `x ∈ E_v`,

  \[
    \mathrm{isoTilde}(\iota_{\tilde v / v}(x)) = \mathrm{iso}(x) \in F \subseteq \tilde F,
  \]

  with `ι_{ṽ/v}` the Library's completion map
  `AdelicFunctoriality.FiniteExtension.completionMap`. Second, `isoTilde`
  carries the image of `E'_{v'}` (under `ι_{ṽ/v'}`) exactly onto `F'`. So
  `isoTilde ∘ ι_{ṽ/v'}` is an isomorphism `E'_{v'} ≅ F'`.
- `PlaceDatum.HasComponent P χ η`, for a Hecke character `χ` of `E'` and
  a character `η` of `F'ˣ` (`FieldCharacter F F'`): whenever `x ∈ E'_{v'}ˣ`
  and `y ∈ F'ˣ` correspond under `isoTilde ∘ ι_{ṽ/v'}`, then
  `χ_{v'}(x) = η(y)`. When `P` is compatible, every `x` has such a `y`,
  and the condition says that the component of `χ` at `v'` is `η`
  transported along `E'_{v'} ≅ F'`.
- `conjPlace E v`, for a CM field `E`, is the complex-conjugate place
  `c(v)`: the place of `E` obtained from `v` through
  `IsCMField.complexConj E` (the Library's `finitePlaceEquiv`).

### The datum

`IsProposition48Datum e χ χs K₀ P Ps ξ` takes a reciprocity family
`e : ReciprocityFamily F`, characters `χ, χs` of `F'ˣ` (Harris's `χ` and
`χ(*)`), an intermediate field `K₀` of `E/ℚ`, two place data `P` and `Ps`
(Harris's `v₁` and `v(*)₁`), and a Hecke character `ξ` of `E'` (Harris's
bold `𝛘`). Both `E` and `E'` carry `IsCMField` instances. It is the
conjunction of:

1. `IsSplitImaginaryQuadratic p K₀`;
2. `IsScalarTower E E' L` and `IsNormalClosure E E' L`: the three algebra
   structures are compatible and `L` is a normal closure of `E'/E`
   (Mathlib's `IsNormalClosure`). So `L` is Harris's `Ẽ`;
3. for `P`: `p ∈ v₁`, `P.IsCompatible`, and exactly one place of `L`
   above each of `v₁` and `c(v₁)`;
4. the same for `Ps`, with `v(*)₁` and `c(v(*)₁)`;
5. `v(*)₁ ≠ v₁` and `v(*)₁ ≠ c(v₁)`: the two pairs of conjugate places
   are different;
6. `IsInGeneralPosition F F' (weilCharacter F e F' χs)`: the character
   `χs`, pulled back to `W_{F'}` through `e`, is in general position
   relative to `F` (Harris Definition 4.5, published in
   `GeneralPositionStatement`);
7. `IsAlgebraicAfterTwist ([E' : E] - 1) ξ` (written
   `Module.finrank E E' - 1`), `IsRelativelyRegular E ξ` and
   `IsConjugateInverse ξ`. The first is Harris's normalization of
   "algebraic" for automorphic induction to `GL(n)`, `n = [E' : E]`
   (derived choice 11). It is not `IsAlgebraic ξ` when `n` is even;
8. `P.HasComponent ξ χ` and `Ps.HasComponent ξ χs`.

## Instances, universes and scope

- The carrier universe of `F` is `uF`. `E`, `E'` and `L` live in arbitrary
  universes, and `K₀` is an `IntermediateField ℚ E`, so `K₀ ⊆ E` is part
  of its type.
- `IsTotallyComplex` instances for `E` and `E'` come from their
  `IsCMField` instances.
- `ReciprocityFamily F` is the Library's candidate family of local
  reciprocity maps. The datum does not assume `NormalizedReciprocity F e`.
  For an unnormalized `e`, condition 6 is about the wrong Weil
  characters. The statement of Proposition 4.8 assumes
  `NormalizedReciprocity F e`, as the published Library statements do.
- Every prime `p` is included, `p = 2` among them. There is no condition
  `n < p` and no tameness condition.
- The degree `n` is not a parameter (see derived choice 4).

## Original source correspondence

Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p* (1998). Page numbers are printed pages; PDF page = printed
page − 176. Each passage was read in both the PDF and the arXiv TeX source
`math_9611226v1.tex`; the pages below were checked against the printed
page numbers of the PDF.

The cohomological condition is taken from L. Clozel, *Motifs et formes
automorphes: applications du principe de fonctorialité*, in *Automorphic
Forms, Shimura Varieties, and L-functions I* (1990): Définition 1.8 and the
Remarque after it (printed pp.89–90, PDF pages 100–101) and Définition 3.12
(printed p.111, PDF page 122), as in the published
`Langlands/Automorphic/RegularAlgebraic`.

- **Reg(n,E) and Theorem 1.2, p.185 (PDF page 9; TeX lines 514–537).**
  `Reg(n,E)` consists of the isobaric representations whose cuspidal
  constituents are of cohomological type at infinity. Theorem 1.2(ii)
  takes `E = E₀·K₀` with `E₀` totally real and `K₀` imaginary quadratic,
  and `c` the nontrivial element of `Gal(E/E₀)`. The cohomological type
  is Clozel's (1990, Définitions 1.8 and 3.12): the restriction to `ℂ^×` of
  the parameter at each infinite place is `χ_1 ⊕ ⋯ ⊕ χ_n` with
  `χ_i(z) = z^{p_i+(n-1)/2} z̄^{q_i+(n-1)/2}`, `p_i, q_i ∈ ℤ`. The exponents
  lie in `(n−1)/2 + ℤ`, so their integrality depends on the parity of `n`.
  For `n = 1` the condition is that `χ_∞` is algebraic in the sense of
  `IsAlgebraic`.
- **Section 2, global setup, pp.192–193 (PDF pages 16–17; TeX lines
  996–1022).** The places `v₁, v₂` of `E` are the two primes above a place
  `v` of `E₀`, which splits because `p` splits in `K₀`. The primes `v'_i`,
  `ṽ_i` are defined "analogously", and `F` is identified with `E_{v₁}`.
  The tameness assumption and the semidirect-product shape of
  `Gal(Ẽ/E)` in this section belong to the tame case only, and Section 4
  does not assume them.
- **Definition 2.3, p.193 (PDF page 17; TeX lines 1024–1029).** An
  algebraic Hecke character `χ` of `E'` is `E'/E`-regular if, for any
  archimedean place `τ` of `E`, the components of `χ` at the distinct
  places of `E'` dividing `τ` are distinct. This is
  `IsRelativelyRegular`.
- **Proposition 2.4 and (2.4.1), p.193 (PDF page 17; TeX lines
  1031–1049).** For the induced representation `π` of Proposition 2.4,
  `π_τ ≅ χ_{τ_1} ⊞ ⋯ ⊞ χ_{τ_n}` at every archimedean place `τ` of `E`,
  where `τ_1, …, τ_n` are the places of `E'` above `τ`. So the archimedean
  exponents of `π` are those of the components of `χ`, without a shift.
- **The infinity type, p.195 (PDF page 19; TeX lines 1186–1219).**
  Section 3 constructs a Hecke character with the hypotheses of
  Proposition 2.4. Each of its archimedean components is
  `χ_ν = (z/z̄)^{a(ν)/2}`, with all `a(ν)` integers of the same parity.
  Then "if `a` is any integer congruent to `a(ν) (mod 2)` ... the product
  `χ · ‖•‖^{a/2}` is a Hecke character of type `A₀`, in Weil's
  terminology". And: "In order to obtain cohomological representations of
  `GL(n)` by automorphic induction we will take `a(ν) ≡ n−1 (mod 2)`".
  This is the normalization of condition 7, `IsAlgebraicAfterTwist`
  (derived choice 11). Harris also notes (p.191, PDF page 15; TeX lines
  866–875) that the induced representations are defined over the field of
  values "up to twisting by a half-integer power of the absolute value
  character".
- **Section 4, setup, p.200 (PDF page 24; TeX lines 1466–1500).**
  `(F', χ) ∈ G⁰(F)` with `[F' : F] = n`, and `F̃` is the Galois closure of
  `F'/F`. `E'/E` is an extension of CM fields as in Theorem 1.2(ii), with
  `E ⊇ K₀` and `p` split in `K₀`. `Ẽ` is the Galois closure of `E'/E`.
  Complex-conjugate places `v₁, v₂` of `E` above `p` are chosen "as in
  §2" with `E_{v₁} ≅ F`. Exactly one prime `ṽ₁` (resp. `ṽ₂`) of `Ẽ`
  divides `v₁` (resp. `v₂`), and `E_{v₁} ≅ F` extends to
  `Ẽ_{ṽ₁} ≅ F̃`. The primes `v'_i` of `E'` are "the corresponding primes",
  "so that `E'_{v'_1} ≅ F'`". A second pair `v(*)₁, v(*)₂` of
  complex-conjugate places above `p` has the same properties, with
  compatible isomorphisms `E_{v(*)₁} ≅ F` and `Ẽ_{ṽ(*)₁} ≅ F̃`. These are
  conditions 1–5, `PlaceDatum` and `IsCompatible`. Harris's remark that
  the second pair "can be arranged" by a real quadratic compositum is not
  part of the hypotheses.
- **Definition 4.5 and Proposition 4.8, p.201 (PDF page 25; Proposition
  4.8 at TeX lines 1554–1561).** `χ` and `χ(*)` are characters of
  `W_{F'}`, with `χ(*)` in general position relative to `F`. `𝛘` is an
  `E'/E`-regular algebraic Hecke character of `E'` with components `χ`
  and `χ(*)` at `v'₁` and `v(*)'₁`, and `𝛘 = 𝛘⁻¹ ∘ c`. These are
  conditions 6–8. Harris introduces Proposition 4.8 as "the following
  extension of Proposition 2.4", so "algebraic" is read in the
  normalization of p.195. The conclusion (a cuspidal `Π ∈ CU(n,E)` that is a weak
  automorphic induction of `𝛘`, supercuspidal at `v(*)₁`) is not part of
  this module.

### Derived choices

None of these changes the mathematical content. The equivalences are
explained here and are not formalized.

1. **CM fields containing `K₀`.** Harris takes `E = E₀·K₀` and
   `E' = E'₀·K₀` with `E₀, E'₀` totally real. The Lean datum takes CM
   fields `E, E'` with `K₀ ⊆ E`. These are the same. A compositum
   `E₀·K₀` is CM. Conversely, if `E` is CM and contains the imaginary
   quadratic `K₀`, then `K₀` is not contained in the totally real
   subfield `E⁺`. So `E⁺ ⊊ E⁺K₀ ⊆ E`, and `[E : E⁺] = 2` gives
   `E = E⁺·K₀`. The same holds for `E' ⊇ K₀`. The nontrivial element of
   `Gal(E/E⁺)` is the CM involution, so Harris's `c` is
   `IsCMField.complexConj`. Complex conjugation of `E'` restricts to that
   of `E`, so `c` is unambiguous.
2. **Comparing archimedean components.** The components at distinct
   places `w, w'` above `τ` are characters of different groups `E'_wˣ`,
   `E'_{w'}ˣ`. Definition 2.3 compares them, so they must be identified.
   The Lean definition compares them on `E_τˣ` through the canonical maps
   `ι_w`. Since `E` is totally complex, `τ` is complex, and `ι_w` is a
   continuous field embedding `ℂ → ℂ`, hence an isomorphism (the identity
   or complex conjugation in coordinates). This is the identification
   under which Harris forms the Langlands sum of these components as the
   component at `τ` of the induced representation ((2.4.1), p.193).
3. **`v₁ ≠ c(v₁)`.** Harris calls `v₁, v₂` a pair of complex-conjugate
   places. The Lean datum uses `c(v₁)` for `v₂` and does not require
   `v₁ ≠ c(v₁)`, because it follows. `v₁` lies above `p`, so it lies above
   a prime `𝔭` of `K₀` over `p`, and `c(v₁)` lies above `c(𝔭)`. Since `p`
   splits in `K₀`, `c` swaps the two primes above `p`, so `c(𝔭) ≠ 𝔭` and
   `c(v₁) ≠ v₁`. The conditions `p ∈ v₁` and `p ∈ v(*)₁` are stated
   explicitly although they also follow from `E_{v₁} ≅ F`.
4. **The degree.** Harris has `[F' : F] = n = [E' : E]`. The Lean datum
   has no `n`. Because exactly one place of `L` lies above `v₁`, exactly
   one place `v'₁` of `E'` does, and `[E'_{v'₁} : E_{v₁}] = [E' : E]`.
   `IsCompatible` makes `E'_{v'₁} ≅ F'` over `E_{v₁} ≅ F`, so
   `[F' : F] = [E' : E]`.
5. **`E'_{v'₁} ≅ F'`.** Harris writes "so that `E'_{v'_1} ≅ F'`" without
   naming the isomorphism. In general it is not a consequence of the
   other stated assumptions: the image of `E'_{v'₁}` in `F̃` is the fixed
   field of the image of `Gal(Ẽ/E')` in `Gal(F̃/F)`, and that subgroup
   need not be conjugate to `Gal(F̃/F')`. The Lean datum takes the isomorphism induced by
   `isoTilde` and requires its image to be `F'` itself. This is no loss.
   If the image is `F`-isomorphic to `F'`, then it is `σ(F')` for some
   `σ ∈ Gal(F̃/F)`, and `σ⁻¹ ∘ isoTilde` still extends `iso` (because `σ`
   fixes `F`) and has image `F'`. The components of `𝛘` at `v'₁` and
   `v(*)'₁` are read through this isomorphism.
6. **The places `v'` and `ṽ`.** `v'` is part of the data, with `ṽ | v'`.
   Once `ṽ` is the only place of `L` above `v`, `v'` is the only place of
   `E'` above `v`, so nothing is chosen.
7. **Uniqueness above `c(v₁)`.** Harris states uniqueness above `v₁` and
   above `v₂` separately. The Lean datum keeps both conditions.
8. **Isomorphisms of local fields.** `iso` and `isoTilde` are ring
   isomorphisms. A field isomorphism between finite extensions of `ℚ_p`
   is automatically continuous, by F. K. Schmidt's theorem that a
   non-separably-closed field has at most one henselian valuation
   topology. So these are isomorphisms of local fields, as in Harris.
   This fact is not used or proved here.
9. **Characters of `W_{F'}`.** Harris uses characters of `W_{F'}` and of
   `F'ˣ` interchangeably. The Lean datum takes `χ, χs` on `F'ˣ`, which is
   where the components of `𝛘` live, and passes to `W_{F'}` through
   `weilCharacter F e F'` only for general position.
10. **Name.** Harris's global character is a bold `𝛘`. The Lean name is
    `ξ`, because `𝛘` is not a valid identifier.
11. **"Algebraic".** Propositions 2.4 and 4.8 ask for an "algebraic"
    Hecke character without fixing the parity of its infinity type. Page
    195 fixes it for automorphic induction to `GL(n)`, and the conclusion
    of Proposition 4.8 requires it (see the consistency check below). The
    Lean datum states this as
    `IsAlgebraicAfterTwist (n - 1) ξ` with `n = [E' : E]`. By
    `isAlgebraicAfterTwist_add_two_iff`, any `a ≡ n − 1 (mod 2)` gives the
    same condition. Together with `IsConjugateInverse ξ` it says exactly
    that every archimedean component is `ξ_w(z) = (z/z̄)^{b_w/2}` with an
    integer `b_w ≡ n − 1 (mod 2)`, where `(z/z̄)^{b/2}` means `(z/|z|)^b`.
    The argument is as follows (it is not formalized). Since `E'` is CM,
    the involution `c` fixes every archimedean place `w` and acts on
    `E'_w ≅ ℂ` as complex conjugation. So `IsConjugateInverse` gives
    `ξ_w(z) ξ_w(z̄) = 1`. If `ξ_w(z) |z|^a = z^p z̄^q` with `p, q ∈ ℤ`, this
    gives `|z|^{2(p+q-a)} = 1`, so `p + q = a` and
    `ξ_w(z) = (z/|z|)^{p-q}` with `p − q = 2p − a ≡ a (mod 2)`.
    Conversely, `(z/|z|)^b |z|^a = z^{(a+b)/2} z̄^{(a-b)/2}` has integral
    exponents when `b ≡ a (mod 2)`.

    **Consistency with the conclusion.** By (2.4.1), the induced
    representation has archimedean exponents `±b_w/2` for the places `w`
    above `τ`. These lie in `(n−1)/2 + ℤ`, as Clozel's `Alg(n)` requires,
    exactly when `b_w ≡ n − 1 (mod 2)`. Relative regularity says that
    the components above `τ` are distinct as characters of `E_τˣ`. In one
    coordinate `z` of `E_τ`, the component at `w` is `(z/|z|)^{±b_w}`, with
    the sign `−` when `ι_w` is complex conjugation in coordinates. So the
    exponents read in that coordinate are distinct, which is Clozel's
    regularity (distinct exponents). In the Library's convention
    (`Langlands/Automorphic/RegularAlgebraic`) the infinitesimal character
    is `λ = μ + δ` with `μ` dominant integral and
    `δ = ((n−1)/2, …, −(n−1)/2)`.

    **Even-rank check.** Take `n = 2`, a place `τ` of `E` with places
    `w₁, w₂` of `E'` above it, and `b_{w₁} = 1`, `b_{w₂} = −1`. Then
    `ξ_{w_i}(z) |z| = z` or `z̄`, so condition 7 holds, and the
    holomorphic exponents `(1/2, −1/2)` give `μ = λ − δ = (0, 0)`: trivial
    coefficients. With the earlier condition `IsAlgebraic ξ`, every
    `b_w` is even. Then `λ` is integral, for example `λ = (1, −1)`, and
    `μ = λ − δ = (1/2, −1/2)` is not integral. No reordering or sign
    change makes it integral. For even `n` the earlier datum therefore
    did not match the conclusion of Proposition 4.8.

## Relation to other Library units

- `IsInGeneralPosition`, `galoisClosure`, `weilCharacter`,
  `ReciprocityFamily` and `FieldCharacter` are the published Library
  definitions (`Langlands/Global/Arithmetic/GeneralPositionStatement`,
  `Langlands/LocalFactor/CommonClosure`).
- The weak automorphic induction of the conclusion uses the published
  numerical relation `SpectralSystem.IsWeakInductionOf`
  (`Langlands/Automorphic/Unramified/WeakInduction`), whose Euler factors
  use the unitary Satake normalization and the unshifted values of the
  character. The conjugate self-duality in `CU(n,E)` is the published
  `CuspidalOperatorRealization.IsoClass.IsConjugateSelfDual`
  (`Langlands/Automorphic/ConjugateContragredient`). The cohomological
  condition of `Reg(n,E)` is the published
  `CuspidalOperatorRealization.IsoClass.IsRegularAlgebraic`
  (`Langlands/Automorphic/RegularAlgebraic`).
- The statement of Proposition 4.8, which combines this datum with
  `NormalizedReciprocity F e` and the conclusion, is a separate unit.

## Correction

The version published as artifact `69aadfaf-211b-493a-9964-5d44d632f329`
required `IsAlgebraic ξ` in condition 7. Reviewer 3482 found the defect
while reviewing the statement of Proposition 4.8 (candidate
`66d7ff71-1c22-4ccb-bf8b-7a43be9a62e2`, correction task
`541b5c26-ea9b-4ad0-80a0-6b89b978a05d`). For even `n` that condition
contradicts the normalization of p.195, as the even-rank check in derived
choice 11 shows. The earlier Markdown also said that Harris does not
define "algebraic Hecke character" separately, and it missed the
normalization of p.195. This version keeps `IsAlgebraic`
unchanged and replaces it in the datum by
`IsAlgebraicAfterTwist ([E' : E] - 1) ξ`. For odd `n` the new condition is
equivalent to the old one, by the two lemmas.
