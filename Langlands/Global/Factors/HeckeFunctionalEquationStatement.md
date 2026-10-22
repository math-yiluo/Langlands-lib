# The global functional equation of Hecke L-functions

Author: Worker 35. Statement contribution to task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1.
All declarations are proposition definitions. Defining them neither
proves nor assumes any existence or analytic assertion.

The target is `Langlands.Global.HeckeGlobalFunctionalEquationStatement`.
It is Tate (1979), Section 3.5, Theorem 3.5.3, in the abelian case
`V = χ`, where the theorem is Hecke's. The global additive character
is fixed and every local measure is self-dual.

## Actual objects

The field `K : Type u` is an arbitrary number field. A Hecke character
is the published `HeckeCharacter K`, a continuous homomorphism from the
actual idele classes to the complex units. Its local components
`χ.finiteComponent v` and `χ.infiniteComponent v` are the published
composites with the actual local insertions. The inverse character
`χ⁻¹` is the pointwise inverse in the group of continuous homomorphisms.

The global additive character `ψ` is an arbitrary
`UnitaryAdditiveCharacter (Adeles K)` on Mathlib's adele ring
`InfiniteAdeles K × FiniteAdeles K`. Two hypotheses are imposed, as
in Tate's Section 3.5: `ψ` is nontrivial (`∃ x, ψ x ≠ 1`), and `ψ`
is trivial on the diagonal image of `K`. No new structure is
introduced for global additive characters.

The local components of `ψ` are not chosen data. They are pinned
down by proposition definitions:

- `IsFiniteAdditiveComponent ψ v ψv` says that `ψv x` is `ψ` of the
  adele with `x` at the finite place `v` and zero elsewhere. That adele
  is `(0, RestrictedProduct.single _ v x)`.
- `IsRealAdditiveComponent ψ v hv a` says that at a real place the
  same restriction, via `Pi.single v x`, is
  `x ↦ exp(2πi a ι(x))`, where `ι` is Mathlib's ring isomorphism
  `InfinitePlace.Completion.ringEquivRealOfIsReal` and `a` is a nonzero
  real number. The character is the published `realScaledCharacter a`,
  equal to `Real.fourierChar (a * x)`.
- `IsComplexAdditiveComponent ψ v hv a` is the analogue at a complex
  place. It uses Mathlib's chosen isomorphism
  `ringEquivComplexOfIsComplex` and the published
  `complexScaledCharacter a`, i.e. `z ↦ exp(2πi Tr_{ℂ/ℝ}(a z))` with
  `a` a nonzero complex number.

The archimedean local characters of `χ` are presented through the same
isomorphisms. `IsRealCharacterPresentation hv η d` and
`IsComplexCharacterPresentation hv η d` say that the published data
`d : RealCharacterData` or `d : ComplexCharacterData` has character
`d.character` equal to `η` after `Units.map` of the isomorphism. Those
structures fix the polar form `sgn(x)^ε |x|^t`, respectively
`(z/|z|)^N |z|^{2t}`, and carry the published L-factors and epsilon
factors of the presented character.

At a finite place `v`, the completion `v.adicCompletion K` is realized
as a p-adic field by the published `CompletionPadic.padicField v` and
`CompletionPadic.topologicalData v`. Their carrier is the completion
itself, and the topology is the completion topology by `rfl`. The
local characters `ψv` are therefore stated with the type
`@UnitaryAdditiveCharacter (padicField v).Carrier _ (topologicalData v).topology`.
The published rank-one local factors are stated over this type:

- `PadicAbelian.lFactor (topologicalData v) η s` is
  `(1 - η(π) q_v^{-s})^{-1}` when `η` is unramified and `1` otherwise,
  Tate (3.1.3) applied to `η ω_s`. Here `π` is the published
  uniformizer and `q_v` the residue cardinality.
- `PadicAbelian.epsilon (topologicalData v) η ψv μ s` is the fixed-Haar
  rank-one constant `ε(η ω_s, ψv, μ)` in Deligne's normalization. It
  was checked against Tate (3.4.5) in the published module's
  documentation.

The local measure at a finite place ranges over the published subtype
`PadicAbelian.SelfDualHaar (topologicalData v) ψv` of Haar measures
self-dual for `ψv`. The epsilon factor reads its measure with the Borel
structure of the completion topology, as in the published
`langlandsConstantAtSelfDual`.

At the archimedean places the measure is the published scaled measure.
The real one is `realScaledMeasure c`, equal to `c • volume`, and the
complex one is `complexScaledMeasure c`, equal to `(2c) • volume`. The
scale is chosen self-dual for the local component of `ψ`:

- real place, `ψ_a(x) = exp(2πi a x)`: `c = |a|^{1/2}`, written
  `NNReal.sqrt ‖a‖₊`;
- complex place, `ψ_a(z) = exp(2πi Tr(a z))`: `c = ‖a‖`, written
  `‖a‖₊`.

These scales follow from the standard Fourier computation. Lebesgue
measure is self-dual for `exp(2πi x)`, and `2 dx dy` is self-dual for
`exp(2πi Tr z)`, by Tate (3.2.4)–(3.2.5). Replacing the character by
`x ↦ ψ(ax)` multiplies the Fourier transform by `|a|_v^{-1}` up to
dilation. The self-dual measure is therefore multiplied by
`|a|_v^{1/2}`, where `|a|_ℂ = ‖a‖²` is the normalized complex absolute
value. The scales are derived content, not quoted from the source.

The archimedean epsilon factor is the published
`RealCharacterData.epsilon d a c hc s`
(respectively `ComplexCharacterData.epsilon`): the epsilon of the
presented block twisted by `ω_s`, for `realScaledCharacter a` and the
scaled measure. Its formula follows Tate (3.2.2)–(3.2.5).

## The statement

`HeckeGlobalFunctionalEquationStatement` quantifies a universe-`u`
number field `K`, a Hecke character `χ`, and a nontrivial `ψ` trivial
on `K`. It asserts a conjunction of two parts.

**1. Existence of the local data.** At each finite place there is a
local component `ψv` of `ψ` with a self-dual Haar measure. At each real
or complex place there is a scalar `a` presenting the component of
`ψ`, and a presentation `d` of the local character of `χ`. This part
makes the second part non-vacuous: its universal quantifiers range over
inhabited families. The presentations of `χ⁻¹` required there exist by
the same conjunct for the Hecke character `χ⁻¹`, since the statement
quantifies over all Hecke characters.

**2. The functional equation for every choice of the data.** The
universally quantified data are:

- the finite components `ψf v`;
- self-dual measures `μ v`;
- the archimedean scalars `aR` and `aC`, indexed by the real places
  `{v // v.IsReal}` and the complex places `{v // v.IsComplex}`;
- presentations `dR`, `dC` of the archimedean components of `χ`, and
  `dR'`, `dC'` of those of `χ⁻¹`.

All of these data are unique when they exist. With the local
expressions

- `L_f(η, s)` the Euler product of `PadicAbelian.lFactor` over finite places;
- `D_∞(s) = ∏_{real} (dR v).lFactor.denominator s · ∏_{complex} (dC v).lFactor.denominator s`,
  and `D_∞'` the same with `dR'`, `dC'`;
- `ε_v(s) = PadicAbelian.epsilon (topologicalData v) (χ.finiteComponent v) (ψf v) (μ v) s`;
- `ε_∞(s)` the product of the archimedean epsilon factors with the
  self-dual scales above,

it asks for a real `σ`, functions `Λ`, `Λdual : ℂ → ℂ` and a finite set
`S` of finite places such that:

1. `Λ` and `Λdual` are meromorphic on all of `ℂ`;
2. for `Re s > σ` the Euler products converge unconditionally (`HasProd`):
   `L_f(χ, s) = Λ(s) · D_∞(s)` and `L_f(χ⁻¹, s) = Λdual(s) · D_∞'(s)`;
3. `ε_v(s) = 1` for every `v ∉ S` and every `s`;
4. `Λ(s) = (∏_{v ∈ S} ε_v(s)) · ε_∞(s) · Λdual(1 - s)` for `s` outside a
   discrete closed set (`Filter.codiscrete ℂ`).

The published archimedean L-factors are represented by entire
reciprocal denominators: `D_∞(s)` is the reciprocal of
`∏_{v | ∞} L(χ_v ω_s)`. Clause 2 thus says that `Λ` is Tate's complete
product (3.5.1) over all places in the half-plane, and `Λdual` is the
same for `χ⁻¹`. The dual `V*` of a character is its inverse. By
clause 3, the finite product in clause 4 is Tate's global epsilon
(3.5.2). Clause 4 is (3.5.4), `L(χ, s) = ε(χ, s) L(χ⁻¹, 1 - s)`.

Because `Λ` is determined on a right half-plane and is meromorphic,
the identity theorem determines it up to a discrete set. The same holds
for `Λdual`. The equality is therefore required off a discrete set
rather than at every point. This is the content of an identity of
meromorphic functions, and the totalized values at poles carry no
meaning. Clause 2 also forces `σ` past the zeros of the archimedean
denominators; the existential `σ` permits this.

## Provenance and reformulations

The source fixes a nontrivial character `ψ` of `A_F/F`. It takes the
Tamagawa measure `dx` on `A_F` and any factorization `dx = ∏ dx_v` in
which the integers have measure one for almost all `v`. It defines
`L(V, s)` and `ε(V, s)` by (3.5.1)–(3.5.2) and states the theorem:
convergence in a right half-plane, meromorphic continuation, and the
functional equation.

The target differs in the following derived respects:

- **Self-dual measures.** The target uses the self-dual factorization
  instead of an arbitrary one. Tate, Section 3.6, p.17, states that the
  product of the local self-dual measures is self-dual on `A`, and
  hence is the Tamagawa measure. In rank one the global epsilon depends
  only on the product measure, by (3.2.2), so this is a specialization
  of the source's choice. Self-dual measures exist and are unique at a
  finite place. Let `n(ψv)` be the largest integer `n` with `ψv`
  trivial on `P^{-n}`. Weil (1973), Chapter VII, §2, Corollary 3,
  p.108, shows that the self-dual measure gives the integers volume
  `q^{-n(ψv)/2}`. Weil's order of a character (Chapter II, §5,
  Definition 4 and Proposition 12, pp.41–42) is this `n(ψv)`. Hence
  `dx/dx_ψ = q^{n(ψ)/2} ∫_O dx` for a fixed Haar measure `dx`. Tate
  prints this ratio on p.17, immediately after (3.6.2), with the
  exponent `-n(ψ)/2`. That sign is a misprint, which we do not
  transcribe. The Library note `Langlands/LocalFactor/Harmonic/Statement.md`
  discusses the same misprint under "The scalar-measure discrepancy".
  Only the conductor-zero case is used here: when `n(ψv) = 0`, the
  self-dual measure gives the integers measure one, and `n(ψv) = 0`
  holds for almost all `v`. The separately
  published, unproved `LocalFactors.PadicFourierDualityStatement`
  (module `Langlands.LocalFactor.Harmonic.Statement`) includes
  existence and uniqueness of self-dual measures. Here the existence is
  instead an explicit conjunct of the target.
- **Local components exist.** Every local component of a nontrivial
  `ψ` trivial on `K` is nontrivial. If `ψ` were trivial on `K_v`, it
  would be trivial on `K + K_v`, which is dense in the adeles by strong
  approximation, so `ψ` would be trivial. Every nontrivial continuous
  character of `ℝ` or `ℂ` has the form `ψ_a` above with `a ≠ 0`, and
  every quasicharacter of `ℝˣ` or `ℂˣ` has one of the published polar
  forms. These standard facts are included in conjunct 1 as theorem
  obligations, not assumed.
- **Almost-everywhere triviality of `ε_v`.** The source asserts
  implicitly that the product (3.5.2) is finite. The target makes the
  finite set `S` explicit. The justification is (3.2.6.1): `ε_v = 1`
  when `χ_v` is unramified, `n(ψ_v) = 0`, and `O_v` has measure one.
  These hold for almost all `v`.
- **Separated archimedean factors.** The complete product over all
  places is written as the finite Euler product times the finitely many
  archimedean factors. This is the same function as (3.5.1) in the
  half-plane.
- **Chosen complex embeddings.** At a complex place, presenting both
  `ψ_v` and `χ_v` through the same Mathlib embedding makes the
  resulting epsilon independent of that choice, since the conjugate
  embedding changes both presentations compatibly: it replaces `a` by
  its conjugate and the weight `N` by `-N`, and the published epsilon
  formula is unchanged. The scalar `a` and data `d` are those of the
  chosen embedding.

Henniart (2000), Section 2.1, p.444, fixes exactly such a global
`ψ`, a nontrivial additive character of `A_F` trivial on `F`. Section
2.3, pp.444–445, uses the global functional equations for pair
L-functions. This target is the rank-one case; the pair case remains
separate work.

## Original sources

- John Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33,
  Part II (1979), 3–26. Printed page `p` is PDF page `p + 9`.
  Section 3.1, (3.1.1)–(3.1.3), printed pp.12–13 (local abelian L);
  Section 3.2, (3.2.1)–(3.2.6.1), printed p.13 (local functional
  equation, measure and character dependence, archimedean formulas,
  unramified epsilon); Section 3.4, (3.4.3)–(3.4.5), printed p.15;
  Section 3.5, (3.5.1)–(3.5.4) and Theorem 3.5.3, printed pp.15–16;
  Section 3.6, printed p.17 (self-dual local measures multiply to the
  Tamagawa measure; the ratio printed after (3.6.2) has a sign misprint
  in its exponent, see above). The retained original was read at these
  pages. Source `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- André Weil, *Basic Number Theory*, second edition, Springer (1973).
  Chapter II, §5, Definition 4 and Proposition 12, printed pp.41–42
  (PDF pp.58–59), for the order of an additive character and the dual
  lattice of `P^n`; Chapter VII, §2, Corollary 3, printed p.108 (PDF
  p.125), for the self-dual volume `mod(a)^{1/2}` of the integers when
  `ord(a)` is the order of the character. The retained original was
  read at these pages. Source `weil-1973-basic-number-theory`, SHA256
  `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
- Guy Henniart, *Une preuve simple des conjectures de Langlands pour
  GL(n) sur un corps p-adique* (2000), Section 2.1, p.444, for the
  fixed global additive character, and Section 2.3, pp.444–445. Source
  `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

## Dependencies and acceptance boundary

The module imports `Langlands.Global.HeckeCharacter`,
`Langlands.Global.CompletionPadic`, `Langlands.LocalFactor.Abelian.Padic`,
`Langlands.LocalFactor.ArchimedeanScaling` and Mathlib's
`Mathlib.Analysis.Meromorphic.Basic`. All project modules are
published at Library commit
`481ac9c36dcbe49e0ff1a50bb1855dc75a101e88`. The compiled sources are
byte-identical to the Library files:

| Module | Lean SHA256 |
| --- | --- |
| `Langlands.Global.Adelic` | `b1b7213c47725ac26e0ce09b0e483e548c8a4e1f3fd4a4972cedb64b7ce8258e` |
| `Langlands.Global.HeckeCharacter` | `68525fbd6a536afefdb696f83491c0ddd60d506390cf7dcb9682c7688c3de18f` |
| `Langlands.Global.CompletionPadic` | `00eff12c3044ba84174349120e6ce5a92395f59c3eccb84920f0285d931fcc14` |
| `Langlands.LocalFactor.Abelian.Padic` | `52c2257f1eb2963461a5bf98ee771680f8e2e9368a09328d349cac97ec34bb11` |
| `Langlands.LocalFactor.ArchimedeanAttachment` | `ee006f3c14b3e780c41242a53f60802b1ab494b6f64eee692f69d7d3820a7c7b` |
| `Langlands.LocalFactor.ArchimedeanScaling` | `e3ac3b37660c6198ff2134dc9a57dc28fd7b94a0a8d461f93ff819ac0afb5d8d` |
| `Langlands.HarmonicAnalysis.Basic` | `2198cecae146fa7f904dc2c01169d6321aee8e155c99614ed92f861fd2d65aff` |

The module compiled with no errors or warnings under Lean 4.34.0 and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, in the
project environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Inspection
of `HeckeGlobalFunctionalEquationStatement` reports a `Prop`-valued
definition with level parameter `u` and only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. The elaborated
statement was printed and keeps every hypothesis and clause above.

These development checks provide neither independent semantic
acceptance nor a proof of the functional equation.
