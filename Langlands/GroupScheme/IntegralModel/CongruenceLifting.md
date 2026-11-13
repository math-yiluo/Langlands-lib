# Lifting congruence-level points of smooth groups over a Henselian ring

`Langlands.GroupScheme.IntegralModel.HenselianCongruenceLiftingStatement.{u}`
states Kaletha–Prasad Lemma 8.1.3 for smooth group schemes over a Henselian
local ring. It is a prerequisite for
`Langlands.GroupScheme.ConnectedGenerationStatement`. It is an unproved
proposition; this module proves nothing.

## Statement

Let `R` be a commutative ring in universe `u` with `[HenselianLocalRing R]`.
Let `Y` be a group scheme over `Spec R` whose structure morphism is smooth.
For every positive level `n : ℕ+`, the proposition asserts that the
homomorphism

`baseChangeSectionHom (congruenceBaseMap R n) Y : Y(R) → Y(R/𝔪ⁿ)`

is surjective. Here `congruenceBaseMap R n` is the spectrum map of the
actual quotient `R → R ⧸ (maximalIdeal R) ^ n`. The homomorphism restricts
an integral section of `Y` along that map and identifies the result with a
section of the base change of `Y` over `Spec (R ⧸ 𝔪ⁿ)`. It is the reduction
map used in `ConnectedGeneration.sectionCongruenceKernel` and in the target
statement. Its surjectivity says that every `R/𝔪ⁿ`-point of `Y` lifts to an
`R`-point.

`Y` need not be affine, separated or quasi-compact. No noetherian,
completeness or discrete valuation hypothesis is made on `R`.

## Source and provenance

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Lemma 8.1.3 and its proof, printed pp. 284–285 / PDF pp. 315–316:

> Let X be a smooth o-scheme. For any natural number n the canonical
> reduction map X(o) → X(o/mⁿ) is surjective.

In the source, `o` is the ring of integers of the book's Henselian
discretely valued field. The proposition makes two changes.

- **Group schemes only.** The Lean reduction homomorphism
  `baseChangeSectionHom` is defined for group schemes, and the target
  statement applies the lemma only to its group schemes `X` and `Y j`.
  So the proposition is the specialization of the source lemma to smooth
  group schemes.
- **Henselian local rings.** The source proof uses only the Henselian
  property of `o`, and the proposition states it for every Henselian local
  ring. The proof starts at a point `x₀ ∈ X(o/mⁿ)`. Since `Spec(o/mⁿ)` has
  one point, `x₀` factors through an affine open `U` that is étale over an
  affine space `𝔸ʳ_o` (EGA IV 17.11.4). The image of `x₀` in `𝔸ʳ` lifts
  coordinatewise to `y ∈ 𝔸ʳ(o)`. Then `x₀` factors through the étale
  `o`-scheme `f⁻¹(y)`. For an étale `o`-scheme over a Henselian local ring,
  EGA IV 18.5.12 gives bijections `Hom(Z, X) → Hom(Z_f, X_f)` for finite
  `Z`. Taking `Z = Spec o` and `Z = Spec(o/mⁿ)` gives the lift. No step uses
  the discrete valuation or noetherianity. The source cites EGA IV 18.5.12
  and 18.5.17 and BLR §2.3, Proposition 5 for `n = 1`.

The level is a positive natural number, as in the Library's congruence
tower. The source allows any natural number `n`, but `n = 0` is trivial.

The Library already proves the case `n = 1` for the group scheme of a smooth
`IntegralModel` over a Henselian local domain:
`Langlands.GroupScheme.IntegralModel.reduction_surjective`, in module
`Langlands.GroupScheme.IntegralModel.HenselianReduction`. Its étale input is
`Langlands.CommutativeAlgebra.HenselianSections.exists_lift_of_etale`.
