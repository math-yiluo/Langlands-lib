# Abelian schemes up to prime-to-`p` isogeny

For a prime `p` and a scheme `S`, the module `Langlands.AbelianScheme.PrimeToP`
constructs the category of the Library's actual abelian schemes over `S`
(`Langlands.AbelianScheme S`, with their actual homomorphisms of commutative
group schemes) **up to prime-to-`p` isogeny**: the coefficient extension of
`Langlands.CategoryTheory.CoefficientExtension` with coefficients in
`ℤ_(p) = PrimeLocalIntegers p`.

## Source

Kottwitz, *Points on some Shimura varieties over finite fields*, J. Amer.
Math. Soc. 5 (1992), source `kottwitz-1992-points-shimura-finite-fields`,
SHA-256 `c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
§5, printed p.390 (PDF p.18), considers projective abelian schemes "up to
prime-to-`p` isogeny" with `i : 𝒪_B → End(A)` a homomorphism into the
`ℤ_(p)`-algebra `End(A)`, and isomorphisms of quadruples given by
prime-to-`p` isogenies. §9, printed p.401 (PDF p.29), defines the category
up to `R`-isogeny by Hom groups `Hom(A, B) ⊗ R` and an `R`-isogeny as an
isomorphism there. This module is that definition for `R = ℤ_(p)` over an
arbitrary base scheme, with the actual relative Hom groups of
`AbelianScheme S`.

## The localized category

* `PrimeToPCategory p S` is `CoefficientExtension (PrimeLocalIntegers p)
  (AbelianScheme S)`. `HomP p A B = ℤ_(p) ⊗[ℤ] Hom_S(A, B)` and `EndP p A`
  is the endomorphism `ℤ_(p)`-algebra of `A` there, with multiplication
  `a * b = b ≫ a` (`endP_mul`) and scalars `r ⊗ 𝟙 A` (`endP_algebraMap`).
  Elements of `EndP p A` are endomorphisms with denominators prime to `p`;
  they need not be actual endomorphisms.
* `homToHomP`, `f ↦ 1 ⊗ f`, `idP`, and the `ℤ_(p)`-bilinear composition
  `compP` in diagrammatic order (`compP_tmul`), with the unit, associativity
  and compatibility laws (`compP_homToHomP`, `idP_compP`, `compP_idP`,
  `compP_assoc`). `endToEndP` is the unital ring map from actual
  endomorphisms.

The coefficients invert exactly the integers prime to `p`
(`PrimeLocalIntegers.mem_primeCompl_iff`). Mathematically every element of
`HomP p A B` is then an actual homomorphism divided by a natural number prime
to `p`; this module does not formalize that description, and it makes no
assertion that a particular isogeny of degree divisible by `p` fails to be
invertible.

## Comparison with the rationalized category

The existing `RationalCategory S` (`Langlands.AbelianScheme.Rational`, with
Hom groups `Hom0 A B = ℚ ⊗[ℤ] Hom_S(A, B)`) is used only as a comparison.
`primeToPRationalization p S` is the additive functor along
`PrimeLocalIntegers.toRat p : ℤ_(p) → ℚ`, and `homPToHom0` its map on Hom
groups, `r ⊗ f ↦ r ⊗ f` (`homPToHom0_tmul`, `homPToHom0_homToHomP`). It is
semilinear (`homPToHom0_smul`) and preserves identities and composition
(`homPToHom0_idP`, `homPToHom0_compP`). `endPToEnd0` is the unital ring map
`EndP p A → End0 A`, compatible with `endToEnd0` and with scalars
(`endPToEnd0_endToEndP`, `endPToEnd0_algebraMap`).

## Base change

`primeToPBaseChange p b`, for `b : T ⟶ S`, is the extension of the actual
pullback functor `AbelianScheme.baseChange b` (whose additivity is the
published `baseChange_additive`) by `CoefficientExtension.lift`.
`baseChangeHomP p b` is its `ℤ_(p)`-linear map on Hom groups,
`r ⊗ f ↦ r ⊗ b^* f` (`baseChangeHomP_tmul`), preserving identities and
composition (`baseChangeHomP_idP`, `baseChangeHomP_compP`);
`baseChangeEndP` is the induced unital `ℤ_(p)`-algebra map on `EndP`.
`homPToHom0_baseChangeHomP` proves compatibility with the existing rational
base change `rationalBaseChangeHom`.

## Isogenies

* `IsPrimeToPIsogeny p f`, for an actual homomorphism `f : A ⟶ B`, means that
  `f` is an isogeny in the Library's sense (`GroupScheme.IsIsogeny`: finite,
  flat and surjective) and that the native finite flat degree
  `(hom f).finrank y` is prime to `p` at every point `y` of the target. For a
  finite flat morphism this rank is the degree of the fibre at `y`, so this
  is Kottwitz's condition that the degree is prime to `p` on every geometric
  fibre, imposed at every point of `B`.
* `IsPrimeToPQuasiIsogeny p f`, for `f : HomP p A B`, means that `f` is an
  isomorphism of `PrimeToPCategory p S`: a `ℤ_(p)`-isogeny in the sense of
  §9. `IsPrimeToPQuasiIsogeny.rational` proves that its image in the rational
  category is invertible. `IsPrimeToPQuasiIsogeny.invP` is the inverse as a
  localized homomorphism, with `compP_invP` and `invP_compP`; `of_compP`
  recognizes a `ℤ_(p)`-isogeny from a two-sided inverse, and
  `isPrimeToPQuasiIsogeny_unit_smul_iff` (with `IsPrimeToPQuasiIsogeny.unit_smul`)
  proves that multiplying by a unit of `ℤ_(p)` does not change invertibility.
* `isPrimeToPQuasiIsogeny_of_kernel`: an actual isogeny `f` whose scheme
  kernel is killed by multiplication by a natural number `n` prime to `p`
  becomes a `ℤ_(p)`-isogeny. The inverse is `n⁻¹ • g`, where `g` is the
  published `GroupScheme.descent` of multiplication by `n` along `f`, with
  `f ≫ g = n` and `g ≫ f = n` (`comp_descent`, `descent_comp`). The proof is
  the `ℤ_(p)`-analogue of the published `isogenyInverse`. The module does not
  prove that the degree of an isogeny annihilates its kernel, so it does not
  derive this hypothesis from `IsPrimeToPIsogeny`.

## Scope

The base scheme is arbitrary. No faithfulness of `homToHomP`, torsion-freeness
of Hom groups, or representability is asserted.
