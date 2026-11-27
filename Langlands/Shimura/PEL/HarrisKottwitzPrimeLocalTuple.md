# Kottwitz's tuples `(A, λ, i)` up to prime-to-`p` isogeny for the Harris datum

The module `Langlands.Shimura.PEL.HarrisKottwitzPrimeLocalTuple` defines the
objects of Kottwitz's integral PEL moduli problem for the Harris datum,
before prime-to-`p` level structure, their isomorphisms up to prime-to-`p`
isogeny, and the comparison with the existing rational algebra actions.
The tuples are formed for a datum `Dat : HarrisKottwitzPrimeLocalDatum D C p`
(`Langlands.Shimura.PEL.HarrisKottwitzPrimeLocalDatum`), which includes
Kottwitz's hypothesis that `B_{ℚ_p}` is a product of matrix algebras over
finite unramified extensions of `ℚ_p`.

## Source

Kottwitz, *Points on some Shimura varieties over finite fields*, J. Amer.
Math. Soc. 5 (1992), §5, printed p.390 (PDF p.18), source
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`: for a
scheme `S` over `𝒪_E ⊗ ℤ_(p)`, the quadruples `(A, λ, i, η̄)` with `A` a
projective abelian scheme up to prime-to-`p` isogeny, `λ` a polarization
(a prime-to-`p` isogeny to the dual which is a polarization at every
geometric point), `i : 𝒪_B → End(A)` a `*`-homomorphism for the Rosati
involution, the determinant condition `g = f` on `Lie(A)`, and isomorphisms
given by prime-to-`p` isogenies commuting with `𝒪_B`, carrying `λ` into a
`ℤ_(p)^×`-multiple. This module treats `(A, λ, i)`; the level structure `η̄`
is not part of it.

## Bases and scalars

The test schemes are `S : Scheme.{0}` with a structure morphism
`s : S ⟶ Spec (PrimeLocalRingOfIntegers K p)`, over `𝒪_K ⊗ ℤ_(p)` after the
transport of the reflex field to `K` made in the datum. `baseScalars s` is
the composite `ℤ_(p) → 𝒪_K ⊗ ℤ_(p) → Γ(S, ⊤)` (any two ring maps out of
`ℤ_(p)` agree, `PrimeLocalIntegers.ringHom_ext`). `sectionDeterminant s W` maps
the integral determinant polynomial of the datum to `Γ(S, W)` with the
published structure-section map `secHom s W`.

## Projectivity

`AbelianScheme.IsLocallyHProjective A` requires, for every affine open `U` of
`S`, that the base change of `A` to `U` be H-projective over
`Γ(U, ⊤)` in the published sense `IsHProjective` (a closed immersion into a
finite projective space over the ring commuting with the structure maps).
The Library's `IsHProjective` is defined over affine bases; this is its
Zariski-local form.

## Tuples

`HarrisKottwitzPrimeLocalTuple Dat P s` has the fields

* `abelian : AbelianScheme S`, an actual abelian scheme, with `projective`
  (`IsLocallyHProjective`) and `dimension`, the published
  `HarrisTaylor.PrescribedRelativeDimension E abelian n`, i.e. relative
  dimension `[E : ℚ] n²`, the source's `dim V / 2` for `dim_ℚ V = [K : ℚ] n²`;
* `dualWitness : DualWitness abelian`, the actual dual, and
  `polarization : HomP p abelian (dualWitness.dual P)` with
  `isPolarization : dualWitness.IsPrimeToPPolarization P p polarization`
  (an isomorphism of the localized category that is a prime-to-`p` multiple
  of an actual polarization of prime-to-`p` degree, `PrimeToPDual`);
* `action : Dat.order →ₐ[ℤ_(p)] EndP p abelian`, an action of the order on
  the localized endomorphisms, whose values need not be actual
  endomorphisms;
* `rosati`, the Rosati equation `i(τ b) ≫ λ = λ ≫ i(b)^∨` for the positive
  left involution `τ` (`DualWitness.RosatiCompatible` with
  `Dat.orderInvolution`); since `λ` is invertible, this says that `i(τ b)`
  is the conjugate `λ⁻¹ ∘ i(b)^∨ ∘ λ` of `i(b)`
  (`IsPrimeToPPolarization.rosatiCompatible_iff`), which for the symmetric
  polarizations of the source is the Rosati involution;
* `determinant : Dat.DeterminantCondition s abelian action`.

`DeterminantCondition` states that on every finite free chart
`e : free I ≅ (Lie B)|_U` of the actual Lie module and every `V` over `U`,
the polynomial `liePSectionDeterminant` of the action on the order basis,
`det(X₁ i(α₁) + ⋯ + X_t i(α_t) ; Γ(V, Lie B))`, equals
`sectionDeterminant s V`. The Lie action is the one of `LiePrimeToP`: since
`S` lies over `ℤ_(p)`, the integers prime to `p` are units on `S` and a
localized endomorphism `r ⊗ φ` acts by `r • Lie(φ)`. The condition is the
full polynomial identity in the variables of an order basis, as in the
source, valid in every characteristic; no central trace condition is used.

## Comparison with the rational action

`rationalActionLinear` is the `ℚ`-linear map `A → End0 A` defined on the
basis `Dat.ratBasis` by `α_k ↦ endPToEnd0 (i α_k)`.
`rationalActionLinear_order` proves that it extends `endPToEnd0 ∘ i` on the
whole order (expanding in the basis and using `endPToEnd0_smul`), and
`rationalActionLinear_one`, `rationalActionLinear_mul` (checking products of
basis elements, which lie in the order) make it the `ℚ`-algebra
homomorphism `rationalAction`. `rationalAction_unique` proves that it is the
only `ℚ`-algebra homomorphism extending the order action, since the order
spans `A`. `toRationalAlgebraActionData` is the corresponding object of the
existing `RationalAlgebraActionData S A` of the characteristic-zero Harris
problem. Over a base whose global sections are a rational algebra, such as
a generic fibre, `liePOrderAction_eq_rational` identifies the Lie action of
the tuple with the published `lieRationalOrderAction` of `rationalAction` on
the order.

## Isomorphisms

`PrimeToPIso X Y` consists of an isomorphism `iso` of
`PrimeToPCategory p S` between the abelian schemes (a `ℤ_(p)`-isogeny),
`intertwines` (`i_X(b) ≫ iso = iso ≫ i_Y(b)`), a unit `scalar` of `ℤ_(p)`
and `polarization_eq`: `iso^*(λ_Y) = scalar • λ_X`, with the pullback
`DualWitness.pullbackP`. `PrimeToPIso.refl`, `PrimeToPIso.symm` (with the
inverse scalar, from `pullbackP_compP` and `pullbackP_smul`) and
`PrimeToPIso.trans` (with the product of scalars) show that
`PrimeToPIsomorphic` is an equivalence relation, `primeToPSetoid`, and
`PrimeToPClasses` is the set of isomorphism classes, in `Type 1`; no
smallness is asserted.

## Scope

Prerequisites `P` and dual witnesses are data as in the Library's polarized
moduli. No level structure, base-change functoriality of tuples,
representability, deformation theory or trace assertion is made or used.
Kottwitz restricts to locally noetherian `S`; the definitions here make sense
over every `S`.
