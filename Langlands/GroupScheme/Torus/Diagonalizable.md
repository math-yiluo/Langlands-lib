# Diagonalizable group schemes of character groups

Author: Worker 228.

For a commutative ring `R : CommRingCat` and an additive commutative group `Λ` (both in
universe `u`), this module constructs the diagonalizable group scheme `D(Λ) = Spec R[Λ]` over
`Spec R` with the published `Corepresented` interface ([`Corepresented`](../Corepresented.md)).
For `Λ ≃ ℤ^I` it identifies `D(Λ)` with the published split torus `splitTorus (Spec R) I`
([`Split`](Split.md)). All declarations are in `Langlands.GroupScheme.Diagonalizable`.
No finiteness or freeness of `Λ` is assumed until the last section.

## The character functor

`commFunctor R Λ : CommAlgCat R ⥤ CommGrpCat` sends an algebra `B` to the group
`Multiplicative Λ →* Bˣ` of characters of `Λ` with values in `Bˣ`. An algebra map acts by
`Units.map`. `functor R Λ` is the same functor with values in `GrpCat`.

`algebra R Λ` is the group algebra `AddMonoidAlgebra R Λ`, written `R[Λ]`.
`monomialUnits` sends `γ` to the unit `single γ 1`. `lift R Λ χ : R[Λ] ⟶ B` is Mathlib's
`AddMonoidAlgebra.lift` applied to the values of `χ`. `lift_single` says it sends
`single γ r` to `r • χ(γ)`.

`corepresentation R Λ` corepresents `commFunctor R Λ` by `R[Λ]`. An algebra map `f` gives the
character `γ ↦ f(single γ 1)`, and `lift` is the inverse. Both inverse laws are checked on
monomials with `AddMonoidAlgebra.algHom_ext`. Every `R`-algebra map out of `R` is unique, so
that case is automatic. `grpCorepresentation R Λ` is the same corepresentation for the
group-valued functor.

`groupScheme R Λ := Corepresented.commGroupScheme (commFunctor R Λ) (corepresentation R Λ)`
is the commutative group scheme `D(Λ)`. By `CorepresentedPoints`, its points over any test
scheme `T` are the characters `Hom(Λ, Γ(T, 𝒪_T)ˣ)`. `groupScheme_toGrp` records that its
underlying group scheme is `Corepresented.groupScheme (functor R Λ) (grpCorepresentation R Λ)`
by definition.

## Comultiplication and antipode on monomials

These use the existing `Corepresented.LinearEmbedding.comul` and the `antipode` of
[`CorepresentedComultiplication`](../CorepresentedComultiplication.md).

* `comul_single`: the comultiplication sends `single γ r` to `single γ r ⊗ single γ 1`.
  The product of the two universal characters takes `γ` to
  `(single γ 1 ⊗ 1)(1 ⊗ single γ 1)`.
* `antipode_single`: the antipode sends `single γ r` to `single (-γ) r`.

## Restriction along a homomorphism of character groups

For `g : Λ' →+ Λ`:

* `restrict R g : functor R Λ ⟶ functor R Λ'` restricts characters along `g`.
* `incl R g : R[Λ'] ⟶ R[Λ]` is the algebra map with `incl_single : single γ r ↦ single (g γ) r`.
  `incl_apply` identifies it with `AddMonoidAlgebra.mapDomain g`. Hence `incl_injective`:
  it is injective when `g` is injective (`AddMonoidAlgebra.mapDomain_injective`).
* `homEquiv_symm_restrict`: the restricted character `χ ∘ g` is classified by
  `incl g ≫ lift χ`. `restrict_homEquiv` is the same statement in the opposite direction.
* `comul_incl`: `incl g` intertwines the comultiplications,
  `comul ≫ (incl g ⊗ incl g) = incl g ≫ comul`, where `incl g ⊗ incl g` is written as
  `tensorLift (incl g ≫ inl) (incl g ≫ inr)`. It is checked on monomials.

## Split tori

Let `I : Type u` be a finite type with decidable equality, and let `b : Λ ≃+ (I → ℤ)`.

* `charEquiv b M : (Multiplicative Λ →* M) ≃* (I → M)`, for a commutative group `M`, evaluates a
  character on the elements `b⁻¹(e_i)` corresponding to the standard basis vectors. The inverse
  sends `t` to the character `m ↦ ∏ i, t i ^ (b m) i`. For the left inverse law, each `m` is
  written as `∏ i, (b⁻¹ e_i)^((b m) i)` in `Multiplicative Λ`. For the right inverse law, only
  the factor `i = j` survives (`Finset.prod_eq_single`).
* `splitPointsEquiv R b T` identifies the points of `D(Λ)` over any test scheme `T` with
  `I → Γ(T, 𝒪_T)ˣ`. It composes `Corepresented.pointsEquiv` with `charEquiv`.
  `splitPointsEquiv_naturality` shows that restriction along `a : T' ⟶ T` acts by
  `splitTorus.unitsRestrict`. This follows from `Corepresented.pointsEquiv_naturality`.
* `splitIso R b : (groupScheme R Λ).toGrp ≅ splitTorus (Spec R) I` is the published
  `isoOfPointModels`. Its inputs are this point model and `splitTorus.pointsEquiv`.
* `isSplitTorus R b`: hence `D(Λ)` is a split torus in the sense of the published
  `IsSplitTorus`.

## Provenance

This is the standard construction of the diagonalizable group with character group `Λ` as
the spectrum of the group algebra. It is built from the published `Corepresented`,
`CorepresentedPoints` and `Torus/Split` modules and Mathlib's `AddMonoidAlgebra`, and it
introduces no claim from the literature. Its purpose is to supply split tori with explicit
coordinate algebras for the image theorem of
[`Rational/SplitTorusImage`](../Rational/SplitTorusImage.md).
