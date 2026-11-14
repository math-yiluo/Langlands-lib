# Lifting morphisms from smooth schemes to `Spec B`

Module `Langlands.GroupScheme.IntegralModel.Smoothening.Lift`. This is a helper
module of the proof of `Langlands.GroupScheme.IntegralModel.SmootheningStatement`.

Let `R` be a Henselian discrete valuation ring with algebraically closed residue
field and fraction field `K`. Let `A` be a commutative `R`-algebra and
`B = integralFunctions R K A`, with `incl : A → B` from the module
`IntegralFunctionsBasic`. The module proves the universal property of `Spec B`
for smooth schemes and smooth group schemes over `Spec R`. For group schemes this
is the factorization property of the smoothening, Lemma A.6.4 of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (literature ID
`kaletha-prasad-2023-bruhat-tits-new-approach`), without its closed-immersion
part. The source proves it for the dilatation tower of Construction A.6.1. The
argument here goes through the ring of integral functions instead and is internal
to this project. Every algebra map from `A` to the global functions of a smooth
scheme extends to `B`, by the divisibility result of the module `SmoothSections`.

## Instances

- `smooth_tensorUnit_hom`: the unit object `𝟙_` of the cartesian monoidal category
  of schemes over `Spec R` is smooth over `Spec R`. Its structure map is the
  identity (`Over.tensorUnit_hom`), an open immersion.
- `smooth_tensorObj_hom`: the product `X ⊗ Y` of two smooth schemes over `Spec R`
  is smooth. Its structure map is the composite of a base change of `Y.hom` with
  `X.hom` (`Over.tensorObj_hom`). Both are smooth.

## Algebra maps and morphisms

`algHomEquiv Y C` identifies `R`-algebra maps from `C` to the global functions of
`Y` with morphisms `(algΓ R).obj Y ⟶ op C` in the opposite category of
commutative `R`-algebras. It is a change of packaging, and both inverse laws hold
by `rfl`.

`specIncl R K A : Spec B ⟶ Spec A` is the morphism over `Spec R` given by
`algSpec` applied to `incl`.

## Bijectivity

`comp_incl_bijective Y`: for a smooth scheme `Y` over `Spec R` with global
function algebra `D`, the map `φ ↦ φ ∘ incl` from `R`-algebra maps `B → D` to
`R`-algebra maps `A → D` is bijective.

Proof. Injectivity is the uniqueness `algHom_ext_incl` of the module `Hopf`. For
surjectivity, let `ψ : A → D`. By the extension construction `extend` (module
`Saturation`) and `extend_comp_incl` it suffices to show the following. Whenever
`s ≠ 0` in `R` and `1 ⊗ a = s • b` for some `b ∈ B`, the element `ψ a` is
divisible by `s` in `D`. For every `R`-point `χ : D → R` of `Y`, the composite
`χ ∘ ψ` is an `R`-point of `Spec A`, so `s` divides `χ (ψ a)`
(`dvd_of_exists_smul_eq`). The module `SmoothSections`
(`exists_eq_smul_of_smooth`) then gives `ψ a = s • d` for some `d ∈ D`.

`bijective_comp_specIncl Y`: for a smooth scheme `Y` over `Spec R`, composition
with `specIncl R K A` is a bijection from morphisms `Y ⟶ Spec B` over `Spec R`
to morphisms `Y ⟶ Spec A` over `Spec R`.

Proof. The adjunction `algΓAlgSpecAdjunction R` (`algΓ R ⊣ algSpec R`), combined
with `algHomEquiv`, gives bijections `eB` from algebra maps `B → D` to morphisms
`Y ⟶ Spec B`, and `eA` likewise for `A`. Naturality of the adjunction bijection
(`homEquiv_naturality_right`) gives `eB φ ≫ specIncl = eA (φ ∘ incl)`. So the
composition map is `eA ∘ (· ∘ incl) ∘ eB⁻¹`, a composite of bijections by
`comp_incl_bijective`.

## Group schemes

Assume now that `A` is a commutative Hopf algebra over `R`. Then `B` carries the
Hopf algebra structure of the module `Hopf`, and `incl` is the bialgebra map
`inclBialgHom`.

- `specB R K A` is the group scheme `hopfSpec` of `B`, and `specA R A` the group
  scheme `hopfSpec` of `A`.
- `specInclHom R K A : specB R K A ⟶ specA R A` is the homomorphism `hopfSpec`
  applied to `inclBialgHom`. `specInclHom_hom_hom` records that its underlying
  morphism is `specIncl R K A` (by `rfl`).

`existsUnique_lift H f`: let `H` be a group scheme over `Spec R` whose underlying
scheme is smooth over `Spec R`, and `f : H ⟶ specA R A` a homomorphism. Then
there is exactly one homomorphism `f' : H ⟶ specB R K A` with
`f' ≫ specInclHom R K A = f`.

Proof. Write `ι` for the underlying morphism of `specInclHom`. By
`bijective_comp_specIncl` for `H.X` there is a unique morphism `g` of schemes over
`Spec R` with `g ≫ ι` equal to the underlying morphism of `f`. The morphism `g` is
a monoid morphism. The unit and multiplication axioms are equalities of morphisms
out of `𝟙_` and `H.X ⊗ H.X`. Both objects are smooth by the instances above, so
composition with `ι` is injective on morphisms out of them. After composing with
`ι`, both sides of each axiom agree because `ι` and `f` are monoid morphisms. So
`Grp.homMk g` is a homomorphism lifting `f`. Uniqueness follows from injectivity
of composition with `ι` on morphisms out of `H.X`.
