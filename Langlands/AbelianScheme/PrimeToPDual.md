# Duals, prime-to-`p` polarizations and the Rosati equation

The module `Langlands.AbelianScheme.PrimeToPDual` extends the Library's actual
dual abelian schemes and dual homomorphisms to the category of abelian
schemes up to prime-to-`p` isogeny (`Langlands.AbelianScheme.PrimeToP`), and
defines prime-to-`p` polarizations and the Rosati equation there. Its
declarations are in `Langlands.AbelianScheme.PolarizedFiniteLevel`, beside
the existing `Prerequisites` and `DualWitness`.

## Source

Kottwitz, *Points on some Shimura varieties over finite fields*, J. Amer.
Math. Soc. 5 (1992), source `kottwitz-1992-points-shimura-finite-fields`,
SHA-256 `c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
§5, printed p.390 (PDF p.18): `λ : A → Â` is a polarization, "a prime-to-`p`
isogeny from `A` to its dual abelian scheme, which at every geometric point
is a polarization", and `i` is a `*`-homomorphism for the involution on
`𝒪_B` and the Rosati involution defined by `λ`; isomorphisms carry `λ` into
a `ℤ_(p)^×`-multiple. §9, printed p.401 (PDF p.29): duality extends to the
category up to `R`-isogeny, `f^*(λ) = f̂ λ f`, and the Rosati involution is
`f ↦ λ⁻¹ f̂ λ`.

## The dual

The dual of `A` is the Library's actual dual `W.dual P`, for a
`DualWitness A` `W` and the named prerequisites `P : Prerequisites`, as in
`PolarizedFiniteLevel.Data`; `W.map P W' f` is the actual dual homomorphism.

* `DualWitness.additivity` proves `DualSchemeMapAdditivity` for any two dual
  witnesses, by the published theorem `dualSchemeMap_add` applied to the
  proved `picardZeroLineBundleClassification` and
  `smoothProperConnectedGlobalFunctions`. No additivity hypothesis is taken.
* `DualWitness.mapAddHom` is the published `dualAbelianSchemeMapAddHom`, the
  actual dualization as an additive map `(A ⟶ B) →+ (B^∨ ⟶ A^∨)`;
  `mapAddHom_apply` identifies it with `DualWitness.map`.
* `DualWitness.dualP P p WA WB : HomP p A B →ₗ[ℤ_(p)] HomP p B^∨ A^∨` is its
  `ℤ_(p)`-linear extension `r ⊗ f ↦ r ⊗ f^∨` (`dualP_tmul`,
  `dualP_homToHomP`), built with `CoefficientExtension.extendAddHom`. It
  preserves identities (`dualP_idP`, from `DualWitness.map_id`) and reverses
  composition (`dualP_compP`, from `DualWitness.map_comp`).
* `homPToHom0_dualP` proves that `dualP` agrees, after
  `homPToHom0`, with the existing rational dual `dualHom0`.

## Polarizations

`DualWitness.IsPrimeToPPolarization P p W λ`, for `λ : HomP p A W^∨`, holds
when

* `λ` is invertible in the localized category (`IsPrimeToPQuasiIsogeny p λ`,
  a `ℤ_(p)`-isogeny in the sense of §9), and
* there are a natural number `N` prime to `p` and an actual homomorphism
  `μ : A ⟶ W^∨` such that `μ` is an actual polarization
  (`W.IsPolarization P μ`, the Library's `AbelianScheme.IsPolarization`: an
  isogeny which at every geometric point has an ample Mumford
  presentation), `μ` is an actual prime-to-`p` isogeny (`IsPrimeToPIsogeny`,
  degree prime to `p` at every point of the base), and `N • λ = 1 ⊗ μ`.

Since `N` is a unit of `ℤ_(p)`, `λ = N⁻¹ μ`: the localized polarization is a
prime-to-`p` multiple of an actual polarization of prime-to-`p` degree, so no
isogeny of degree divisible by `p` is inverted by this convention. The
geometric-point condition of the source is part of `IsPolarization` for `μ`.

The localized category uses one global tensor product
`ℤ_(p) ⊗[ℤ] Hom_S(A, B)`, so an inverse of `μ` has one denominator prime to
`p` over the whole base. The degree condition on `μ`, imposed point by point,
need not supply such a uniform denominator when the base has infinitely many
connected components with growing prime-to-`p` degrees; this is why
invertibility of `λ` is a separate condition. It is what makes conjugation
by `λ` after dualization, `rosatiP`, defined on `EndP p A` (below).

* `IsPrimeToPPolarization.isPrimeToPQuasiIsogeny` extracts invertibility.
* `isPrimeToPPolarization_iff` restates the predicate with invertibility of
  the actual numerator `1 ⊗ μ` in place of that of `λ` (equivalent, since
  `N` is a unit; `isPrimeToPQuasiIsogeny_unit_smul_iff`).
* `isPrimeToPPolarization_homToHomP`: an actual polarization `μ` of
  prime-to-`p` degree with `1 ⊗ μ` invertible in the localized category is a
  prime-to-`p` polarization, with `N = 1`.
* `isPrimeToPPolarization_homToHomP_of_kernel`: the same conclusion when the
  scheme kernel of `μ` is killed by multiplication by one natural number `n`
  prime to `p`, by `isPrimeToPQuasiIsogeny_of_kernel` of
  `Langlands.AbelianScheme.PrimeToP`.

## Rosati equation, conjugation by `λ` and pullback

For a ring `O` with a map `τ : O → O` and an action `i : O →+* EndP p A`,
`DualWitness.RosatiCompatible P p τ W λ i` is the equation

```text
i(τ b) ≫ λ = λ ≫ i(b)^∨        for all b : O
```

in `HomP p A W^∨` (diagrammatic composition, `^∨ = dualP`).

For an invertible `λ` (`hλ : IsPrimeToPQuasiIsogeny p λ`),
`DualWitness.rosatiP P p W hλ f = λ ≫ f^∨ ≫ λ⁻¹`, in ordinary order
`λ⁻¹ ∘ f^∨ ∘ λ`, is conjugation by `λ` after dualization on `HomP p A A`;
`rosatiP_idP` and `rosatiP_compP` prove that it fixes the identity and
reverses composition. `rosatiCompatible_iff` proves that, for invertible
`λ`, the Rosati equation holds exactly when `i(τ b) = rosatiP (i b)` for
every `b`; `IsPrimeToPPolarization.rosatiCompatible_iff` is the same
statement for a prime-to-`p` polarization.

When `λ` is symmetric, i.e. equal to its dual under the canonical
identification of `A` with its double dual, the same formula is the Rosati
involution `f ↦ λ⁻¹ f^∨ λ` of §9, and the Rosati equation says that `i` is a
`*`-homomorphism for `τ` and that involution. For a general invertible `λ`
the map `rosatiP` need not be involutive. For example, let `E` be an
elliptic curve without complex multiplication and identify the dual of
`E × E` with `E × E` by the product principal polarization, so that
endomorphisms are `2 × 2` integer matrices and duality is transposition.
For `λ` corresponding to the automorphism `L = [[1,1],[0,1]]`, the map
`f ↦ L⁻¹ fᵗ L` sends `diag(1,0)` to `[[1,1],[0,0]]` and that to
`[[0,0],[1,1]]`.

`DualWitness.pullbackP P p WA WB e λ = e ≫ λ ≫ e^∨` is the pullback `e^*(λ)`
of §9. `pullbackP_idP`, `pullbackP_compP` (`(f ≫ g)^* = f^* ∘ g^*`) and
`pullbackP_smul` are its identity, functoriality and `ℤ_(p)`-linearity laws.

## Scope

The prerequisites `P` and the dual witnesses are inputs, as in the Library's
other polarized moduli data; this module proves no existence of duals and
no base-change compatibility of `dualP`. It does not compare the global
convention with a base-local localization of the Hom sheaf, it does not
prove that the degree of an isogeny kills its kernel, and it contains no
identification of the double dual and no symmetry condition on `λ`. Those
two inputs are what the involution law `rosatiP (rosatiP f) = f` needs, so
this module does not state that law.
