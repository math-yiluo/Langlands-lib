# Descent from scaled CM levels to small CM levels

## Purpose and provenance

Harris (1999), *Galois properties of cohomological automorphic forms on GL(n)*,
Sections 3-4, lets an element `g` of the finite-adelic group act on the
cohomology `H^d(S, W)` of the Shimura tower with coefficients in the systems
attached to `(ρ, W)` and a lattice `ℒ_W`. Since `g` need not preserve the
lattice, the integral coefficient systems are only carried into each other
after multiplying by a power `ℓ^e` of the coefficient prime. The Library
records this with scaled levels `CMScaledLevel D ρ p` (a small CM level with an
exponent; see [HarrisTaylorCMScaledLevels](HarrisTaylorCMScaledLevels.md)),
whose morphisms are transporters with an admissible exponent difference.

This file is the purely categorical step that removes the exponents once `ℓ`
is invertible. It is generic: it takes any presheaf `G` on scaled levels with
values in a `Λ`-linear category `C` over a field `Λ`, any family of objects
`O U` indexed by small CM levels, and any isomorphisms
`ψ X : G(X) ≅ O(X.level)`. It does not mention cohomology. It is intended to be
applied with `G` the `λ`-adic cohomology of the scaled coefficient diagram and
`O U` the Library's `λ`-adic cohomology at level `U`. The descended presheaf
then has the Library's objects as values, and the published tower and isotypic
constructions can be applied to it.

The file is derived. Its definitions are built from Library objects
(`exists_cmHarrisLatticeScaled`, `CMScaledLevel`, `CMScaledLevel.raise`,
`CMScaledLevel.Hom.shift`, `RestrictedLevelColimit.IsLevelTrivial`). Its
theorems are proved in Lean, and no statement from the literature is
transcribed. Harris's paper is cited only as the motivation for rescaling by
`ℓ^e`.

## Notation and hypotheses

The CM data are the section variables of
[HarrisTaylorCMScaledLevels](HarrisTaylorCMScaledLevels.md): the totally real
field `E`, the CM field `F`, the central simple algebra `A` with unitary data
`D : CentralSimpleUnitaryData E F A d`, a number field `K`, a finite-dimensional
`K`-vector space `W` with an algebraic representation `ρ`, and a finite place
`p` of `ℚ`. Write `ℓ = harrisCoefficientPrime p`. As in the Library,
`SmallCMLevel D` is the category of sufficiently small compact open levels,
with transporters `b : V ⟶ U` as morphisms.

In the section `Descent`:

* `C` is a category, later assumed `[Preadditive C] [Linear Λ C]` for a field
  `Λ`;
* `G : (CMScaledLevel D ρ p)ᵒᵖ ⥤ C`;
* `O : SmallCMLevel D → C`;
* `ψ : ∀ X : CMScaledLevel D ρ p, G.obj (op X) ≅ O X.level`.

## Least admissible exponents

* `cmHarrisLatticeExponent D ρ p b` is the least `e : ℕ` with
  `CMHarrisLatticeScaled D ρ p b e`, defined with `Nat.find` from
  `exists_cmHarrisLatticeScaled`. So `e` is the least exponent for which
  `x ↦ ℓ^e ρ(ι b) x` maps Harris's lattice of `U` into that of `V`.
* `cmHarrisLatticeScaled_exponent`: this exponent is admissible.
* `cmHarrisLatticeExponent_le`: it is at most every admissible exponent.
* `cmHarrisLatticeScaled_zero_of_mem`: for `b : U ⟶ U` with
  `b.hom.element ∈ U.obj.subgroup`, the exponent `0` is admissible. The proof
  uses the stability of Harris's lattice of `U` under the level
  (`harrisLattice_stable`).
* `cmScaledLevelLeast D ρ p b : ⟨V, 0⟩ ⟶ ⟨U, cmHarrisLatticeExponent D ρ p b⟩`
  is the morphism of scaled levels with transporter `b` and exponents `0` and
  `e_b`.

## Transport and its laws

* `cmScaledTransport D ρ p G O ψ f`, for `f : X ⟶ Y` in `CMScaledLevel D ρ p`,
  is `(ψ Y).inv ≫ G.map f.op ≫ (ψ X).hom : O Y.level ⟶ O X.level`. Below it is
  written `T(f)`.
* `cmScaledTransport_id`: `T(𝟙 X) = 𝟙`.
* `cmScaledTransport_comp`: `T(f ≫ g) = T(g) ≫ T(f)`.

The following are `Prop`-valued definitions, used as hypotheses:

* `CMScaledTransportRaise D ρ p Λ G O ψ`: for every level `U` and `n ≤ n'`,
  `T(CMScaledLevel.raise D ρ p U h) = (ℓ : Λ)^(n' - n) • 𝟙 (O U)`.
* `CMScaledTransportShift D ρ p G O ψ`: for every `f : X ⟶ Y` and `k`,
  `T(CMScaledLevel.Hom.shift D ρ p f k) = T(f)`.
* `CMScaledTransportLevelTrivial D ρ p G O ψ`: for every `Y` and every
  `f : Y ⟶ Y` whose transporter's element lies in `Y.level.obj.subgroup`,
  `T(f) = 𝟙`.

## The descended presheaf

* `cmScaledDescentMap D ρ p Λ G O ψ b`, for `b : V ⟶ U` in `SmallCMLevel D`, is
  `((ℓ : Λ)^(e_b))⁻¹ • T(cmScaledLevelLeast D ρ p b) : O U ⟶ O V`, where
  `e_b = cmHarrisLatticeExponent D ρ p b`.

The remaining results assume `hℓ : (ℓ : Λ) ≠ 0`,
`hraise : CMScaledTransportRaise D ρ p Λ G O ψ` and
`hshift : CMScaledTransportShift D ρ p G O ψ`. Here `Λ`, `G`, `O` and `ψ` are
implicit, determined by `hraise`.

* `cmScaledDescentMap_eq D ρ p hℓ hraise hshift b g hg`: for any morphism
  `g : ⟨V, n⟩ ⟶ ⟨U, n'⟩` of scaled levels with transporter `b` (`hg`),
  `cmScaledDescentMap ... b = ((ℓ : Λ)^(n' - n))⁻¹ • T(g)`. The proof factors
  `g` as the shift by `n` of `cmScaledLevelLeast b` followed by the raise from
  `n + e_b` to `n'`. Here `e_b ≤ n' - n` holds by minimality.
* `cmScaledDescentMap_id`: the map of `𝟙 U` is `𝟙`. Apply
  `cmScaledDescentMap_eq` with `g = 𝟙 ⟨U, 0⟩`.
* `cmScaledDescentMap_comp`: the map of `c ≫ b` is the map of `b` followed by
  the map of `c`. Apply `cmScaledDescentMap_eq` with `g` the composite of
  `cmScaledLevelLeast c` and the shift of `cmScaledLevelLeast b` by `e_c`, then
  use `hshift` and `pow_add`.
* `cmScaledDescent D ρ p hℓ hraise hshift : (SmallCMLevel D)ᵒᵖ ⥤ C` is the
  functor with `obj U = O U.unop` and `map b = cmScaledDescentMap ... b.unop`,
  with `@[simps!]` lemmas.
* `isLevelTrivial_cmScaledDescent D ρ p hℓ hraise hshift htriv`: if
  `htriv : CMScaledTransportLevelTrivial D ρ p G O ψ`, then `cmScaledDescent` is
  level-trivial in the sense of `RestrictedLevelColimit.IsLevelTrivial`: every
  self-arrow `restrictedSelfArrow _ U k hk` with `k ∈ U` acts by the identity.
  Apply `cmScaledDescentMap_eq` with the self-morphism of `⟨U, 0⟩` given by that
  arrow (admissible by `cmHarrisLatticeScaled_zero_of_mem`), then `htriv`.

## Use

For the `λ`-adic cohomology, take `C = Action (ModuleCat K_λ) Gal(F̄/F)`, which
is `K_λ`-linear, and `Λ = K_λ`, in which `ℓ` is a unit. Then
`cmScaledDescent` is a presheaf on small CM levels whose value at `U` is the
Library's cohomology at level `U`. With `isLevelTrivial_cmScaledDescent` it
satisfies the hypothesis of the tower constructions in
[HarrisTaylorCMSmallLevelGaloisTower](HarrisTaylorCMSmallLevelGaloisTower.md).
