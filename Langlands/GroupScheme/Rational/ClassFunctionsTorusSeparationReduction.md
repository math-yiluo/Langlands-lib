# Torus separation from triangular character data

Worker 1800. Internal support for the proof of
`Langlands.GroupScheme.ClassFunctions.TorusSeparationStatement` (task
`0c854e73-f39c-45cf-9dda-31e34e1711f6`). It follows the proof of Corollary 6.6
in R. Steinberg, *Regular elements of semi-simple algebraic groups*, 1965
(source `steinberg-1965-regular-elements-semisimple-groups`, printed p.63).
There, regular class functions with equal values at two points `s t` of a
maximal torus `T` restrict to `W`-invariant regular functions on `T` with equal
values at `s` and `t`. Since such functions separate `W`-orbits, `t = w s` for
some `w ∈ W`. Points of `T` that are conjugate under `W` are conjugate in `G`
(Steinberg, Section 6, printed p.62, before Lemma 6.2).

This file proves the group-side part of that argument. It does not prove that
class functions supply the needed `W`-invariant functions (Chevalley
restriction, Steinberg Corollary 6.4). That input is a hypothesis of the final
theorem, in a triangular form. The orbit separation is
`Langlands.LinearAlgebra.DominantTriangular.exists_mem_reflectionGroup_of_triangular`
from `Langlands.LinearAlgebra.InvariantOrbitSeparation`. The Lean proofs are
original arguments; they are not transcribed from a text.

## Characters separate torus points

Namespace `Langlands.GroupScheme`.

- `IsSplitTorus.point_ext_characters`: for a split torus `T` over a base `S`,
  two points `x y : U ⟶ T.X` over any `U : Over S` are equal if
  `x ≫ χ = y ≫ χ` for every character `χ : characterLattice T`, where
  `χ` acts on points through `CommGroupScheme.groupHom χ`. Proof: transport a
  splitting `T ≅ 𝔾_m^I` to commutative group schemes. The identity of `T` is
  the sum over `c ∈ I` of the projection to the `c`-th factor followed by the
  inclusion of that factor (`splitTorus.sum_proj_comp_single`). On points this
  writes `z` as the product of the images of `z ≫ (eC.hom ≫ proj c)`, and
  these are characters of `T`.

## Character values at rational points

For a commutative ring `k` and a commutative group scheme `T` over `Spec k`:

- `characterValues s : Multiplicative (characterLattice T) →* k`, for a
  `k`-point `s`, sends `ofAdd ν` to the value at `s` of the rational character
  corresponding to `ν`. It is the published `rationalCharacterEval` composed
  with `(rationalCharacters.equivCharacterLattice T).symm` and the inclusion
  `kˣ → k`. `characterValues_apply` restates this definition.
  `characterValues_eq_affinePointsEquiv` gives the same value as
  `Gm.affinePointsEquiv` of `s ≫ χ`, by `rfl`.
- `characterValues_characterAut`: for an automorphism `σ` of `T`, the value at
  `s` of `characterAut σ ν` equals the value of `ν` at the point
  `s ≫ σ⁻¹`.
- `IsSplitTorus.eq_of_characterValues_eq`: two `k`-points of a split torus
  with equal `characterValues` are equal. This follows from
  `point_ext_characters` and injectivity of `Gm.affinePointsEquiv`.

In the notation of `InvariantOrbitSeparation`, `characterValues s` is the
point `φ : Multiplicative M →* k` for `M = characterLattice T`. The number
`evalChar (characterValues s) c` is the value at `s` of the regular function
`∑ ν, c ν · ν`.

## Reflections come from normalizing points

For a field `k`, a group scheme `G` over `Spec k` and `i : T ⟶ G`:

- `IsRootDatumOf.exists_isNormalizingPoint`: if `P` is a root datum of `i`
  (`IsRootDatumOf i P`), then every `w ∈ reflectionGroup P` is
  `characterAut σ` for some `k`-point `n` of `G` normalizing `i` through `σ`.
  Proof: closure induction. The generators are the reflections, which
  `IsRootDatumOf` provides together with normalizing points. The identity
  comes from `IsNormalizingPoint.one`, products from `IsNormalizingPoint.mul`
  (with the composite automorphism) and inverses from
  `IsNormalizingPoint.inv`.
- `IsNormalizingPoint.inv_mul_mul_eq`: if `n` normalizes `i` through `σ` and
  `t = s ≫ σ⁻¹`, then `n⁻¹ * i(s) * (n⁻¹)⁻¹ = i(t)` in `G(k)`. Proof: compose
  `IsNormalizingPoint.inv` with `s` and unfold conjugation on points
  (`comp_innerIso_hom`).

## Conjugacy from triangular data

- `SplitPinning.exists_conj_of_triangular`: let `p` be a split pinning of `G`
  and `s t` two `k`-points of its torus. Suppose that every dominant character
  `lam` (`p.IsDominantWeight lam`) admits `c : characterLattice p.torus →₀ k`
  with these properties: `c` is invariant under `reflectionGroup p.rootDatum`,
  `c lam = 1`, `lam - ν ∈ p.positiveRootMonoid` whenever `c ν ≠ 0`, and
  `evalChar (characterValues s) c = evalChar (characterValues t) c`. Then
  some `g ∈ G(k)` satisfies `g * i(s) * g⁻¹ = i(t)`, where `i` is
  `p.inclusion`. Proof: `exists_mem_reflectionGroup_of_triangular` with base
  `p.base` gives `w` in the reflection group with
  `characterValues t ν = characterValues s (w ν)`. Write `w = characterAut σ`
  for a normalizing point `n`. By `characterValues_characterAut` and point
  separation, `t = s ≫ σ⁻¹`, and `g = n⁻¹` works. Here `p.IsDominantWeight`
  and `p.positiveRootMonoid` agree by definition with `IsDominant` and
  `positiveCone` of `DominantTriangularInvariants`.

- `ClassFunctions.torusSeparation_of_triangular`: assume
  1. `hroot : RootDatumExistenceStatement.{u}`, the published statement that a
     connected reductive group with a split maximal torus has a finite
     reduced root datum (Milne Theorem 21.11, Corollary 21.12), and
  2. `htri`: for every algebraically closed field `k`, every `G` with
     `IsAffineHom G.X.hom`, every split pinning `p` of `G` and all `k`-points
     `s t` of `p.torus` with `(s ≫ i) ≫ rho G = (t ≫ i) ≫ rho G`, every
     dominant `lam` admits a `c` as in `exists_conj_of_triangular`.

  Then `TorusSeparationStatement.{u}` holds. Proof: a maximal torus over an
  algebraically closed field is split. This uses the published
  `SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites` with
  `CoalgebraDescent.separablyClosedGroupLikeSpanning`. `hroot` gives a root
  datum, and `SplitPinning.ofRootDatum` with the published `splitRootLieLine`
  builds a split pinning whose torus inclusion is the given `j`. Then
  `exists_conj_of_triangular` applies with the data from `htri`.

## Scope

Both hypotheses of `torusSeparation_of_triangular` remain open here.
`RootDatumExistenceStatement` is a separate task
(`972e4466-2aff-4fc0-a62e-1be346c899a0`). `htri` is to be supplied by the trace
characters of highest-weight representations restricted to the torus. Their
existence is `SplitDominantHighestWeightRepresentationsExistStatement` (task
`65df1467-7f2d-4446-b493-1dc93e8e54e0`). The triangularity and invariance of
their weight multiplicities are not proved in this file. The semisimplicity
hypothesis of `TorusSeparationStatement` is used only through
`IsSemisimple.isConnectedReductive`.
