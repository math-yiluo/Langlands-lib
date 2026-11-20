# Gluing and restricting meromorphic functions in linear coordinates

Module `Langlands.Analysis.Meromorphic.CoordinateGluing` proves elementary
facts about the meromorphic functions of the Library modules
`Langlands.Analysis.Meromorphic.AnalyticSystems` (`IsHolomorphicOn`,
`IsMeromorphicOn` on a manifold modelled on `ℂᵐ`) and
`Langlands.Analysis.Meromorphic.LinearCoordinates`
(`IsMeromorphicInCoordinatesOn` on a finite-dimensional complex vector
space). They are used to turn the local, Fréchet-valued meromorphic
continuation of Eisenstein series into scalar functions with one domain of
holomorphy, and to modify these functions on the complement of an open dense
set.

Recall the definitions. `IsHolomorphicOn I f U` says that `μ ∘ f` is
manifold-differentiable on `U` for every continuous linear form `μ`.
`IsMeromorphicOn I f U` says that `U` is open and dense, `f` is holomorphic on
`U`, and every point `s₀` has an open connected neighbourhood `W` with a
holomorphic scalar `g` on `W`, not identically zero on `W`, and a holomorphic
`h` on `W` such that `g • f = h` on `U ∩ W`.
`IsMeromorphicInCoordinatesOn f U` says that the space is
finite-dimensional and that `f ∘ e` is meromorphic with domain `e⁻¹(U)` for
every complex linear isomorphism `e : ℂⁿ ≃ X`.

## Provenance

Internal to the Library. The notion of meromorphy is the one of
Bernstein–Lapid, J. Amer. Math. Soc. 37 (2024), §3.1, p.192 (registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`), as formalized in
the modules above. The facts proved here are elementary: invariance under
linear changes of coordinates, restriction to smaller domains, and gluing of
local data by the identity theorem for continuous functions on the closure of
a set (`Set.EqOn.of_subset_closure`). No literature statement is
reproduced.

## Declarations

### Flat space `ℂᵐ`

- `isHolomorphicOn_of_differentiableOn`, `differentiableOn_of_isHolomorphicOn`:
  for a scalar function on `ℂᵐ`, weak holomorphy on `U` is equivalent to
  complex differentiability on `U` (Mathlib's
  `mdifferentiableOn_iff_differentiableOn`; for the converse take `μ` the
  identity of `ℂ`).
- `IsMeromorphicOn.comp_continuousLinearEquiv`: if `f` is meromorphic on
  `ℂᵐ` with domain `U` and `T : ℂⁿ ≃ ℂᵐ` is a continuous linear isomorphism,
  then `f ∘ T` is meromorphic with domain `T⁻¹(U)`. Openness and density pull
  back along the homeomorphism `T`. The local data `(W, g, h)` at `T s₀` pull
  back to `(T⁻¹(W), g ∘ T, h ∘ T)`; `T⁻¹(W)` is connected as the image of `W`
  under the continuous map `T⁻¹`.
- `IsMeromorphicOn.congr_mono`: if `f'` is meromorphic with domain `U'`, `U`
  is open and dense, `U ⊆ U'`, and `f = f'` on `U`, then `f` is meromorphic
  with domain `U`. Holomorphy restricts to `U`, and the local quotient
  identities `g • f' = h` on `U' ∩ W` restrict to `U ∩ W`.

### Coordinates

- `IsOpenDenseInCoordinates U`: the preimage of `U` under every complex linear
  isomorphism `e : ℂⁿ ≃ X` is open and dense. A domain of holomorphy in
  coordinates has this property
  (`IsMeromorphicInCoordinatesOn.isOpenDenseInCoordinates`). The property is
  stable under finite intersections (`IsOpenDenseInCoordinates.inter`,
  `isOpenDenseInCoordinates_iInter`, using Mathlib's
  `dense_iInter_of_isOpen`) and under union with a set whose preimages under
  all such `e` are open (`IsOpenDenseInCoordinates.union_isOpen`).
- `isMeromorphicInCoordinatesOn_of_coordinates`: on a finite-dimensional `X`,
  meromorphy of `f ∘ e₀` with domain `e₀⁻¹(U)` for one linear isomorphism
  `e₀ : ℂᵐ ≃ X` gives `IsMeromorphicInCoordinatesOn f U`. For another `e`,
  `f ∘ e = (f ∘ e₀) ∘ T` with `T = e₀⁻¹ ∘ e`, a continuous linear isomorphism
  because the spaces are finite-dimensional; apply
  `IsMeromorphicOn.comp_continuousLinearEquiv`.
- `IsMeromorphicInCoordinatesOn.congr_mono`: the coordinate form of
  `IsMeromorphicOn.congr_mono`, with `U` open and dense in coordinates.
- `isMeromorphicInCoordinatesOn_univ`: on a finite-dimensional `X`, a scalar
  function `f` such that `f ∘ e` is differentiable on `ℂⁿ` for every linear
  isomorphism `e` is meromorphic in coordinates with domain all of `X`. The
  local data are `W = ℂⁿ`, `g = 1`, `h = f ∘ e`.

### Gluing

- `HasLocalMeromorphicData φ s₀`, for a family `φ i` of scalar functions on
  `ℂᵐ`: there are open sets `D` and `W` such that every `φ i` is
  differentiable on `D`, `W` is connected, `s₀ ∈ W ⊆ closure D`, and there is
  a scalar `q`, differentiable on `W` and not identically zero on `W`, such
  that for every `i` some `h` differentiable on `W` satisfies `q φ i = h` on
  `D ∩ W`. The denominator `q` and the sets `D`, `W` do not depend on `i`.
- `exists_isMeromorphicOn_of_local`: if the family has local meromorphic data
  at every point, there is one set `U` such that every `φ i` is meromorphic
  with domain `U`. Take `U` to be the set of points having an open
  neighbourhood on which every `φ i` is differentiable. It is open, every
  `φ i` is differentiable on it, and it contains every local `D`. It is dense
  because every `s₀` lies in some `W ⊆ closure D ⊆ closure U`. For the local
  quotient at `s₀`, use the local data at `s₀`. The identity `q φ i = h`
  holds on `D ∩ W` and both sides are continuous on `U ∩ W`, which lies in
  the closure of `D ∩ W` because `W` is open. So it holds on `U ∩ W`.

### Evaluation of a vector-valued meromorphic function

- `extendOpens W f`: extension by zero to `ℂᵐ` of a scalar function on an
  open subset `W ⊆ ℂᵐ`, viewed as a manifold (`TopologicalSpace.Opens`).
  `differentiableAt_extendOpens` and `differentiableOn_extendOpens` say that
  manifold differentiability on an open part of `W` gives complex
  differentiability of the extension there (Mathlib's
  `liftPropAt_iff_comp_subtype_val` for the local invariant property of
  differentiability).
- `hasLocalMeromorphicData_of_isMeromorphicOn`: let `f : W → V` be meromorphic
  on the open submanifold `W ⊆ ℂᵐ` with domain `D`, with values in a
  topological complex vector space `V`. Let `ev i : V →L[ℂ] ℂ` be continuous
  linear forms, and let `φ i` be scalar functions on `ℂᵐ` with
  `φ i t = ev i (f t)` for `t ∈ D`. Then the family `φ` has local
  meromorphic data at every point of `W`. The data are the images in `ℂᵐ` of
  `D` and of the neighbourhood `W'` of the local quotient of `f`, the
  extended denominator `g`, and the extended numerators `ev i ∘ h`. These are
  differentiable because `f` is weakly holomorphic and `ev i` is continuous
  linear.
