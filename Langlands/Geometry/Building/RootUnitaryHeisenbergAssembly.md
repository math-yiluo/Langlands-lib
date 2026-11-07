# Quadratic unitary coordinates from a Heisenberg normal form with field data

This module constructs the published structure `RootUnitaryCoordinates i jZ s a`, the
quadratic unitary coordinates of a multipliable relative root `a` (Kaletha–Prasad (2.7.2),
§6.1). It starts from two inputs:

1. a Heisenberg normal form of `U_a` that is equivariant for the centralizer `Z` acting by
   conjugation (published `EquivariantHeisenbergNormalForm`, module
   `GroupScheme/Rational/RootHeisenbergEquivariant`);
2. rational field coordinates, collected in the new structure `HeisenbergUnitaryData`.

The proof combines these with the field algebra of the published
`GroupScheme/Examples/SU3RootHeisenbergComparison`. It is a reduction: the field data are
hypotheses, and this module does not construct them.

Provenance: internal. The target structure and its literature source are those of the
published `RootUnitaryCoordinateCompatibility`. The construction is a formal assembly of
published modules.

## Setting

All declarations live in namespace `Langlands.Geometry.Building`. Let `k` be a field and
`i : S.toGrp ⟶ G` a torus map. Let `jZ : Z ⟶ G`, and let `a` be a character of `S`. Let
`j : U ⟶ G` and `j₂ : U₂ ⟶ G` represent the root functors of `a` and `2 • a` (`hj`, `hj₂`).
`C : DoubleRootCommutatorPairing i a hj hj₂` is the published quotient datum: the quotient
`C.q : U ⟶ C.V` by `U₂` and the commutator pairing. The action of `Z` on `G` is
`AutomorphicAction.conjugation jZ`. The hypothesis `hfix` states that this action fixes every
point `t ≫ i` of the torus. `N` is an `EquivariantHeisenbergNormalForm` of `C` for this
action, and `s : S.toGrp ⟶ Z`. Rational points are sections over `Spec k`
(`rationalPoints`).

## Statements

- `commute_of_comp_q C g h hh`: if `h ≫ C.q = 1`, then the points `g` and `h` of `U` commute.
  So the points of `U₂` are central in `U`.
- `HeisenbergUnitaryData C N s`, a structure with the following fields.
  - Fields `base` and `extension`, with the same instance fields as `RootUnitaryCoordinates`:
    `extension / base` is separable quadratic, and `extension` is finite separable over `k`.
  - `first : Multiplicative extension ≃* rationalPoints C.V` and
    `second : Multiplicative (traceZero) ≃* rationalPoints U₂`, group isomorphisms. Here
    `traceZero` is the published additive group of trace-zero elements of `extension`.
  - `form : extension → extension → extension` and `cocycle_eq`: the cocycle of `N` at
    `first x` and `first y` has `second`-coordinate `form x y`.
  - `form_add`, `form_trace` and `form_nonsymm`. These say that `form` is additive in its
    second argument, satisfies
    `form (f x) y + form x (f y) = (f + σ f) form x y`, and is not symmetric.
  - `character` and `restriction`: a character of `Z_extension` restricting to `a`, as in
    `RootUnitaryCoordinates`. Let `c(z)` be its value on `z ∈ Z(k)`.
  - `first_act`: `z` acts on `first x` as `first (c(z) x)`, for the published
    `torusQuotientAction`. `second_act`: `z` acts on `second w` as `second w'` whenever
    `w' = c(z) σ(c(z)) w`.
- `form_traceZero`: `form` has trace-zero values.
- `coefficient`, `coefficient_ne_zero` and `form_eq`. The comparison module gives an `A` with
  `A + σ A ≠ 0` and `form = normalizedCocycle A`; `coefficient` is a chosen such `A`.
- `point w x = incl(second w) · sec(first x)`, a point of `U`.
  - `inclusion_comp_q`: `incl ≫ C.q = 1`, for any Heisenberg normal form.
  - `point_comp_q`: `point w x ≫ C.q = first x`.
  - `point_mul`: `point w x · point w' x' = point (w + w' + normalizedCocycle A x x') (x + x')`.
  - `point_injective`: `point` is injective.
  - `point_zero_comp`: `point w 0 ≫ j = second w ≫ j₂`.
- `heisenberg`: the published bijection `heisenbergEquiv` for `A = coefficient`.
  `heisenberg_zero`: it sends `(0, 0)` to `1`.
- `toPoints`: the group homomorphism from the quadratic root parameters to `U(k)`, sending
  `heisenberg (w, x)` to `point w x`. Its formula on `heisenberg (w, x)` is
  `toPoints_heisenberg`, and `toPoints_bijective` states that it is bijective.
- `equiv`: `toPoints` followed by the published `hj.pointsEquiv`, a group isomorphism onto
  `rootGroupPoints i a`. Its values in `G(k)` are `toPoints p ≫ j` (`equiv_coe`).
- `double`: a point of `G(k)` lies in `rootGroupPoints i (2 • a)` exactly when it is
  `equiv p` for a parameter `p` in `Parameters.central`.
- `scaleValue z` is `c(z)`. `scale_mem_traceZero`: `c σ(c) w` has trace zero.
- `conjugation`: `jZ(z) · equiv p · jZ(z)⁻¹ = equiv (Parameters.scale (c(z)) p)`.
- `rootUnitaryCoordinates`: the resulting `RootUnitaryCoordinates i jZ s a`. Its field
  extension, character and restriction are those of the data.

## Proofs

**Centrality.** By the published bilinearity of the commutator pairing, `pairing(x, 1) = 1`.
So if `h ≫ C.q = 1`, the commutator of `g ≫ j` and `h ≫ j` is trivial, and `g` and `h`
commute because `j` is a monomorphism.

**Group law.** `point w x · point w' x'` is computed using three facts: centrality of
`incl(second w')`, the law `sec(x) sec(x') = incl(β(x, x')) sec(x x')` of the normal form,
and `cocycle_eq` with `form_eq`. Under `heisenberg` this law is the parameter law (published
`heisenbergParameter_mul`), so `toPoints` is a homomorphism.

**Bijectivity.** Composing with `C.q` recovers `first x`. Cancelling `sec(first x)` and the
monomorphism `incl` then recovers `w`. Surjectivity is the published `exists_eq_mul_sec`.

**Double root group.** A parameter is central exactly when its first coordinate is `0`. The
point of `(w, 0)` is `incl(second w)`, whose image in `G` is `second w ≫ j₂`. The points of
`U₂` are exactly the points of `rootGroupPoints i (2 • a)` (`hj₂.pointsEquiv`).

**Conjugation.** Conjugation by `jZ(z)` on the image of `U` is the action of `z` on `U`
(published `rootActionOfFixesTorus_act_comp`). This action is computed by
`act_inclusion_torus` and `act_sec_torus` of the equivariant normal form and by `first_act`
and `second_act`. The published `heisenbergParameter_scale` identifies the result with
`Parameters.scale (c(z))`.

## Scope

The module proves no field data. In particular, it does not prove that `Z` is a torus, does
not construct the coordinates `first` and `second`, and does not prove trace compatibility
or non-symmetry of `form`.
