# Locally constant powers of a character on a scheme

Module `Langlands.AlgebraicGeometry.LocallyConstantUnitPower`, namespace
`Langlands.AlgebraicGeometry.LocallyConstantUnitPower`.

## Purpose and provenance

This is an internal helper for the canonical comparison between the
Cartier character presheaf of a diagonalizable group `D_S(M)` and the constant
presheaf with coefficients `M` (module
`Langlands.GroupScheme.Cartier.DiagonalizableConstant`, through
`Langlands.GroupScheme.Cartier.DiagonalizableGlue`). There, a locally constant function
`f : V → M` on an `S`-scheme `V` must be turned into a character. That needs one
unit of `Γ(V, ⊤)` that equals `t (ofAdd m)` on each clopen fibre `f ⁻¹' {m}`,
where `t : Multiplicative M →* Γ(V, ⊤)ˣ` is a group homomorphism. This module
builds that unit.

The mathematics is the sheaf (gluing) axiom for the structure sheaf `𝒪_X`,
applied to the open cover of `X` by the fibres of a locally constant function.
There is no single literature source to cite: this is standard sheaf theory used
as an auxiliary step. The record's provenance is therefore `internal`.

Throughout, `X Y : Scheme.{u}`, `Γ(X, ⊤)` is the ring of global sections, and
`X.presheaf.germ ⊤ x trivial : Γ(X, ⊤) → 𝒪_{X,x}` is the germ map at `x`.

## Gluing locally constant families of global sections

- `ext_germ`: global sections with the same germ at every point are equal.
- `exists_germ_eq (g : LocallyConstant X Γ(X, ⊤))`: there is a global section
  `s` whose germ at every `x` equals the germ of `g x`. Proof: each fibre
  `g ⁻¹' {r}` is open, and the restrictions of the sections `r` to these fibres
  agree on overlaps. On a nonempty overlap the two values of `r` coincide, since
  both equal `g x`. Mathlib's `existsUnique_gluing'` for `X.sheaf` therefore
  glues them. Comparing germs uses `germ_res_apply`.
- `glue g` is that section, chosen with `Classical.choose`. `germ_glue` gives its
  germs, and `eq_glue_iff` says `s = glue g` exactly when `s` has those germs.
  So `glue g` is uniquely determined, and the choice does not matter.
- `germ_appTop`: for `b : Y ⟶ X`, the germ of `b.appTop s` at `y` is the stalk
  map of `b` at `y` applied to the germ of `s` at `b y`. This is Mathlib's
  `Scheme.Hom.germ_stalkMap_apply`.
- `stalkMap_ι_injective`: for an open `U` of `X`, the stalk maps of the open
  immersion `U.ι` are injective. They are isomorphisms.
- `ext_of_cover`: global sections that agree after pullback to some open
  neighbourhood of every point are equal.
- `appTop_glue`: gluing commutes with pullback along `b : Y ⟶ X`, namely
  `b.appTop (glue g) = glue ((g.map b.appTop).comap b.base.hom)`.
- `glue_const`: gluing a constant family returns its value.

## Gluing units

- `glueUnits : LocallyConstant X Γ(X, ⊤)ˣ →* Γ(X, ⊤)ˣ` glues the values and
  the inverses separately. Both are checked to be inverse to each other on germs.
  The map is a monoid homomorphism, which is also checked on germs.
- `glueUnits_val`, `germ_glueUnits`, `eq_glueUnits_iff`, `glueUnits_const`:
  the underlying section, the germs, the germ characterization, and the constant
  case.
- `map_glueUnits`: naturality for pullback along `b : Y ⟶ X`, stated with
  `Units.map b.appTop.hom.toMonoidHom`.
- `eq_glueUnits_of_cover`: suppose that, for every `x`, some open neighbourhood
  `U` of `x` has `Units.map U.ι.appTop.hom.toMonoidHom u` equal to
  `Units.map U.ι.appTop.hom.toMonoidHom (g x)`. Then `u = glueUnits g`.
- `units_ext_of_cover`: units agreeing on an open neighbourhood of every point
  are equal.

## Locally constant powers

Let `M` be an additive commutative group, which need not be finitely generated.
Let `t : Multiplicative M →* Γ(X, ⊤)ˣ` and `f : LocallyConstant X M`.

- `lcPow t f := glueUnits (f.map fun m => t (Multiplicative.ofAdd m))`.
- `germ_lcPow`: the germ of `lcPow t f` at `x` is the germ of
  `t (ofAdd (f x))`.
- `eq_lcPow_iff`: `u = lcPow t f` exactly when, for every `x`, the germ of `u`
  at `x` is the germ of `t (ofAdd (f x))`.
- `eq_lcPow_of_cover`: the open-neighbourhood form of this characterization.
- `lcPow_const`: `lcPow t (const X m) = t (ofAdd m)`.
- `lcPow_add` and `lcPow_zero`: `lcPow t (f + g) = lcPow t f * lcPow t g` and
  `lcPow t 0 = 1`.
- `lcPow_mul` and `lcPow_one`: `lcPow (t * t') f = lcPow t f * lcPow t' f` and
  `lcPow 1 f = 1`.
- `lcPow_naturality`: for `b : Y ⟶ X`,
  `Units.map b.appTop.hom.toMonoidHom (lcPow t f)` equals
  `lcPow ((Units.map b.appTop.hom.toMonoidHom).comp t) (f.comap b.base.hom)`.
  The proof compares germs using `germ_appTop`.
- `map_ι_lcPow_of_eqOn`: if `f x = m` for every `x ∈ U`, where `U : X.Opens`,
  then `Units.map U.ι.appTop.hom.toMonoidHom (lcPow t f)` equals
  `Units.map U.ι.appTop.hom.toMonoidHom (t (ofAdd m))`. Proof: by
  `lcPow_naturality`, the pullback of `f` to `U` is constantly `m`, and
  `lcPow_const` finishes.

## Remarks

- Only Mathlib is imported: `Mathlib.AlgebraicGeometry.Restrict`,
  `Mathlib.Topology.LocallyConstant.Algebra`, and
  `Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`.
- There are no `sorry`s and no new axioms. The only noncomputable choice is in
  `glue`, and `eq_glue_iff` shows that the result does not depend on it.
