# Setup for points over a non-nilpotent prime

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusCaseA`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus`. This is a
supporting module of the proof of `ClosedOfGenericStatement`. It imports
`EtaleLocusGen`.

## Open sets where a germ vanishes (section `Germ`)

- `isOpen_germ_eq_zero`: for a section `s` of a scheme over an open `U`, the
  set of points of `U` where the germ of `s` vanishes is open. If the germ
  vanishes at `x`, then `s` vanishes on a neighbourhood of `x`
  (`RingedSpace.exists_res_eq_zero_of_germ_eq_zero`), so its germs vanish
  there too.
- `isOpen_structMap_eq_zero`: for `q : X ⟶ Spec D` and `d₀ ∈ D`, the set of
  `x` with `structMap q x d₀ = 0` is open. The value is the germ at `x` of
  the global section `q^*(d₀)` (`Scheme.Hom.germ_stalkMap_apply`).

## Comparing points of a level (namespace `LocalDatum`)

- `left_of_map_eq`: let `T` be over `Spec R` with structure morphism
  `t ≫ levelMap`, let `z ∈ F(T)`, and let `k : Spec L ⟶ T` with
  `k.left ≫ t = Spec δ` and `F(k)(z) = ζ`. Then the morphism attached to `z`,
  precomposed with `k.left`, is the point `mor` given by `ξ`. The proof is
  `elemEquiv_naturality'` followed by `left_eq_of_elemEquiv_eq`.
- `pt_eq_of`: if `Spec π ≫ h = mor` for a local `π : C → L`, then `h` sends
  the closed point of `Spec C` to `pt`.

## Levels `R'/I^{n+1}` (section `CaseA`)

Let `R'` be noetherian and `I` an ideal of `R'`. For a point `w` with
`I ⊆ P_w` (passed as an instance `Fact (I ≤ primeOf 𝔍 w)`):

- `Ln 𝔍 I n w = O_w/(𝔍 + I^{n+1})O_w`, a local ring;
- `nDatum R 𝔍 I n w` is the standard datum `Ln 𝔍 I n w` at `w` for the level
  `R' → R'/I^{n+1}`, an epimorphism, with `𝔞 = I^{n+1}`;
- `VanN 𝔍 I Lvs ξ n w` says that `𝔍` vanishes in the stalk at the point given
  by `nDatum` at level `n`, for chosen levels `Lvs n` for
  `R' → R'/I^{n+1}`.
