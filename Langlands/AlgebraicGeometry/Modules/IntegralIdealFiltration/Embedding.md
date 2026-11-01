# The pushforward of the ideal sheaf embeds into the module

Author: Worker 716. This is an internal helper module for
`Langlands.AlgebraicGeometry.Modules.coherentIntegralIdealFiltration`.

## The map

A section of `(Scheme.Modules.pushforward w.i).obj w.I` over an open `W` of `X` is an
admissible function on `i⁻¹ W`.

- `w.val a` is the underlying function and `val_mem` its admissibility.
- `val_add`, `val_zero`, `val_smul` and `val_res` record that addition, zero, scalar
  multiplication through `i.app W` and restriction are computed on underlying functions.
  All four hold by `rfl`.
- `inT_val`: the underlying function satisfies `InT W`.
- `w.phiApp W a` is a chosen killed extension of `a · s` over `W`. By `agrees_unique` it is
  the unique one (`phiApp_eq`).
- `w.phiPresheaf` is the morphism of abelian presheaves with components `phiApp`.
  Additivity and naturality follow from uniqueness, together with `Killed.add`,
  `Agrees.add`, `Killed.res` and `Agrees.res`.
- `w.phi : (Scheme.Modules.pushforward w.i).obj w.I ⟶ Q` is
  `PresheafOfModules.homMk w.phiPresheaf`; linearity follows from uniqueness with
  `Killed.smul` and `Agrees.smul`.

## Injectivity

`eq_zero_of_phiApp_eq_zero` assumes `Q` quasi-coherent and shows that `phiApp W a = 0`
forces `a = 0`.

- If `W` meets `Zc`, it contains the point `w.pt`, which lies in `U`. Take a basic open
  `D(g) ≤ W` of `U` containing the point. The zero extension agrees with `a`, so
  `r • s|_{D(g)} = 0` for a lift `r` of `a|`. By `mem_J_of_smul_eq_zero`, `r` lies in the
  kernel of `i.app`, so `a` restricts to `0` on `i⁻¹ D(g)`. This open is nonempty, since it
  contains a preimage of the point. Since `Z` is integral, restriction to a nonempty open
  is injective (Mathlib's `map_injective_of_isIntegral`), so `a = 0`.
- If `W` misses `Zc`, then `i⁻¹ W = ⊥` and the sections are trivial. This uses the Library's
  `ClosedImmersionHigherDirectImageVanishing.subsingleton_sections_of_eq_bot`.

Then `phiApp_sub` and this give `phiApp_injective`. The instance `Mono w.phi` follows by
`PresheafOfModules.mono_of_injective` and faithfulness of `SheafOfModules.forget`.

## Nonvanishing

`w.oneU` is the admissible function `1` over `i⁻¹ U` (`inT_one_U`). It is nonzero,
because `i⁻¹ U` is a nonempty open of the integral scheme `Z`, so its ring of sections is
a domain.

- `not_isZero_pushforward`: the pushforward `i_* I` is not zero.
- `not_isZero_I`: `I` is not zero, since `Scheme.Modules.pushforward` preserves zero
  objects.
