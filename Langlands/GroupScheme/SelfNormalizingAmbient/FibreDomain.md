# Fibres of smooth geometrically connected affine schemes are domains

The theorem
`Langlands.GroupScheme.SelfNormalizingAmbient.isDomain_tensor_of_smooth_geometricallyConnected`
concerns a commutative `R`-algebra `C` whose structure morphism `Spec C → Spec R` is
smooth and geometrically connected. It states that `K ⊗[R] C` is a domain for every field
`K` over `R`. In geometric terms, every fibre of a smooth affine scheme with geometrically
connected fibres is integral, including the fibre at a field point that is not a residue
field of `R`.

## Provenance

This module is internal supporting content for the task proving
`Langlands.GroupScheme.SelfNormalizingProperAmbientStatement`. There, `C` is the coordinate
ring of a smooth affine group scheme with connected fibres, and the theorem lets the field
fibres of that group be treated as domains. The statement is a standard fact: a smooth
scheme over a field that is geometrically connected is geometrically integral. The Lean
proof is new. It reduces the claim to the Library theorem
`Langlands.AbelianScheme.smoothGeometricIntegrality`, which proves
`Langlands.AbelianScheme.SmoothGeometricIntegrality` (the Stacks Project derivation is
described in that statement's Markdown). No outside source is ported here.

## Conventions

`R`, `C` and `K` all live in the same universe `u`. `R` and `C` are commutative rings, `C`
is an `R`-algebra, and `K` is a field with an `R`-algebra structure. The structure
morphism is `Spec.map (CommRingCat.ofHom (algebraMap R C))`. `Smooth` and
`GeometricallyConnected` are Mathlib's morphism properties of schemes. `IsDomain` is
Mathlib's class, so a domain is nontrivial.

## Declarations

### Export

`isDomain_tensor_of_smooth_geometricallyConnected hs hc K` takes
`hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R C)))`,
`hc : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap R C)))` and a field
`K` with `[Algebra R K]`, and states

```
IsDomain (K ⊗[R] C)
```

It lives in the namespace `Langlands.GroupScheme.SelfNormalizingAmbient` and imports
`Langlands.AbelianScheme.SmoothGeometricIntegralityProof` and
`Mathlib.AlgebraicGeometry.Geometrically.Integral`.

## Proof

Let `f = Spec.map (algebraMap R C)` and `g = Spec.map (algebraMap R K)`. The second
projection `pullback.snd f g` from `pullback f g` to `Spec K` is the base change of `f`
along `g`. Smoothness and geometric connectedness are stable under base change, and
Mathlib supplies both instances for `pullback.snd`. The Library theorem
`smoothGeometricIntegrality`, applied over the field `K`, then makes `pullback.snd f g`
geometrically integral.

The space of `Spec K` has a single point. So `GeometricallyIntegral.isIntegral_of_subsingleton`
shows that the source `pullback f g` is an integral scheme. The isomorphism
`pullbackSpecIso R C K` from `pullback f g` to `Spec (C ⊗[R] K)` transfers integrality
(`IsIntegral.of_isIso`). An affine scheme `Spec A` is integral exactly when `A` is a domain
(`affine_isIntegral_iff`), so `C ⊗[R] K` is a domain. Finally the algebra isomorphism
`Algebra.TensorProduct.comm R K C` identifies `K ⊗[R] C` with `C ⊗[R] K`, which gives the
export (`MulEquiv.isDomain`).
