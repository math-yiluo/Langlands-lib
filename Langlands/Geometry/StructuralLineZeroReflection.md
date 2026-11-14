# Reflection of zero for actual structural line sheaves

Worker 225. This is derived infrastructure for the Deligne construction in
Task 5556. It uses the existing actual structural-module pullback and scalar
endomorphisms from `DeligneStructuralBaseChange`, together with Mathlib's
canonical restriction and spectrum comparisons. It does not formalize a
separate assertion quoted from the original literature.

All declarations are in `Langlands.DeligneFormalSpace`. Schemes, residue
fields and their spectra use one universe `u`. The sheaves and morphisms are
actual `Scheme.Modules` objects and morphisms. `IsLineSheaf S M` is the
existing local triviality predicate: around every point of `S`, the
restriction of `M` is isomorphic to the actual structure module.

## Scalars on the structure module

`structuralUnitEndScalar e` evaluates an endomorphism `e` of the actual
structure module on its global section `1`. The theorem
`structuralUnitEnd_eq_scalar` proves that `e` equals
`structuralScalarEnd` for this global scalar. Its proof first uses naturality
to identify the value of `e` on `1` on any open with the restriction of its
global value. Linearity then determines its value on every section. The
module is the underlying ring on each open, so scalar multiplication here
is the ordinary product in that ring.

`structuralScalarEnd_naturality` states that every actual module-sheaf map
commutes with multiplication by a global scalar. It follows from linearity
on each open. `structuralScalarEnd_eq_zero_of_unitIso` says that a scalar
acting as the zero endomorphism on a sheaf globally isomorphic to the
structure module must itself be zero. The proof transports the action
through the isomorphism and evaluates on the global section `1`.

For any scheme morphism `f : S' ⟶ S`,
`structuralPullback_unit_map_eq_zero_iff` assumes only that the actual map
`f.appTop` on global structural sections is injective and proves that
`f* e = 0` if and only if `e = 0` for endomorphisms of the structure module
on `S`. The pullback action is the already constructed
`pullback_structuralScalarEnd`; `structuralPullbackUnitIso f` identifies
the pulled structure module with the structure module of `S'`. Thus the
argument reduces to injectivity of the scalar map. The reverse direction
uses preservation of zero by actual structural pullback.

## Line sheaves on a singleton scheme

`structuralTopRestrictionIso M` constructs the canonical comparison from
pullback of the restriction of `M` to the top open back to `M`. It composes
Mathlib's restriction/pullback comparison, pullback composition, the
identity relating the top-open inclusion to `S.topIso.inv`, and pullback
of the identity morphism.

If the underlying space of `S` is nonempty and a subsingleton,
`IsLineSheaf.nonempty_unitIso` shows that a locally trivial line sheaf is
globally isomorphic to the structure module. Any open neighbourhood of
the chosen point is the top open. A local trivialization on that open can
therefore be pulled back along `S.topIso.inv`; the preceding comparison
and the canonical structure-module comparison yield the global
isomorphism. The conclusion is existence (`Nonempty`) of an isomorphism,
without a preferred choice of frame.

`structuralPullback_line_map_eq_zero_iff` combines these facts. Assume that
`S` is nonempty and a subsingleton, that `f.appTop` is injective, and that
`M` and `N` are line sheaves on `S`. Then pullback along `f` preserves and
reflects zero for any actual morphism `g : M ⟶ N`. The proof chooses global
unit isomorphisms for `M` and `N` and conjugates `g` into an endomorphism
of the structure module. Functoriality transports its zero pullback;
the unit theorem detects zero, and cancellation of the isomorphisms
recovers `g = 0`. The source scheme `S'` has no singleton or line
triviality hypothesis.

## Field extension

For fields `K` and `L` and an arbitrary unital homomorphism
`r : CommRingCat.of K ⟶ CommRingCat.of L`,
`specField_appTop_injective` proves injectivity of the actual global
sections map of `Spec.map r`. The naturality of `Scheme.ΓSpecIso`
identifies this map, under the canonical global-sections isomorphisms,
with the injective field homomorphism `r`.

`specField_pullback_line_map_eq_zero_iff` specializes the singleton theorem
to the spectrum of `K`. For actual line sheaves `M` and `N` on `Spec K`
and an actual map `g : M ⟶ N`, it proves

```text
(Scheme.Modules.pullback (Spec.map r)).map g = 0 ↔ g = 0.
```

The singleton and nonemptiness instances for the spectrum of a field are
supplied by Mathlib. No separability, finiteness, local-field or
algebraic-closure hypothesis is imposed on `r`.

## Scope and intended use

These results do not assume faithfulness of structural pullback. The
line-map statement is restricted to a singleton base with an injective
global structural map; the field case discharges those hypotheses
unconditionally. This unit does not assert faithfulness on arbitrary
module sheaves or arbitrary schemes. It is intended to reflect vanishing
of the actual Deligne homogeneous fibre maps after extension of residue
fields. The resulting Pi-zero-locus equality and transport of Deligne
admissibility are separate successor results.
