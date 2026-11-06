# Descent of local group isomorphisms with a trivial discrepancy cocycle

Fix an arbitrary universe, a scheme `S`, actual group schemes `G` and `H`
over `S`, and a relative scheme `U`. `LocalGroupHom G H U` consists of
homomorphisms `G(Z) → H(Z)` for every `Z : Over S` and every `a : Z ⟶ U`,
commuting with all morphisms of test schemes. `LocalGroupIso` uses
multiplicative equivalences in place of homomorphisms. Thus these data concern
actual scheme-valued points on all tests.

`IsIndependent` requires the local maps at any two points of `U` to agree
on every test. The `symm` operation on local isomorphisms preserves
naturality, and independence passes to the inverse family.

For an fpqc structural morphism `U.hom` (quasi-compact, flat and surjective),
`LocalGroupHom.value` descends a local value at `g : Z ⟶ G.X` through
the effective epimorphism `Z ×_S U → Z`. Naturality and independence imply
agreement on every pair identified by this projection. The implementation
first converts that relation into one for all underlying scheme morphisms,
uses `EffectiveEpi.desc`, and recovers the map over `S` by epimorphic
cancellation. `value_fac` records the pullback equation, and `comp_value`
recovers the local value after any test morphism supplied with a cover point.

Cancellation after the same projection proves that descended values are
natural and preserve the identity and multiplication. The existing
`homOfPoints` constructor in `Multiplicative` produces an actual
group-scheme homomorphism `LocalGroupHom.descend`; `comp_descend` gives
its action on points. Descending the inverse local family and checking the
inverse identities after the projection proves `LocalGroupIso.descend :
G ≅ H` for an independent family.

Now let another actual group scheme `A` act on `G` through an
`AutomorphicAction A G`, and let `ξ : Cocycle A U`. The proposition
`e.HasDiscrepancy a ξ` is the all-test equation

```
e_b(a.act(ξ(b,c),g)) = e_c(g).
```

For a cochain `f : U ⟶ A.X`, `e.twist a f` precomposes `e_b` by the
point automorphism given by `f(b)`. Its naturality follows from naturality
of the original family and of the actual action morphism. If
`ξ(b,c) = f(b) * f(c)⁻¹`, substituting `a.act(f(c),g)` in the discrepancy
equation and applying the action laws proves `twist_isIndependent`.
Consequently `descendOfTrivial` chooses a cochain witnessing
`ξ.IsTrivial` and descends the corrected family to an actual isomorphism
`G ≅ H`. The original cocycle convention is retained throughout.

This is an internal construction from effective epimorphic descent,
the published pointwise Yoneda constructors, and the action and cocycle laws.
It does not assume or prove existence of a local family, a discrepancy
cocycle, a quasi-split inner form, a torus reduction, or a trivializing
cochain. Those are explicit inputs to this helper and remain substantive
obligations in the Steinberg proof. No field, characteristic, perfectness,
smoothness, reductivity, or supplied Borel is used in this generic descent.
