# Composition of actual sheaf cohomology pushforward

This internal construction and its coherence proof concern the unchanged
`UnitSheafPushforward.cohomologyPushforwardEquiv`. They apply to arbitrary
topological spaces `X`, `Y`, `Z : TopCat.{u}`, isomorphisms `e : X ≅ Y` and
`f : Y ≅ Z`, an actual sheaf `F` of abelian groups in universe `u` on `X`,
and every degree `n : ℕ`. No compactness or scheme hypothesis is imposed.

Write `e_*`, `f_*`, and `(e ≪≫ f)_*` for the actual topological sheaf
pushforward functors, and write `C(e,F,n)` for the published additive
equivalence

```text
Hⁿ(Y,e_*F) ≃+ Hⁿ(X,F).
```

Here `H` is Mathlib's actual `CategoryTheory.Sheaf.H`, defined as Ext from
the constant abelian sheaf `ULift ℤ`, as in the imported implementation.
The topological pushforward definitions identify `f_*(e_*F)` with
`(e ≪≫ f)_*F` definitionally.

`cohomologyPushforwardCompositeEquiv e f F n` is the additive equivalence
obtained by applying `C(f,e_*F,n)` and then `C(e,F,n)`. The lemma
`cohomologyPushforwardEquiv_comp` proves the pointwise equation

```text
C(e,F,n) (C(f,e_*F,n) x) = C(e ≪≫ f,F,n) x
```

for every class `x` in `Hⁿ(Z,f_*(e_*F))`.
`cohomologyPushforwardCompositeEquiv_eq` packages this equation as equality
of additive equivalences.

The implemented proof is induction on `n`, generalized over `F`. In degree
zero, apply the injective global-section identification
`Sheaf.H.equiv₀ F isTerminalTop`. Three applications of the published
`cohomologyPushforwardEquiv_equiv₀` reduce the equation to a definitional
equality of global sections.

For the successor step, embed `F` into Mathlib's chosen injective object
`Injective.under F` and take the cokernel, obtaining the actual short exact
sequence

```text
0 → F → Injective.under F → cokernel (Injective.ι F) → 0.
```

The pushforward functors for `e` and `f` are equivalences, by the imported
`sheafPushforwardEquivalence`; hence they are exact and preserve injective
objects. The double pushforward of the middle sheaf is therefore injective
and has zero positive-degree cohomology. Mathlib's
`Sheaf.H.longSequence_exact₁` then expresses every class in
`Hⁿ⁺¹(Z,f_*(e_*F))` as a connecting image of a degree-`n` cokernel class.
The published `cohomologyPushforwardEquiv_δ` moves this connecting map
through the two successive comparisons. The induction hypothesis
identifies the resulting degree-`n` comparisons, and the same connecting
compatibility for `e ≪≫ f` finishes the proof.

The provenance is internal: the only inputs are the actual published
pushforward comparisons and their global-section and connecting-map
normalizations, together with Mathlib's enough injectives, preservation
of injectives under equivalences, vanishing for injective sheaves, and
the long exact cohomology sequence. This result supplies composition
coherence for those specific existing comparisons. It does not assert a
comparison of intrinsic Picard restriction maps, general scheme base
change, or representability of a Picard sheaf.
