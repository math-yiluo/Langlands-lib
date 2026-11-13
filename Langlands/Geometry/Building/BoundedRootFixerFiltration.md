# A bounded root fixer is one filtration level

This is an internal consequence of the published apartment and root-filtration
definitions. It supplies a reduction needed in the root-model part of the
unramified parahoric construction. It does not construct an integral model or
prove the parahoric model statement.

Fix any field `k`, an affine group `G`, a monomorphic split-torus inclusion
`i : S → G`, and supplied `D : KPApartmentData i ω`. No local-field topology,
discreteness, completeness, or further building axioms are used.

For a relative root `a`, a reference point `x` of the apartment, and a nonempty
subset `Ω`, define the real threshold set

```text
{ -a(y - x) | y ∈ Ω }.
```

Here `a(y - x)` is the existing affine function
`D.affineFunctional a x 0 y`, defined using the root form on the apartment's
translation space. `D.rootFixerDepth a x Ω` is the real supremum of this set.
The definition is total; its mathematical threshold interpretation in the
theorems requires the stated nonemptiness and upper bound.

`rootFixer_eq_filtration_csSup` proves

```text
D.rootFixer a Ω = D.filtration x a (D.rootFixerDepth a x Ω).
```

Its hypotheses are that `Ω` is nonempty and that this threshold set is bounded
above. The reference point need not lie in `Ω`. The implemented proof applies
`filtration_vadd` to write each depth-zero group at `y` as the filtration at `x`
with level `-a(y - x)`. For any value in `WithTop ℝ`, being above all these
levels is equivalent to being above their supremum: for a real value this is
`csSup_le_iff`, and for the value `⊤` both sides hold. The explicit root-group
membership in `rootFixer` and `filtration` is retained in both directions.

`rootFixer_eq_filtration_of_bounded` obtains the threshold bound from the
hypothesis that every real affine function is bounded above on `Ω`, applied
to `-D.affineFunctional a x 0`. Thus it applies to the exact apartment
boundedness hypothesis of `UnramifiedParahoricModelStatement`.

This argument uses a supremum, so it does not require that any point of `Ω`
attain the extreme value. It also does not assert that the resulting affine
functional is an affine root, or that the fixer agrees with the fixer of a
finite subset. Those are different conclusions. The retained construction
obligation is to realize the actual single-level root filtration by a smooth
affine integral model with geometrically connected fibres and a compatible
map into the full model.
