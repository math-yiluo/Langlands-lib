# Relative closed-immersion descent along affine scheme limits

This derived statement supports the closed-immersion clause of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
printed pp. 5–6, Theorem 3.4(2). The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source uses finitely presented models. The present relative result
uses a finite-type, quasi-separated morphism and a target quasi-compact
over its affine base. It is a derived strengthening under these explicit
hypotheses, not a literal restatement of all of Theorem 3.4.

`RelativeClosedImmersionDescent` quantifies an actual small cofiltered
diagram `D` of affine Mathlib schemes, an affine base `S`, a compatible
natural transformation `t` to the constant base, and an actual limit
cone `c` with its limit witness. The supplied map `p : c.pt ⟶ S` agrees
with all cone projections followed by their structure maps. All sizes
share arbitrary universe `u`.

The models `X` and `Y` are arbitrary schemes; they need not be affine
or separated. Their structural maps are `a` and `b`. The morphism
`f : X ⟶ Y` satisfies `f ≫ b = a`, is locally of finite type,
quasi-compact and quasi-separated, and `b` is quasi-compact. The
proposition equates closed immersion of the actual limiting
`baseChangeMap a b f w p` with existence of a stage at which the
actual `baseChangeMap a b f w (t.app i)` is a closed immersion.
There is no injectivity assumption on coordinate-ring transitions.

The provenance is a finite affine-target-chart argument. For a chosen
chart of `Y`, the limiting closed immersion has affine source. Affineness
descends at some stage; restricting to the actual cofiltered category of
arrows to that stage retains the limit and makes all sources affine.
The actual affine-diagram closed-immersion detection statement then
provides a closed immersion at a stage. A common lower bound of the
finitely many chart stages gives a closed immersion by target locality.
The reverse implication follows from the actual Cartesian cone square
and stability under base change.

The paired Lean file defines the proposition only. Its proof, the
specialization to original filtered rings and all the other properties
in Theorem 3.4(2) are separate obligations.
