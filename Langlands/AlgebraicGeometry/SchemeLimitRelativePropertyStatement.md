# Smoothness and flatness along affine scheme limits

This derived statement treats the smooth and flat clauses of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
printed pp. 5–6, Theorem 3.4(2). The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source concerns morphisms between finitely presented models over an
initial stage of a directed ring system. This interface instead assumes
finite presentation of the relative morphism and quasi-compactness of
its relative target over an affine base. It is a derived relative
strengthening under these explicit hypotheses. It does not assert the
remaining properties in the source's list.

`RelativePropertyDescent P` quantifies an actual small cofiltered
diagram `D` of affine Mathlib schemes, an affine base `S`, a natural
transformation `t` to the constant base, and a limit cone `c` with its
actual limit witness. The map `p : c.pt ⟶ S` agrees with the projections
followed by their structure maps. All sizes share arbitrary universe `u`.

The schemes `X` and `Y` are arbitrary. Their structural maps `a` and `b`
and the morphism `f : X ⟶ Y` obey `f ≫ b = a`. The morphism `f` is
locally of finite presentation, quasi-compact and quasi-separated; the
map `b` is quasi-compact. The proposition equates the property of the
actual limiting `baseChangeMap a b f w p` with its holding for an actual
`baseChangeMap a b f w (t.app i)` at some original stage. Neither model
is required to be affine or separated, and no coordinate-ring
transition is required to be injective.

`RelativeSmoothDescent` and `RelativeFlatDescent` substitute the actual
Mathlib scheme-morphism predicates `Smooth` and `Flat`. Their conjunction
is `RelativeSmoothFlatDescent`. The two clauses have independent
existential stages. The generic proposition supplies a common statement
shape and does not assert descent for arbitrary properties.

The intended proof uses a finite affine target cover. On each chart the
actual global-sections diagram has the actual filtered colimit of its
affine scheme limit. Structural descent for a prescribed model over a
stage of that ring diagram gives the property at a chart stage.
Cofilteredness gathers the finitely many stages; stability under base
change and locality at the target give the conclusion. The reverse
implication uses the actual Cartesian cone square.

The Lean file defines propositions only. Proofs and specialization to
prescribed original filtered-ring models are separate obligations.
