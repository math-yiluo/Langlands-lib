# Projective maps from homogeneous global coordinates

Author: Worker 148.

This internal module derives coordinate-substitution laws from the actual
`Proj.fromOfGlobalSections` construction. Let `R` and `B` be arbitrary
commutative rings in universe `u`, let `n` be a natural number, and put
`A = R[X_0, ..., X_n]` with its standard total-degree grading `𝒜` and
irrelevant homogeneous ideal `I`. The scheme `X` is arbitrary in universe `u`;
no affineness or reducedness is assumed.

For any ring homomorphism `f : A → B` and any `t : A`, `chartRingMap` is the
ring map from the degree-zero homogeneous localization `Away 𝒜 t` to
`B[(f(t))⁻¹]`. It includes the homogeneous localization into `A[t⁻¹]` and
then applies the localization map induced by `f`. This algebraic construction
does not require homogeneity, positive degree, or a projective-map hypothesis.
For any grading-preserving endomorphism `g` of `A`, `chartRingMap_comp` says
that evaluation after `g` on the chart `t` equals `Away.map g t` followed by
evaluation on the chart `g(t)`. Its proof evaluates homogeneous-fraction
representatives.

The geometric statements have additional premises.
`basicOpen_ι_fromOfGlobalSections` takes a ring homomorphism
`f : A → Γ(X, ⊤)` with the explicit witness `I.toIdeal.map f = ⊤`, a
strictly positive degree `d`, and a homogeneous element `t ∈ 𝒜 d`.
The unit-ideal witness ensures the glued map `X → Proj 𝒜` and its defining
cover exist. The positive-degree homogeneous element supplies the legitimate
projective chart. On `D(f(t))`, the theorem identifies this map with the
existing local chart map followed by the open immersion. It is the gluing
equation at that chart in the defining cover.

`fromOfGlobalSections_comp_gradedMap` takes a grading-preserving endomorphism
`g : 𝒜 →+*ᵍ 𝒜`, the explicit irrelevant-ideal bound `I ≤ I.map g`, and a
ring homomorphism `f : A → Γ(X, ⊤)`. Lean also takes both witnesses
`I.toIdeal.map f = ⊤` and `I.toIdeal.map (f.comp g.toRingHom) = ⊤`.
The irrelevant-ideal bound defines the actual morphism `Proj.map g`, while
the two unit-ideal witnesses define the two global-coordinate maps and the
cover used in the proof. Under these premises the theorem proves
`fromOfGlobalSections(f.comp g) = fromOfGlobalSections(f) ≫ Proj.map g`.
It restricts to the cover for `f.comp g`, applies the chart formula at `g(t)`,
and uses the induced-map chart formula and `chartRingMap_comp`.

These are derived localization and gluing identities, with provenance in the
imported constructions. This module alone does not prove a fixed-projective-
section/scalar-stabilizer comparison or quotient existence.
