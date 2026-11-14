# Finite-index closed subgroups and the identity component

The theorem
`Langlands.GroupScheme.ConnectedGeneration.componentRange_le_of_finiteIndex`
is an internal helper for the field step of KP Lemma A.4.26. Over an
algebraically closed field `k`, let `G` be smooth and let `j : H ⟶ G` be a
closed subgroup. If the image of `H(k)` has finite index in `G(k)`, then the
rational-point range of every relative identity-component representative
`i : N ⟶ G` is contained in that image. The helper has no affineness or
connectedness hypothesis on `H`, and no affineness hypothesis on `G`.

Its source motivation is Borel, *Linear Algebraic Groups*, second enlarged
edition (1991), Proposition 1.2(c), PDF pages 57–58 (the proof is on printed
page 47), source ID `borel-1991-linear-algebraic-groups-second`. Borel treats
algebraic groups as varieties and proves that a finite-index closed subgroup
contains the identity component by observing that it is open and closed.
The present scheme-theoretic helper is derived from the current Library and
Mathlib; it uses irreducibility directly after establishing a finite closed
cover. It concludes containment of rational points, which is the interface
needed by the field-generation proof.

The implemented proof first establishes private rational-point lifting and
translation lemmas. A rational point whose underlying point lies in a closed
immersion factors through it: the source is the reduced one-point scheme
`Spec k`, so the existing
`FiniteIndexTransfer.exists_lift_of_range_subset` applies. Left translation
is the regular action's `SchemeAction.translation`, with inverse supplied by
`SchemeAction.translationIso`. Consequently, a rational point `a` lies in
the translated closed image `xH` exactly when `x⁻¹ * a` belongs to the
rational-point range of `j`.

The finite coset quotient `G(k) / image(H(k))` supplies finitely many
representatives. Their translated scheme images are closed. They contain
every rational point and therefore every closed point, since `G` is locally
of finite type over an algebraically closed field. The Jacobson property and
density of closed points imply that these finitely many closed images cover
the entire underlying space of `G`.

The supplied relative identity-component representative is an open
immersion, so `N` is smooth. Smooth relative identity-component existence and
uniqueness transfer geometric connectedness to `N`; hence it is connected,
and the existing smooth-connected irreducibility theorem makes it
irreducible. Its image in the finite closed cover lies in one translated
image. The image contains the unit, so the rational representative of that
coset belongs to the subgroup. The translation criterion then puts every
rational point of `N` in the rational-point range of `j`.

All constructions and the theorem are polymorphic in the arbitrary universe
`u`. The file imports existing results without changing them.
