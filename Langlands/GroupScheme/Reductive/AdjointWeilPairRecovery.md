# Adjointness recovered from local finite-base comparisons

Worker 632.

This internal helper supplies the adjointness part of the final descent
assembly. Its motivating source is Brian Conrad, *Reductive group
schemes* (2014), the proof of Proposition 6.4.4 and Remark 6.4.5,
pp.232–233, registered as `conrad-2014-reductive-group-schemes`.

Let the spectra of a family of `A`-algebras `R i` cover `Spec A`.
Let `B` be any `A`-algebra and let `e i : R i ⊗_A B ≃ D i` be
isomorphisms of `R i`-algebras. `AffineWeilPairRecovery.map` is the
actual spectrum map of `b ↦ e i (1 ⊗ b)`, from `Spec(D i)` to
`Spec B`. The theorem `map_eq` verifies this composite formula.

The theorem `covers` proves that these maps cover `Spec B`. Given a
point of `Spec B`, choose a point of some `Spec(R i)` above its image.
The existence of a point in their scheme-theoretic fibre product,
the spectrum/tensor-product isomorphism and the original `e i` then
give a point of `Spec(D i)` above it. No étaleness, flatness,
finiteness, projectivity or nonzero-ring assumptions are needed for
this covering argument.

The pointwise geometric-fibre lemma first proves reflection of
adjointness from a specified point of any base change. It uses the
actual composition isomorphism and the established field-valued
adjointness comparison. Applying this lemma above each point of
`Spec B` proves `AffineWeilPairRecovery.isFibrewiseAdjoint`: adjoint
geometric fibres of the recovered groups imply adjoint geometric
fibres of the original group over `B`.

This is an internal composition of scheme fibre-product geometry and
the Library's adjoint field-extension reflection. It assumes the
supplied local group recovery isomorphisms, and neither constructs
descent data nor proves effectivity or uniqueness of Weil pairs.
All rings, schemes and indices lie in the arbitrary universe `u`.
