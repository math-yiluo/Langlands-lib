# Affine finite charts after an etale base change

This is an internal construction for the proof that a locally finite type monomorphism from an algebraic space to a scheme has a scheme source. It packages the local finite piece supplied by Mathlib's scheme Zariski Main Theorem, rather than asserting the algebraic-space representability theorem.

`EtaleFiniteChart f x` consists of affine schemes `D` and `T`, etale morphisms `D → X` and `T → Y`, a finite morphism `D → T`, their commuting square over `f : X → Y`, and a point of `D` mapping to `x`. Its map to `X ×_Y T` is etale: its composite with the etale projection to `X` is etale, so etale cancellation applies.

`nonempty_etaleFiniteChart` assumes that `f` is separated and locally of finite type, and is quasi-finite at `x`. Mathlib's `exists_etale_isCompl_of_quasiFiniteAt` supplies a finite clopen piece after an etale base change. Choose an affine neighborhood of the image of its marked point and pull back the finite piece to it. The new source is affine because it is finite over an affine scheme. Surjectivity of the map from scheme pullback points to the set theoretic pullback supplies the marked point. All etale and finite properties follow by base change and composition. The construction preserves the universe of `X` and `Y`.

Provenance: derived from the pinned Mathlib scheme theorem in `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean` and Mathlib's affine cover and pullback APIs. It is intended for the finite local charts used in Stacks Project Proposition 67.50.2 (Tag 03XX), retained under literature ID `stacks-mono-lft-schemehood-2026-11-02`. It does not yet assert representability of an algebraic-space image or any descent result.
