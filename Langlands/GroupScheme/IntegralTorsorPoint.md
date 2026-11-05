# Actual torsor points over complete rings with finite residue

The construction `integralTorsorPoint` chooses an actual `R`-valued point of
an actual fpqc torsor `X` under a smooth affine group scheme `H` over `R`.
The ring `R` is adically complete for a maximal ideal `I`, the quotient
`R / I` is finite, and the actual special fibre of `H` is connected.
The action is the existing categorical `ModObj`; the actual shear must be
invertible. Flatness, surjectivity and quasi-compactness of `X` over the base
are supplied. No affineness of `X`, preselected residue point, or preselected
integral point is assumed. All objects share an arbitrary universe.

First the scheme `X` is smooth over `R`. After pulling its structure map back
along itself, the invertible shear identifies this pullback map with the
second projection from `H × X`, which is smooth by base change from `H`.
Smoothness then descends along the given fpqc structure map of `X`.
This follows the existing locally-finite-type argument in
`FiniteFieldTorsorPoint.TorsorAction`, using Mathlib's smooth fpqc descent.

Pull back the actual group, scheme and action along the literal quotient
map `Spec (R / I) → Spec R`. `MonoidalActionMap` transports the action and
shows the actual shear remains invertible. Flatness, surjectivity,
quasi-compactness, group smoothness and group affineness are preserved by
this pullback. The published finite-field torsor point theorem supplies a
point on this actual special-fibre torsor. The canonical base-change point
equivalence identifies it with an `R / I`-valued point of the original `X`.
The smooth field-residue lifting theorem produces its actual `R`-valued
lift. Nonemptiness follows, and the final construction chooses a point.

This is a derived complete-ring implementation of the torsor point step in
Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Lemma B.2.4,
printed p.543 / PDF p.548. The registered October 2026 errata does not correct
this passage. The theorem retains the torsor and special-fibre hypotheses;
it does not construct a good arithmetic model, prove a proper quotient or
parabolic covering, establish integral maximality, or prove the global
integral Iwasawa family. It does not assert general Henselian lifting.
