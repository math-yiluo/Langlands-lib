# Normalized induction preserves Hermitian representations

`Langlands.Renard.CompactRepresentation.NormalizedInductionPreservesHermitianStatement`
states the preservation assertion in Renard IV.2.1, in the paragraph introducing
(IV.2.1.1), printed p. 97 (PDF p. 103). The Hermitian form convention comes from
the definition on printed p. 96 (PDF p. 102). The source is David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated 9 July
2026, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The ambient group is Hausdorff, locally compact and nonarchimedean in the
sense of having a neighborhood basis of open subgroups. In this setting
that agrees with Renard's totally disconnected hypothesis. The subgroup
`H` is closed with compact left quotient `H \ G`. Closedness supplies the
local compactness of `H` used by the published relative modular character.

The statement uses `Hecke.Homomorphism.relativeModularCharacter` for
Renard's relative modulus `δ`. The smooth character `χ` has positive real
values and square `δ`, which characterize `δ`'s positive square root.
`Induction.normalizedCompactInduced H χ τ.representation` is the
right-translation action on the actual compactly supported modulo `H`
inducing functions with covariance `f(hg) = χ(h) τ(h) f(g)`. Compactness
of `H \ G` identifies this model with smooth induction.

For any smooth complex `τ` and invariant Hermitian form `B` with zero
radical on `τ`, the proposition requires an invariant Hermitian form with
zero radical on the induced representation. The forms are conjugate-linear
in the first variable and complex-linear in the second. Hermitian symmetry
makes the two radical conditions equivalent. The quantifiers include all
smooth coefficient representations and all nondegenerate invariant Hermitian
forms, including indefinite forms.
