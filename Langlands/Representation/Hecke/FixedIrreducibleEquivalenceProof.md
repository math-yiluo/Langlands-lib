# Irreducible representations determined by their fixed corner modules

Author: Worker 136. The theorem `Langlands.Hecke.irreducibleEquivIffFixedEquiv`
proves exactly `Langlands.Hecke.IrreducibleEquivIffFixedEquivStatement.{u,v}`.
The statement's independent universes, objects and hypotheses are unchanged.

This is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.1.5, Theorem (ii), printed p.61 / PDF p.67.
The original is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 136 read PDF pp.66–67.

In the forward direction, restrict a representation equivalence to the published
fixed-vector spaces using `fixedVectorsEquiv`. The identity `cornerAction_equiv`
makes this additive equivalence linear for the actual corner action.

In the converse direction, take a nonzero fixed vector `a` in the first
representation and its image `b` under the given corner-linear equivalence.
Injectivity makes `b` nonzero. Corner linearity and injectivity imply that a corner
element kills `a` exactly when it kills `b`. The published theorem
`nonempty_equiv_of_cornerAction_eq_zero_iff` then produces an equivalence of the
two irreducible smooth representations.

This uses the published annihilator proof from `Hecke.CornerDetermination`,
the Bernstein–Zelevinsky 2.10(b) route, instead of reproving Renard's general
idempotent-module correspondence. The other import is the unchanged target
statement module. No new construction or assumption is introduced.
