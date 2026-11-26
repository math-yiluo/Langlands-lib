# Exactness and finite length for the matrix parabolic functors

`Langlands.Aubert.General.RationalPointFamily.GL.LocalFieldMatrixParabolicPreservationStatement`
asserts that the actual normalized parabolic induction and normalized
Jacquet functors of every standard upper-block parabolic of
\(\mathrm{GL}_n(F)\) preserve finite length and short exact sequences of
finite-length smooth complex representations. It quantifies over every
nonarchimedean local field, every rank including zero, and the carrier
universes used in `LocalFieldMatrixParabolicExactLength`. These four
preservation properties define the exact Grothendieck-group maps in the
matrix alternating operator.

This is the matrix specialization of Renard, *Représentations des groupes
réductifs p-adiques* (French 2026 version), VI.1.2 for exactness, VI.6.2
for finite length under induction, and VI.6.4 for finite length under
Jacquet restriction, printed pp. 135–136 and 178–179
(`renard-2026-representations-groupes-reductifs-padiques`). Renard uses the
inverse convention for the parabolic modulus. Accordingly, the Lean
functors use the positive half-power of the upper-block determinant
modulus for induction and its inverse for the normalized Jacquet module.
The empty block shape gives the extension to the trivial group in rank
zero.
