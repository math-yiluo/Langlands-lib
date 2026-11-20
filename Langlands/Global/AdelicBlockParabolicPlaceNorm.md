# Determinant normalization at one archimedean place

For a matrix inserted at one real place, the adelic determinant character
is the absolute value of its local determinant. At a complex place it is the
squared complex norm of that determinant. The proof projects the determinant
to each mixed archimedean coordinate. The projection commutes with taking
determinants, so every other coordinate contributes the determinant of the
identity. The completion identifications are isometries, and the adelic
norm product gives exponent one at the real place and exponent two at the
complex place.

Let \(n_i\) be the ordered block sizes and \(m_i\) the diagonal blocks of a
local parabolic element. The definitions `realPlaceModulusValue` and
`complexPlaceModulusValue` write the local determinant formula

\[
\prod_{i<j}\frac{|\det m_i|_v^{n_j}}{|\det m_j|_v^{n_i}}
\]

with the corresponding real or complex local norm. The two theorems
`coe_parabolicHalfCharacter_realPlace` and
`coe_parabolicHalfCharacter_complexPlace` identify the restriction of the
global half-character with the positive square root of this formula.
Diagonal block extraction commutes with place insertion, so the proof
applies the preceding norm comparison to each block and takes the
existing square root.

This is an internal comparison of the determinant characters in
[`AdelicBlockDeterminantCharacter`](AdelicBlockDeterminantCharacter.md),
the local norm convention of [`IdeleAbsoluteValue`](IdeleAbsoluteValue.md)
and the local embeddings of
[`AdelicBlockParabolicPlace`](AdelicBlockParabolicPlace.md). It supplies
the normalization when comparing the covariant place restrictions of
adelic sections with local induction in stages.
