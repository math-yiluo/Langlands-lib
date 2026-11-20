# Transitivity of normalized block constant terms on GLₙ

`normalizedBlockConstantTerm` integrates a continuous rational-invariant
function over the rational quotient of the block unipotent radical, using its
intrinsic measure of total mass one. Compactness follows by recognizing the
block unipotent subgroup as the radical of the parabolic for the corresponding
diagonal cocharacter. This also covers the trivial radical.

For weights `e` refining `w`, `normalizedBlockConstantTerm_eq_iterated`
identifies the refined term with the mass-one period of the coarse term over
the extra unipotent directions in the coarse Levi. Its proof uses the block Levi
projection, which splits the refined radical as the coarse radical followed by
its Levi part, over both the adeles and the ground field. The normalized
semidirect integral formula applies to the three compact rational quotients.
The inner period is identified with the coarse term by associativity of
multiplication. `normalizedBlockConstantTerm_unipotent_mul` follows from right
invariance of the quotient probability.

The module gives a derived formula for the integrals used in Langlands's
Lemma 4 and the Levi-cuspidality step in the proof of Proposition 2, printed
pp. 204–205 (Corvallis Part I, PDF pp. 199–200). The registered source is
`langlands-1979-notion-automorphic-representation`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
