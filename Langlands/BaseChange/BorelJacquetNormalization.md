# Normalization of the actual integral-diagonal Borel Jacquet action

`BorelJacquetNormalizationStatement` identifies
`borelJacquetFixed F ρ` with `borelJacquetIntegralFixed F ρ` as submodules
of the actual upper Borel Jacquet quotient. They are the fixed spaces
of the integral diagonal for the unnormalized and normalized actions,
respectively.

`unnormalizedBorelJacquet_eq_half_smul` compares the two actions on each
vector of the quotient. The proof lifts the vector to the original
representation and applies the normalized Jacquet formula on quotient
classes. The unnormalized action at \(t\) is then the normalized
action multiplied by the positive half-modulus \(\delta_B(t)^{1/2}\).

`leviModulus_singletonLevi_of_ord` computes the full modulus from the
orders \(\nu_i\) of the diagonal entries. The upper Borel product of
the absolute-value quotients is
\[
   \delta_B(t)=q^{-\sum_{i<j}(\nu_i-\nu_j)}.
\]
The proof substitutes the residue-normalized absolute values in each
factor and adds their exponents. Integral diagonal units have order
zero in every coordinate, so their half-modulus is one. The actions
therefore have the same fixed vectors.

This comparison supplies the normalization in Henniart–Lemaire,
*Changement de base et induction automorphe pour GLₙ en caractéristique
non nulle* (2011), I.5.3, Proposition and proof, printed pp. 31–32,
and I.5.4, Lemma 2, printed p. 35. Multiplying the unnormalized
elementary prefactor \(q^{\rho(\nu)}\) by
\(\delta_B(t)^{1/2}\) gives the prefactor for the normalized action
in the source.
