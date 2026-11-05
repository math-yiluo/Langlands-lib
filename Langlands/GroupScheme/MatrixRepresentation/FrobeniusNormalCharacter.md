# Inverse multiple characters via Frobenius-stable coordinates

Let `k` be a field of universe `u`, let `G` and `H` be group schemes over
`Spec k`, and assume `H` affine. All representations in this module are actual
group-scheme homomorphisms into finite general linear group schemes. Character
spaces use the universal affine coordinate-ring equation, retaining nilpotents.

`map_projection_mulVec` states that an identity `(B * C) * v = v` remains true
after applying any ring endomorphism of `k` to both matrices and the vector. It
uses preservation of matrix products and matrix-vector multiplication. No
linearity over `k` is asserted for that endomorphism.

`characterSpan_restrictCoordinates_frobenius` starts with a representation
`rho`, a homomorphism `i : H -> G`, and split matrices `B` and `C` whose columns
belong to the sum of the `H`-character spaces of `rho` and whose projection is
the identity on that sum. Fix an exponential characteristic `p` and exponent
`e`. Assume that the entrywise powered matrices split and are stable for
`rho.frobeniusPower p e`. The resulting coordinate restriction is spanned by
its `H`-character spaces. This assertion needs neither normality nor reducedness;
stability is an explicit premise.

The proof applies the coefficient ring homomorphism `x -> x^(p^e)` to vectors
in the original character span. Character-space vectors acquire weight
`(p^e) chi`, and their images under the powered projection belong to the same
character space of the coordinate restriction. Additivity extends membership
to the whole original span. Applying this to each column of `B` gives each
standard basis vector: `C * B = 1`, and entrywise powers fix zero and one.
Those basis vectors span the restricted representation. There is no need to
choose Frobenius roots of scalars.

Now assume that `k` is algebraically closed, `G` is affine and locally of finite
type, `p` is prime with `ExpChar k p`, and `i` is a monomorphism with normal
subgroup functor range. No reducedness or smoothness premise is made on either
group. `exists_inverse_frobenius_normal_characterVector` states that any
nonzero vector of subgroup character `chi` gives some exponent `e`, finite
ambient representation `sigma`, and nonzero vector of subgroup character
`-((p^e) chi)` in `sigma`.

Choose split coordinates on the original subgroup character span. Normality
gives invariance at rational ambient points. The imported finite-defect
nilpotence theorem supplies an exponent for which the powered coordinates are
stable on every scheme test. Ring-map functoriality preserves the splitting
identity. The preceding span theorem therefore applies. The original nonzero
vector remains nonzero after powering, since a field endomorphism is injective;
its image under the powered coordinate projection remains nonzero because the
split inclusion recovers it. The inverse-character theorem for a
character-spanned representation then supplies a nonzero vector of the opposite
character in the actual dual ambient representation. Restriction commutes with
duality, giving the required result.

`inverseFrobeniusNormalCharacterVector` chooses this data and packages it in
`InverseMultipleNormalCharacterVector`, with strictly positive degree `p^e`
encoded as `(p^e - 1) + 1`. The theorem
`hasInverseMultipleNormalCharacters_of_prime_expChar` supplies the full
inverse-positive-multiple occurrence property for every normal monomorphism
under the stated algebraically closed positive-characteristic hypotheses.
Closedness of the monomorphism is not needed for these occurrence conclusions.

This is an internal derivation toward the general quotient-existence theorem.
Milne, *Algebraic Groups* (2017), Lemma 5.16, printed pp. 102-103 (PDF pp.
118-119), obtains inverse positive multiples using a smooth Frobenius image.
The present argument replaces that geometric step by killing finitely many
nilpotent coordinate defects and then taking a dual character-spanned
representation. It proves the positive-characteristic occurrence conclusion
directly. Characteristic zero, descent to arbitrary fields, quotient
representability, and faithful flatness are not proved in this module.
