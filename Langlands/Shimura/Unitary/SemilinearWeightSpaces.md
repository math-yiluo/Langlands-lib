# Semilinear transport of inverse-weight spaces

This internal construction derives from the common inverse-weight submodule in `ComplexWeightConjugacy` and Mathlib's matrix and module-rank APIs. It supplies the coefficient-transport step needed to compare complex cocharacter weights under field automorphisms. It does not assume that an automorphism of a matrix algebra is inner.

Let `S` be any commutative ring in any universe, let `s : S ≃+* S` be a ring automorphism, and let `n : ℕ`. The definition `coefficientVectorEquiv s n` is the `s`-semilinear equivalence of `Fin n → S` given by applying `s` coordinatewise. Its inverse applies `s.symm` coordinatewise. Additivity and semilinearity are the corresponding ring-homomorphism identities. The two local `RingHomInvPair` instances express that the scalar homomorphisms of `s` and `s.symm` are mutually inverse; they introduce no additional hypotheses.

`coefficientVectorEquiv_mulVec` proves

\[
 s(Mv)=s(M)s(v),
\]

where both occurrences of `s` on vectors and its occurrence on the matrix mean entrywise application. The proof is Mathlib's finite-sum matrix identity `RingHom.map_mulVec` at each coordinate.

For any family `a : Sˣ → Matrix (Fin n) (Fin n) S`, `coefficientWeightFamily s a` is the family

\[
 b(u)=s\bigl(a(s^{-1}(u))\bigr).
\]

The inverse automorphism on units is the inverse of `Units.mapEquiv s.toMulEquiv`; the outer automorphism acts entrywise on matrices. The identity `coefficientWeightFamily_map` evaluates this at the transported unit and gives `b(s(u)) = s(a(u))`. No homomorphism condition on `a` is needed.

Recall that `inverseWeightSpace a` consists of the vectors `v` such that `a(u)v = u⁻¹ • v` for every unit `u`. The theorem `mem_inverseWeightSpace_coefficient_iff` proves that `s(v)` lies in `inverseWeightSpace b` exactly when `v` lies in `inverseWeightSpace a`. For the forward implication it evaluates the target condition at `s(u)` and uses injectivity of the coordinate equivalence. For the reverse implication it writes every target unit as `s(u)` using surjectivity. In both directions the matrix identity and preservation of multiplication and inverse units transport the weight equation.

The definition `inverseWeightSpaceCoefficientEquiv s a` restricts the coordinate equivalence and its inverse to these submodules, using the preceding membership equivalence. Its inverse laws, additivity and semilinearity follow by subtype extensionality from the ambient equivalence.

Finally, `finrank_inverseWeightSpace_coefficient` states

\[
 \operatorname{finrank}_S(\operatorname{inverseWeightSpace}(b))
 =\operatorname{finrank}_S(\operatorname{inverseWeightSpace}(a)).
\]

The proof applies Mathlib's `rank_eq_of_equiv_equiv` to the additive equivalence, the bijective scalar map `s`, and the semilinearity equation, then applies `Cardinal.toNat` to the resulting equality of cardinal ranks. Thus the stated equality uses Mathlib's general `finrank` convention; no field, nontriviality, freeness, or finite-dimensionality hypothesis is added. When specialized to a complex vector space it gives the usual equality of finite dimensions.

This module constructs generic semilinear transport. Identifying a particular Galois-transformed cocharacter family with this transport, accounting for the inner change between embedding charts, and comparing reflex fields remain separate obligations.
