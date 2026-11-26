# Proper induction and the unramified orbit of a σ-discrete series

Over a nonarchimedean local field `E`, let `τ` satisfy
`IsSigmaDiscreteSeries σ n τ`. The underlying representations in its
σ-invariant unramified twist orbit cannot be equivalent to actual
unnormalized smooth induction from a smooth σ-stable representation on
a proper standard Levi. The inducing carrier and the two representation
carriers use the same universe, as in the definition of σ-discreteness.

Given such an equivalence for a twist by `ψ`, twist the entire equivalence
by `ψ⁻¹`. The inverse character factors on the parabolic through its Levi
projection, since an unramified character of `GL_n(E)` depends on the
determinant order and the determinant is the product of the diagonal block
determinants. The Levi character is σ-invariant because the block diagonal
embedding commutes with the entrywise automorphism. Multiplication of
sections by the inverse ambient character moves the twist inside induction.
The twisted inducing representation remains smooth and σ-stable. The
resulting equivalence for `τ` contradicts its σ-discreteness.

This is the twist invariance of noninduction used for essentially
σ-discrete representations in Henniart–Lemaire (2011), II.5.13, printed
p. 114. In II.4.6, p. 88, the source defines σ-discreteness with respect
to normalized induction of irreducible data. The implication above uses
the Library's noninduction predicate and allows nonunitary unramified
twists of the underlying representation.
