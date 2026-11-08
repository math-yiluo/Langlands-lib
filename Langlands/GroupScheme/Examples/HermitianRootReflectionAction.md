# Action of Hermitian middle reflections

This internal continuation of `HermitianRootLeviReflections` derives the
middle-reflection action from the established coordinate formulas. The
coefficient field and finite index universes are independent; all
characteristics are allowed.

`DiagonalForm.IsAnisotropic H` means that `H.pairing x x = 0` implies
`x=0`. The module also proves subtraction identities for the pairing and
that entrywise conjugation preserves each self-pairing. The latter follows
term by term from commutativity and the involution identity.

For a root parameter `x` with scalar `z`, `reflectionMiddle_mulVec` proves
the action formula, even when `z=0`:

    (reflectionMiddle x * w)_i
      = w_i - bar(x_i)*H.pairing(w,bar(x))/z.

Division has its field meaning. The proof expands the matrix-vector product,
distributes the identity-minus-rank-one matrix, and factors the finite sum.
No invertibility conclusion is drawn when `z=0`.

For vectors `w,v` of equal self-pairing, put `u=w-v`.
`Parameters.betweenParameter w v heq` is the actual root parameter with
vector `bar(u)` and scalar `z=H.pairing w u`. Expanding the pairings and
using equality of the two self-pairings proves its trace equation.
If `H` is anisotropic and `w≠v`, the scalar is nonzero: otherwise the
trace equation forces the self-pairing of `u` to vanish, so `u=0`.

For nonzero `z`, substitution in the action formula gives
`reflectionMiddle (betweenParameter w v heq) * w = v`, by cancellation.
For any vector `t` with `H.pairing t (w-v)=0`, substitution shows that the
same middle matrix fixes `t`. This fixing identity does not need a
nonzero-scalar hypothesis.

`exists_elementary_levi_between` combines these calculations with the
existing actual Levi lift. Given an anisotropic `H`, a supplied nonzero
trace-zero scalar `s`, and equal-norm vectors `w,v`, it constructs an
element `g` of `elementarySubgroup H`, a nonzero scalar `a`, and a middle
matrix `T`, such that

    g = leviMatrix a T,   T*w=v,
    T*t=t whenever H.pairing t (w-v)=0.

For `w=v`, the proof takes the identity element and identity middle matrix.
Otherwise it takes the Levi lift of the between-vector parameter, with
`a=z/s`, and applies the two action identities. Membership refers to the
actual general linear group element, not a proposed abstract generator.

This establishes a single-vector matching step with a perpendicular fixing
property. Generation of every middle unitary matrix, source group-scheme
comparisons and the unrestricted local Kneser–Tits theorem remain separate
obligations.
