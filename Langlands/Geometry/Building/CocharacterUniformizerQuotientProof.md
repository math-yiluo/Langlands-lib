# Actual integral and common-uniformizer quotients: proof

`Langlands.GroupScheme.CocharacterUniformizer.quotientComparison` proves exactly
`Langlands.GroupScheme.CocharacterUniformizer.QuotientComparisonStatement`.
It retains every universe, field and group-scheme parameter of the published
statement: `F : Type u` is any nonarchimedean local field in either
characteristic, `T` is any actual split torus, `A` is any actual commutative
group scheme, and `f : A → T` is any morphism.

Write `P` for the range of `RealTorusSpace.cocharacterMapInt f`, `N` for
the rational-point image of `CA F A`, and `q` for `QuotientGroup.mk' N`.
The implemented proof has the following steps.

1. `Plancherel.RenardCartan.uniformizerSection_naturality` identifies the
   image of the source section at a cocharacter `b` with the target section
   at its postcomposition `b ≫ f`. These are the existing sections at the
   same chosen field uniformizer.
2. The local equivalence `hzero` proves that
   `q (latticeSection F T (Multiplicative.ofAdd c)) = 1` if and only if
   `c ∈ P`. In the forward direction, membership in `N` supplies a source
   section witness. Naturality and injectivity of the target section,
   from `(isUniformizerLatticeSection F T hT).1`, identify `c` with the
   postcomposition of that witness. In the reverse direction, naturality
   provides a witness for membership in `N` directly.
3. The homomorphism `r` restricts `q` composed with the target section to
   the subgroup `(CA F T).map q`. Its additive form `g` has kernel exactly
   `P.toAddSubgroup`, by `hzero` and equality of subtype values. It is
   surjective because every element of this subgroup has an image witness
   in `CA F T`, and every element of `CA F T` has a section witness.
4. `QuotientAddGroup.liftEquiv` gives the additive equivalence from the
   quotient by this exact kernel. `AddEquiv.toMultiplicativeLeft`
   converts it to the multiplicative equivalence in the statement.
   The required equality in the ambient quotient on every representative
   is definitional and is proved by `rfl`.

Only the target section's injectivity is used; no injectivity of `f` or
of the source section is required. The proof uses the original actual
cocharacters, rational points and uniformizer throughout.

The comparison is an internal consequence motivated by David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, V.2.5 (printed p.107 / PDF p.113) and the quotient relation
(V.3.24.1) (printed p.117 / PDF p.123), registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The scope for arbitrary commutative `A` and arbitrary `f` is the derived
generality explained in the statement's Markdown. This proof concerns
the group quotient and its full representative formula; it supplies no
nonnegative monoid, finite-generation, freeness or strict-face result.

The published dependencies of the proof were verified and the proof was
compiled.
