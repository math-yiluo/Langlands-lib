# Unipotence of dynamic unipotent subgroups over a field

`Langlands.GroupScheme.DynamicUnipotentUnipotenceStatement.{u}` is an unproved
proposition target over every field `k : Type u`. The group scheme `G` over
`Spec k` is affine and locally of finite type, given as instance arguments, and
`χ : Gm ⟶ G` is an actual homomorphism of group schemes over `Spec k`. The
existing subgroup functor `Dynamic.unipotent χ` consists of the points `g` of
`G` on every relative test whose orbit map `t ↦ χ(t) g χ(t)⁻¹` extends over
the affine line with value `1` at `0`; this is `U_G(χ)` of CGP.

For every group scheme `H` over `Spec k` and every homomorphism `j : H ⟶ G`
with `(Dynamic.unipotent χ).IsRepresentedBy j`, meaning that the underlying
morphism of schemes is a monomorphism and the image of `j` equals
`Dynamic.unipotent χ` on every relative test, the statement concludes
`IsUnipotent H`. That predicate is the representation-theoretic one from
`Reductive/Basic.lean`: every nonzero finite-dimensional matrix representation
of `H` over `k` has a nonzero fixed vector. The statement does not assert that
a representative exists; the published affine representability results for
dynamic subgroups supply one.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive Groups* (2nd edition,
2015), Lemma 2.1.5 and its proof, printed pp.50–51 (PDF pp.76–77): "if `G` is
of finite type over `k` then `U_G(λ)` has unipotent fibers over `Spec k`". Over
a field this says that `U_G(λ)` is a unipotent `k`-group. The proof embeds `G`
into some `GL_n` and reduces to Example 2.1.1. The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

The statement specializes Lemma 2.1.5 to a field base ring and to affine `G`
locally of finite type, hence of finite type. It uses the fixed-vector
definition of unipotence, which is Milne's definition (*Algebraic Groups*
(2017), 6.45, recalled at the start of §14b, printed p.280). For affine groups
of finite type over a field it is equivalent to being isomorphic to an
algebraic subgroup of the upper triangular unipotent group `U_n` (Milne,
Theorem 14.5, printed p.281); that equivalence is not part of this statement. Unipotence is preserved by
isomorphism, so the conclusion does not depend on which representative is
used. The field is not assumed perfect or algebraically closed, and no
restriction on its characteristic is imposed. No theorem or instance proves
this target here.
