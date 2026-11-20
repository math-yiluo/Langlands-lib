# Unipotent closed subgroups lie in a unipotent kernel with multiplicative quotient

This module proves two theorems over a field `k : Type u`, for group schemes
over `Spec (CommRingCat.of k)`. Together they give the second part of Milne's
Theorem 16.6: every unipotent closed subgroup lies in the kernel of an fppf
quotient onto a group of multiplicative type.

## `IsUnipotent.hom_eq_zero_of_isMultiplicativeType`

**Statement.** Let `U` and `M` be group schemes with `[IsAffineHom U.X.hom]`,
`IsUnipotent U` and `IsMultiplicativeType M`. Then every homomorphism
`f : U ⟶ M` is the trivial homomorphism `0`.

This is Milne's Corollary 14.18(a). The Library proves 14.18 as part 3 of
`UnipotentMultiplicativeTrivialityStatement` (the theorem
`unipotentMultiplicativeTriviality` in
`Langlands.GroupScheme.Unipotent.MultiplicativeTrivialityProof`). That
statement assumes `LocallyOfFiniteType` and `IsAffineHom` for the structure
morphisms of both `U` and `M`, and concludes `range f = ⊥`. The step that
proves it, with only `[IsAffineHom U.X.hom]` and the conclusion `f = 0`, is a
`private` theorem (`hom_eq_zero_to_multiplicativeType`) in that module, so it
cannot be imported. The proof here copies that private proof verbatim. It is
needed in this form because the quotient groups `M` in Theorem 16.6 come with
no `LocallyOfFiniteType` or `IsAffineHom` instances.

**Proof.** Unfold `IsMultiplicativeType M`: there are a field `K` over `k`, a
finitely generated commutative group `Λ` and an isomorphism
`e : M_K ≅ D(Λ)` over `K`. Let `B` be base change along
`Spec K ⟶ Spec k` and put `g := B.map f ≫ e.hom : U_K ⟶ D(Λ)`.

1. `U_K` is unipotent (`IsUnipotent.baseChange`, Milne 14.9).
2. `g = 0`. By `hom_ext_points` it suffices to show that `x ≫ g` is the unit
   point for every point `x` of `U_K` on every test scheme `T`. Points of
   `D(Λ)` are identified with characters `Multiplicative Λ →* Γ(T)ˣ` by the
   injective map `Diagonalizable.characterPointsEquiv`. For `m : Λ`, the
   character `evalCharacter m` of `D(Λ)` restricts along `g` to a character
   of `U_K`. A character of a unipotent group evaluates to `1` on every point
   (`IsUnipotent.characterEval_eq_one`). So the character attached to
   `x ≫ g` is `1` at every `m`.
3. Base change along `Spec K ⟶ Spec k` is faithful
   (`GaloisCocharacterDescent.faithful_algebraPullback`), so
   `GroupScheme.baseChange b` is injective on morphisms. Since
   `B.map f = g ≫ e.inv = 0`, we get `f = 0`.

## `IsUnipotent.range_le_of_isFppfQuotient`

**Statement.** Let `G` have `[IsAffineHom G.X.hom]`. Let `i : U ⟶ G` and
`q : G ⟶ M` satisfy `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`
and `IsMultiplicativeType M`. Then for every `j : V ⟶ G` with
`IsClosedSubgroup j` and `IsUnipotent V`,
`SubgroupFunctor.range j ≤ SubgroupFunctor.range i`.

This is the second part of Milne's Theorem 16.6, in the form used by the
published statement: neither unipotence nor normality of `U` is needed.

**Proof.** The kernel clause of `IsFppfQuotient` is
`range (kernelι q) = range i`, so it suffices to show
`range j ≤ range (kernelι q)`. Since `j` is a closed immersion and `G` is
affine over `k`, `V` is affine over `k` (`IsClosedSubgroup.isAffineHom`). By
the previous theorem `j ≫ q = 0`. Then `range_le_kernelι_of_comp_eq_zero`
gives the inclusion.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Printed
page numbers; the one-based PDF page is the printed page plus 16.

- Corollary 14.18, p.284: "There are no nontrivial homomorphisms over k (a)
  from a unipotent algebraic group to an algebraic group of multiplicative
  type, or (b) from an algebraic group of multiplicative type to a unipotent
  algebraic group."
- Theorem 16.6, pp.325–326: "When these conditions hold, G_u is unique and
  contains every unipotent algebraic subgroup of G." Milne's proof derives
  this from 14.18: the composite `V → G → G/G_u` is trivial.

The first theorem assumes only that `U` is affine over `k`. It drops Milne's
standing hypothesis that algebraic groups are of finite type, for both `U`
and `M`, as the copied Library proof allows. (A group `M` of multiplicative
type in the sense of `IsMultiplicativeType` is of finite type anyway, since
`Λ` is finitely generated; the point is only that no instance needs to be
supplied.)
