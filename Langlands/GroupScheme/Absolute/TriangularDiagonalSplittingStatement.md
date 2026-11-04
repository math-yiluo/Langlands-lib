# Splitting of the diagonal image of a triangular subgroup

`Langlands.GroupScheme.TriangularDiagonalSplittingStatement.{u}` is a
proposition target. This module supplies no proof.

## The statement

Let `k : Type u` be an algebraically closed field, with `u` arbitrary.
Let `H` be a group scheme over `Spec (CommRingCat.of k)` satisfying
`LocallyOfFiniteType H.X.hom` and `IsAffineHom H.X.hom`. Let `N` be any
natural number, zero included, and let

```text
j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
          (fun i => -(i.val : ℤ))
```

be a homomorphism of group schemes satisfying `IsClosedSubgroup j`. Set

```text
L := GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k)
       (fun i => -(i.val : ℤ))
f := j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k)
       (fun i => -(i.val : ℤ)) : H ⟶ L.
```

The conclusion asserts that there exist a group scheme `D` over
`Spec (CommRingCat.of k)` and homomorphisms of group schemes
`d : D ⟶ L`, `q : H ⟶ D` and `s : D ⟶ H` such that

```text
IsClosedSubgroup d ∧ q ≫ d = f ∧ s ≫ q = 𝟙 D.
```

All three maps are morphisms of `GroupScheme (Spec (CommRingCat.of k))`,
which is `Grp (Over (Spec (CommRingCat.of k)))`. They are therefore
homomorphisms of group schemes over `Spec k`, not merely morphisms of
schemes. `IsClosedSubgroup d` says that the underlying morphism of schemes
of `d` is a closed immersion.

No smoothness or connectedness of `H` is assumed. Nothing is asserted about
the smoothness or connectedness of `D`, about flatness of `q`, or about
uniqueness of `s`.

## The concrete groups and the map `f`

Write `e i = -(i.val : ℤ)`. The block parabolic scheme for `e` has matrix
entries zero whenever `e i < e j`, that is, whenever `i.val > j.val`. It is
the upper triangular group `T_N` in Milne's notation. Distinct indices have
distinct weights, so `L` is the diagonal group `D_N`. The existing theorem
`GeneralLinear.pointsEquiv_blockLimitHom` identifies `blockLimitHom` on
every test scheme with the block diagonal projection of matrices. For these
weights it is the ordinary diagonal map `T_N → D_N`. Thus `f` is the
diagonal map of `H`, embedded in `T_N` by `j`.

The scheme-theoretic kernel `kernel f` is the intersection of `H` with the
upper unitriangular group `U_N`. This is explained in the paired Markdown
of the existing `TriangularDiagonalKernelGeometryStatement`, using
`kernelPointsEquiv` and `GeneralLinear.blockUnipotentIsoKernel`.

## Why `D` is the actual diagonal image

The conclusion pins `D` down. The map `d` is a closed immersion and
`q ≫ d = f`. The map `q` has the section `s`. Let `Z` be a closed
subscheme of `L` through which `f` factors. Then `q` factors through the
closed subscheme `d⁻¹(Z)` of `D`, and so does the identity `s ≫ q = 𝟙 D`.
Hence `d⁻¹(Z) = D`, and `d` factors through `Z`. Therefore `d` identifies
`D` with the scheme-theoretic image of `f` in `L`, together with the
group structure that it inherits. In other words, `D` is the actual image
of `H` in the diagonal group, and `q` is the corestriction of `f` to that
image. Because `d` is a monomorphism, the kernel of `q` is the kernel of
`f`, which is `H ∩ U_N`.

The section `s` is a homomorphism, so it splits the extension

```text
e → kernel f → H → D → e.
```

A downstream use is the retraction `h ↦ h · s(q(h))⁻¹` of `H` onto the
actual kernel `kernel f`.

## Literature correspondence

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes
of Finite Type over a Field* (2017), Chapter 16. Page references are to the
printed book, followed by the one-based PDF page.

- Proposition 16.2(c)⇒(d), printed p.325 (PDF p.341), takes an algebraic
  subgroup `G` of `T_n` and sets `U = U_n ∩ G`. It shows that `U` is normal
  and unipotent. It also shows that `G/U` embeds into `T_n/U_n` and is
  therefore diagonalizable. For `G = H` this embedding is the closed
  subgroup `d : D ⟶ L` of the statement, since `T_N/U_N` is the diagonal
  group by the diagonal projection.
- Theorem 16.6, printed pp.325–326 (PDF pp.341–342), and Note 16.8(b),
  printed p.326 (PDF p.342), show the following. A normal unipotent
  algebraic subgroup with quotient of multiplicative type is unique and
  equal to the canonical `G_u`. So the diagonal kernel `H ∩ U_N` is `H_u`.
  The quotient `H/H_u` is the diagonal image `D`.
- Theorem 16.26(a), printed pp.332–333 (PDF pp.348–349), states the
  following. Let `G` be a trigonalizable algebraic group over an
  algebraically closed field. Then the extension `e → G_u → G → D → e`
  splits. Here `D = G/G_u`. The theorem assumes neither smoothness nor
  connectedness. Applied to `H`, which is trigonalizable by 16.2(c)⇒(a)
because `j` embeds it in `T_N`,
  it furnishes the homomorphism `s : D ⟶ H` with `s ≫ q = 𝟙 D`.

This statement isolates exactly the conclusion of 16.26(a) for the
concrete embedding `j`. It also records the identification of the quotient
with the diagonal image as the factorization `q ≫ d = f`. It does not state
Theorem 16.27 on the conjugacy of sections or on maximal diagonalizable
subgroups.

Milne's algebraic groups are affine group schemes of finite type over the
field. Here the hypotheses `LocallyOfFiniteType H.X.hom` and
`IsAffineHom H.X.hom` state this convention explicitly. An affine morphism
is quasi-compact, so together they make `H` of finite type over `k`. The
task requires both hypotheses to be stated. No smoothness or connectedness
hypothesis is added, because 16.26(a) does not need one. When `N = 0`, the
groups `T_0` and `D_0` are trivial. The statement still quantifies this
case.

The official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read. Its only Chapter
16 entries concern p.324, 16.20 on p.330, and 16.65 on p.349. None of them
corrects 16.2, 16.6, 16.8 or 16.26.

Book source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
