# Splitting of the torus quotient of a solvable group over an algebraically closed field

`Langlands.GroupScheme.SolvableSplitExtensionStatement.{u}` is a
proposition target, not a proof.

Let `k : Type u` be an algebraically closed field and let `H` be a smooth
connected affine group scheme over `Spec k` that is solvable
(`IsSolvableGroupScheme H`). Let `U` and `D` be group schemes over `Spec k`,
with homomorphisms `i : U ⟶ H` and `q : H ⟶ D`, such that:

- `i` is a closed subgroup (`IsClosedSubgroup i`);
- `U` is smooth, connected and unipotent (`IsUnipotent U`);
- the range subgroup functor of `i` is normal in `H` on every test scheme
  (`SubgroupFunctor.IsNormal`);
- `q` is a represented fppf quotient by that range
  (`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`): the
  underlying morphism of schemes of `q` is flat, surjective and locally of
  finite presentation, and the range of the actual kernel of `q` equals the
  range of `i` on every test scheme;
- `D` is a split torus (`IsSplitTorus D`).

Then there is a group-scheme homomorphism `σ : D ⟶ H` with `σ ≫ q = 𝟙 D`.
In other words, the extension `e → U → H → D → e` splits.

The hypotheses on `H`, `U`, `D`, `i` and `q` are exactly the conclusions of
`Langlands.GroupScheme.SolvableTorusQuotientStatement`. So that statement and
this one together give a homomorphic section of the torus quotient of every
smooth connected solvable affine group over an algebraically closed field.
The statement does not assert that sections are unique or conjugate.

## Source

J. S. Milne, *Algebraic Groups* (2017), Theorem 16.26, printed pp.332–333
(zero-based PDF pages 347–348). For a trigonalizable algebraic group `G`
over a field `k`, the extension `e → G_u → G → D → e` splits in case (a),
when `k` is algebraically closed. Here `G_u` is the normal unipotent
subgroup with quotient `D` of multiplicative type (Notation 16.7, printed
p.326, zero-based PDF page 341). Summary 16.29(b), printed p.334 (zero-based
PDF page 349), restates the algebraically closed case for extensions of a
smooth group of multiplicative type by a unipotent group.

The source applies to the present `H`:

- Proposition 16.2, (d)⇒(a), printed pp.324–325 (zero-based PDF pages
  339–340): a group with a normal unipotent subgroup `U` such that `G/U` is
  diagonalizable is trigonalizable. A split torus is diagonalizable, so `H`
  is trigonalizable.
- Theorem 16.6, printed pp.325–326 (zero-based PDF pages 340–341): such a
  normal unipotent subgroup with quotient of multiplicative type is unique.
  Hence `U` is Milne's `G_u` and `D` is `G/G_u`.

Smoothness and connectedness of `H` and `U`, and solvability of `H`, are
not needed by Theorem 16.26(a). They are kept because
`SolvableTorusQuotientStatement` supplies them and because they make the
target easier to prove: Theorem 16.26(b), for a perfect field and smooth
connected `G_u`, uses the `G_a` series of Corollary 16.23.

## Encodings

- Milne's algebraic groups are group schemes of finite type over `k`.
  Here `H` is smooth (so locally of finite presentation) and affine (so
  quasi-compact), hence of finite type. `U` is closed in `H`, so it is
  affine and of finite type. `D` is a finite product of copies of the
  multiplicative group, so it is affine and of finite type.
- Milne's quotient map `G → G/G_u` is a faithfully flat homomorphism with
  kernel `G_u`. The existing predicate `RelativeRoot.IsFppfQuotient` states
  this for the actual morphism `q`. Flat, surjective and locally of finite
  presentation together give faithful flatness. The kernel clause compares
  subgroup functors on every test scheme.
- A splitting of the extension is a section of `q` as a homomorphism of
  algebraic groups (Milne, statement of Theorem 16.27(a), printed p.333).
  Here it is a morphism `σ : D ⟶ H` in the category of group schemes over
  `Spec k`, so it preserves multiplication, and `σ ≫ q = 𝟙 D` is the section
  equation.
- Solvability is the existing Library predicate `IsSolvableGroupScheme`.
  For a smooth connected group over an algebraically closed field it agrees
  with Milne's solvability by Milne Proposition 16.34, (c)⇔(d), printed
  p.336 (zero-based PDF page 351).
- Split tori are the existing `IsSplitTorus`: isomorphic as group schemes to
  a finite product of copies of the multiplicative group over `Spec k`.

The official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read. It rewrites the
proofs of Section 15h, deletes 15.29–15.30, and changes one word in the
chapter 16 introduction, printed p.324. It has no correction to the
statements of Proposition 16.2, Theorem 16.6, Theorem 16.26 or Summary 16.29.

## Use

This is a planned input for a proof of
`Langlands.GroupScheme.SolvableMaximalTorusSemidirectStatement`, which is
Milne Theorem 16.33(d). In the planned proof, the section `σ` gives a torus
`σ(D)` that maps isomorphically onto `D`. Comparing a maximal torus
containing `σ(D)` with a given maximal torus shows that the given torus
surjects onto `D` on rational points. That proof is in turn an input for
`Langlands.GroupScheme.MaximalRankRadicalTorusIntersectionStatement`.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
