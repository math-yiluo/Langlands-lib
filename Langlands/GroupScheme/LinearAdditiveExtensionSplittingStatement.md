# Splitting of extensions of diagonalizable groups by linear closed additive subgroups

Worker 1421.

`Langlands.GroupScheme.LinearAdditiveExtensionSplittingStatement.{u}`
is a proposition definition. It records, without proof, the case of
Milne's Theorem 15.34(d) used for triangular diagonal splitting.

## The proposition

The statement quantifies over every algebraically closed field `k : Type u`
and every `Λ : Type u` with `AddCommGroup Λ` and `AddGroup.FG Λ`. It
writes `R := CommRingCat.of k` and works over the base `Spec R`, and it
lets `D := Diagonalizable.groupScheme R Λ` be the actual diagonalizable
group scheme `Spec R[Λ]`. Its group object is `D.toGrp` and its underlying
scheme over the base is `D.X`. The universe `u` is arbitrary. `Λ` may
have torsion and may be trivial.

It then quantifies over the following data.

- `E : GroupScheme (Spec R)`, with instance binders
  `LocallyOfFiniteType E.X.hom` and `IsAffineHom E.X.hom`. So `E` is an
  affine group scheme of finite type over `k`. Neither smoothness nor
  connectedness is assumed.
- An actual group-scheme homomorphism `q : E ⟶ D.toGrp`. Its underlying
  scheme morphism `q.hom.hom.left` is assumed flat, surjective and locally
  of finite presentation.
- An actual homomorphism `a : kernel q ⟶ VectorGroup.groupScheme R 1`
  with `IsClosedSubgroup a`. Here `kernel q` is the Library's full
  scheme-theoretic kernel, the pullback of `q` along the unit of `D`, and
  `kernelι q` is its inclusion into `E`. `IsClosedSubgroup a` says that
  the underlying morphism of schemes is a closed immersion. So `a` exhibits
  the kernel as a closed subgroup scheme of the one-dimensional vector group
  `𝔾ₐ`. It may be all of `𝔾ₐ`, or finite, or nonreduced. No identification
  with `𝔾ₐ` is assumed.
- A character `χ : characterLattice D`, i.e. a homomorphism `D ⟶ 𝔾ₘ`.
  It may be trivial.
- An `AutomorphicAction D.toGrp (kernel q)` named `b`: an action of `D`
  on the kernel by group automorphisms, given by one scheme morphism. Its
  effect on points is `b.act`.

There are two hypotheses, each required on every test object
`T : Over (Spec R)`. Products and inverses of morphisms `T ⟶ E.X` use
the group structure on points opened by `open scoped CategoryTheory.MonObj`.

1. *The action is induced by conjugation in `E`.* For all
   `g : T ⟶ E.X` and `x : T ⟶ (kernel q).X`,
   `b.act (g ≫ q.hom.hom) x ≫ (kernelι q).hom.hom
     = g * (x ≫ (kernelι q).hom.hom) * g⁻¹`.
   So acting by the image of `g` in `D`, then including into `E`, equals
   conjugating the included point by `g`.
2. *The action is the restriction of a linear action on `𝔾ₐ`.* For all
   `d : T ⟶ D.X` and `x : T ⟶ (kernel q).X`,
   `b.act d x ≫ a.hom.hom
     = (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom)`.
   Here `VectorGroup.weightAction χ` is the Library's action of `D` on
   `𝔾ₐ` that scales the coordinate by the value of `χ`. The equation says
   `a` is equivariant from `(kernel q, b)` to `(𝔾ₐ, weightAction χ)`.

The conclusion is `∃ s : D.toGrp ⟶ E, s ≫ q = 𝟙 D.toGrp`. That is, `q`
has a section that is an actual group-scheme homomorphism.

The statement adds no certificate of an extension class, of vanishing
cohomology or of splitting. It assumes no smoothness, connectedness,
characteristic or reducedness condition, and no isomorphism of the kernel
with `𝔾ₐ`. The two equations describe the actual induced action; they
do not assume a splitting.

## Source and translation

J. S. Milne, *Algebraic Groups* (corrected reprint, 2022), Theorem 15.34,
printed pp.319–320 (zero-based PDF pages 329–330). It considers an
algebraic group `G` of multiplicative type acting on an algebraic subgroup
`U` of `𝔾ₐ`. It states `Ext¹(G, U) = 0` in five cases. Case (d) is:
`k` is algebraically closed and the action of `G` on `U` is the
restriction of a linear action on `𝔾ₐ`.

The pieces correspond as follows.

- *Extensions.* A sheaf extension `0 → M → E → G → 1` (Milne (110),
  printed p.313, zero-based PDF page 323) is exact as a sequence of fppf
  sheaves. Definition 15.21 (printed p.314, zero-based PDF page 324)
  defines `Ext(G, M)` as the set of equivalence classes of sheaf extensions
  inducing the given action on `M`. When `M` is an algebraic group, one may
  restrict to extensions with `E` an algebraic group. The same page
  identifies `Ext¹(G, M)` with `Ext(G, M)`. So `Ext¹(G, U) = 0` says that
  every such extension is equivalent to the semidirect product. This is
  the same as saying the quotient map has a homomorphic section, which is
  the Lean conclusion.
- *The quotient map.* In the Lean statement the kernel of the extension is
  the actual kernel `kernel q`. Exactness on the right becomes the
  assumption that `q` is flat, surjective and locally of finite
  presentation. For finite-type group schemes over a field this is the
  same as being a quotient map, i.e. an epimorphism of fppf sheaves.
- *Algebraic groups.* Milne's algebraic groups are group schemes of finite
  type over `k`; in the Lean statement `E` has finite type over `k`. Milne
  does not require `E` to be affine. Here, though, `E` is an extension of
  the affine group `D` by the affine group `U`, so `q` is a torsor under
  an affine group and `E` is affine. The binder `IsAffineHom E.X.hom` is
  the form the objective specifies; this note explains why it loses
  nothing, and the Lean proves nothing about it.
- *Multiplicative type.* Over an algebraically closed field, a group of
  multiplicative type is diagonalizable. Being of finite type, it is
  `D(Λ)` for a finitely generated abelian group `Λ`. The Lean statement
  takes that diagonalizable group itself as the quotient. Ranging over
  every finitely generated `Λ` covers all such `G` up to isomorphism.
- *The action and its linearity.* `U ⊆ 𝔾ₐ` becomes the closed embedding
  `a`. The `G`-module structure on `U` is `b`. Hypothesis 1 says that the
  extension induces this action. A linear action of `G` on `𝔾ₐ` comes from
  a one-dimensional representation, i.e. scaling by a character. Hypothesis
  2 says that `b` is the restriction of the action through `χ` along `a`.

Milne's printed proof of case (d) uses the exact sequence
`e → U → 𝔾ₐ → 𝔾ₐ → e` from Exercise 14-3 and Proposition 15.31.
For the 2017 edition, the official errata (p.317) says to delete 15.29
and 15.30 and that the proofs in Section 15h have been rewritten. The
registered source entry says that the 2022 reprint contains the rewritten
Section 15h. The 2022 PDF still prints statements numbered 15.29 and 15.30
(printed pp.317–318). This module uses neither of them. It states Theorem
15.34(d) as printed in 2022, as the objective requires, and records no
proof route. The latest author errata page for the 2022 reprint, read on
2026-11-03, has no entry for Theorem 15.34.

Registered original: `milne-2022-algebraic-groups`, SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The errata snapshot for the 2017 edition is registered as
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`.

## Use

This statement is a prerequisite for the triangular diagonal splitting
statement (task `4fe37606-9ed8-4910-a71b-9e0e8ae0a63f`) and its consumer
(task `d1fee1c3-e435-49e7-a1d4-8b431470d790`). There, as in Milne's
Theorems 16.21 and 16.26(a), triangular splitting proceeds by induction
on a finite normal series. At the last step the quotient extension is
pulled back along a section built earlier, and this statement provides
the section of that pulled-back extension. The module contains no proof
of the proposition.
