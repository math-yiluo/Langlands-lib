# Trivial radical and quotient by the radical over a perfect field

`Langlands.GroupScheme.PerfectFieldSemisimpleRadicalStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves nothing.

## Statement

The proposition says: for every field `k : Type u` with `[PerfectField k]` and
every group scheme `G : GroupScheme (Spec (CommRingCat.of k))` with
`Smooth G.X.hom`, `IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`,

```text
(HasTrivialSolvableRadical G → IsSemisimple G) ∧
  ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G),
    IsSolvableRadical r →
      ∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
        IsAffineHom Q.X.hom →
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q →
            IsSemisimple Q.
```

In words: let `G` be a smooth connected affine group scheme over a perfect field
`k`.

1. If every smooth connected solvable normal closed subgroup of `G` over `k` is
   trivial, that is, `R(G) = e`, then `G` is semisimple.
2. If `r : R ⟶ G` represents the radical `R(G)` over `k`, then every affine
   fppf quotient `q : G ⟶ Q` of `G` with kernel `R(G)` is semisimple. So
   `G/R(G)` is semisimple.

Every ingredient is an existing declaration, used without change:

- `IsSemisimple G` (from `Langlands.GroupScheme.Reductive.Semisimple`) is a
  structure with the two fields `IsConnectedReductive G` and `HasFiniteCenter G`:
  `G` is connected reductive, and some closed subgroup `z : Z ⟶ G` has the full
  scheme-theoretic centre functor `center G` as image, with `Z.X.hom` finite.
  `IsConnectedReductive G` (from `Langlands.GroupScheme.Reductive.Basic`) says
  that `G` is smooth, affine and connected and that every smooth connected
  unipotent normal closed subgroup of `G_{k̄}` is trivial
  (`HasTrivialUnipotentRadical`), where `k̄ = AlgebraicClosure k`.
- `HasTrivialSolvableRadical G` (from
  `Langlands.GroupScheme.Rational.SolvableRadicalQuotient`) says: for every
  group scheme `H` over `Spec k` and every closed subgroup `j : H ⟶ G`
  (`IsClosedSubgroup j`) with `H` smooth, connected and solvable
  (`IsSolvableGroupScheme H`) and with normal image `SubgroupFunctor.range j`,
  that image is `⊥`. It does not choose a radical.
- `IsSolvableRadical r` (from `Langlands.GroupScheme.Rational.LeviSubgroup`) is a
  structure with the fields: `r` is a closed immersion (`IsClosedSubgroup r`);
  `R` is smooth, connected and solvable; `SubgroupFunctor.range r` is normal;
  and this image contains the image of every closed subgroup of `G` over `k`
  with these four properties. So `r` represents Milne's radical `R(G)`.
- `IsSolvableGroupScheme H` (from `Langlands.GroupScheme.Absolute.Borel`) says
  that the abstract group of points of the base change of `H` to the algebraic
  closure of its base field, over that algebraic closure, is solvable. For
  smooth affine groups this agrees with Milne's Definition 6.26 of solvability,
  by Milne 6.31, 6.30, 6.20(b) and 6.21, as explained in `Absolute/Borel.md`.
  That equivalence is not formalized. All groups tested here are smooth.
- `RelativeRoot.IsFppfQuotient N q` (from
  `Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`) says that the
  morphism of schemes underlying `q` is flat, surjective and locally of finite
  presentation, and that the image of the kernel inclusion `kernelι q` is the
  subgroup functor `N`. Here `N = SubgroupFunctor.range r`.
- `PerfectField k` is Mathlib's class of perfect fields.

Part 2 quantifies over every representative `r` and every affine fppf quotient
`q`; it does not assert that either exists. The Library theorem
`solvableRadicalExistence`
(`Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof`) supplies `r`.
Milne's quotient `G/R(G)` is affine (Proposition 5.29, printed p. 105: "The
quotient G/H (in the sense of 5.20) is affine if G is affine and H is normal."),
so the hypothesis `IsAffineHom Q.X.hom` is satisfied by it.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

- Proposition 19.2, printed p. 398 (PDF p. 414):

  > PROPOSITION 19.2. Let G be a connected group variety over a perfect field
  > k.
  > (a) If R(G) = e, then G is semisimple.
  > (b) The quotient G/R(G) is semisimple.

- Semisimplicity, Chapter 19, printed p. 397 (PDF p. 413): "Recall (6.44) that
  an algebraic group over a field k is said to be semisimple if it is smooth and
  connected and G_{k^a} has trivial radical." The radical is defined in 6.44,
  printed p. 135 (PDF p. 151): "G contains a largest connected solvable normal
  subgroup variety (6.42). This is called the radical R(G) of G."
- Conventions: 1.26, printed p. 13 (PDF p. 29): "group variety" means "smooth
  algebraic group". Printed p. 162 (PDF p. 178), before Chapter 9: "By
  'algebraic group' we shall mean 'affine algebraic group' and by 'group
  variety' we shall mean 'affine group variety'." The `IsAffineHom G.X.hom`
  hypothesis records this convention, which applies to Chapter 19.

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists
Chapter 19 corrections only on p. 399 (Definitions 19.7 and 19.8) and Chapter 6
corrections only on p. 136 (Example 6.48). None concerns 19.2 or 6.44.

The provenance is derived for four reasons:

1. "Semisimple" is the Library's `IsSemisimple` (connected reductive with
   finite centre), not Milne's definition (`R(G_{k^a}) = e`). By Milne 6.44 and
   Proposition 19.10 the two agree for smooth connected affine groups. That
   equivalence is stated separately as
   `SemisimpleRadicalCharacterizationStatement`
   (`Langlands.GroupScheme.Reductive.SemisimpleRadicalCharacterizationStatement`),
   which was submitted for review as candidate
   `8ee78533-710c-447c-b24d-5348ae0b7b21` and was not yet in the Library when
   this unit was written.
2. Milne's `R(G) = e` in (a) is expressed by `HasTrivialSolvableRadical G`, and
   his `R(G)` in (b) by a representative `r` with `IsSolvableRadical r`, as
   explained above.
3. Milne's quotient `G/R(G)` in (b) is expressed by an arbitrary affine fppf
   quotient `q` with kernel `R(G)`. Milne's quotient maps are faithfully flat
   homomorphisms of algebraic groups (Definition 5.5, printed p. 99: "A
   homomorphism of algebraic groups is a quotient map if it is faithfully
   flat."), hence flat, surjective and of finite presentation, and
   Proposition 5.18, printed p. 103, says: "Every normal algebraic subgroup N
   of an affine algebraic group G is the kernel of a quotient map G → Q with Q
   affine."
4. `k` lies in an arbitrary universe `u`. This is a formalization convention.

The statement makes no claim about imperfect fields.

## For the later proof (not part of this unit)

Milne's proof, printed p. 398: "(a) If R(G) = e, then R(G_{k^a}) = R(G)_{k^a} =
e [by 19.1]. (b) Let N be the inverse image of R(G/RG) in G. Then N is a normal
algebraic subgroup of G, and it is an extension e → RG → N → R(G/RG) → e of
smooth connected solvable algebraic groups. Therefore it is smooth, connected,
and solvable (1.62, 5.59, 6.27), and so RG = N. Hence R(G/RG) = e, and G/RG is
semisimple." The last step applies (a) to `G/RG`, a connected group variety.
Proposition 19.1 applies because `k^a/k` is separable algebraic when `k` is
perfect.

A shorter route through the Library: by Proposition 19.1 (stated as
`SeparableAlgebraicSolvableRadicalStatement` in
`Langlands.GroupScheme.Rational.SeparableSolvableRadicalStatement`, submitted
for review as candidate `0d3ee199-1e18-4b34-8f98-5bad8a83466e`), a solvable
radical `r` over a perfect field is geometric (`IsGeometricSolvableRadical r`).
Then the published theorem `IsGeometricSolvableRadical.isSemisimple_quotient`
(`Langlands.GroupScheme.Reductive.CentralTorusSemisimpleQuotientReduction`)
gives Part 2 directly, and Part 1 follows from `SemisimpleRadicalCharacterizationStatement`
Part 1. Proposition 19.1 for `k^a/k` needs `Algebra.IsSeparable k
(AlgebraicClosure k)`, which holds for perfect `k` because `AlgebraicClosure k`
is algebraic over `k`.
