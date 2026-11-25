# Semisimple groups and commutative normal subgroups

`Langlands.GroupScheme.SemisimpleCommutativeNormalSubgroupStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves nothing.

## Statement

The proposition says: for every field `k : Type u` and every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` with `Smooth G.X.hom`,
`IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`, writing
`NoCommutativeNormal` for the local proposition

```text
∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
  IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
    IsCommMonObj H.X → (SubgroupFunctor.range j).IsNormal →
      SubgroupFunctor.range j = ⊥,
```

the proposition is

```text
(IsSemisimple G → NoCommutativeNormal) ∧
  (PerfectField k → NoCommutativeNormal → IsSemisimple G).
```

In words: let `G` be a smooth connected affine group scheme over a field `k`.
If `G` is semisimple, then every smooth connected commutative normal closed
subgroup of `G` is trivial. Conversely, if `k` is perfect and every smooth
connected commutative normal closed subgroup of `G` is trivial, then `G` is
semisimple.

Every ingredient is an existing declaration, used without change:

- `IsSemisimple G` (from `Langlands.GroupScheme.Reductive.Semisimple`) is a
  structure with the two fields `IsConnectedReductive G` and `HasFiniteCenter G`:
  `G` is connected reductive, and some closed subgroup `z : Z ⟶ G` has the full
  scheme-theoretic centre functor `center G` as image, with `Z.X.hom` finite.
  `IsConnectedReductive G` (from `Langlands.GroupScheme.Reductive.Basic`) says
  that `G` is smooth, affine and connected and that every smooth connected
  unipotent normal closed subgroup of `G_{k̄}` is trivial, where
  `k̄ = AlgebraicClosure k`.
- `IsClosedSubgroup j` says that the morphism of schemes underlying `j` is a
  closed immersion. `SubgroupFunctor.range j` is the image subgroup functor of
  `j` on all test schemes over `Spec k`; `IsNormal` is normality on every test
  scheme, and `⊥` is the trivial subgroup functor.
- `IsCommMonObj H.X` is Mathlib's class saying that the group law of the group
  object `H.X` is commutative. Since `j` is a monomorphism, `H` is commutative
  exactly when its image in `G` is a commutative subgroup functor.
- `PerfectField k` is Mathlib's class of perfect fields.

The tested subgroups `H` are smooth, so their nilpotent structure plays no role.
The perfectness hypothesis is used only in the converse direction, as in the
source.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

- Proposition 19.3, printed p. 398 (PDF p. 414):

  > PROPOSITION 19.3. Let G be a connected group variety over field k. If G is
  > semisimple, then every smooth connected normal commutative algebraic
  > subgroup is trivial; the converse is true if k is perfect.

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

Remark 19.4, printed p. 398, shows that none of the four conditions on the
subgroup can be dropped: `{±I}` in `SL_2` (characteristic not 2) is smooth,
normal and commutative but not connected; `μ_2` in `SL_2` (characteristic 2) is
connected, normal and commutative but not smooth; the upper unitriangular
subgroup `U_2` of `SL_2` is smooth, connected and commutative but not normal;
and `e × SL_2` in `SL_2 × SL_2` is smooth, connected and normal but not
commutative.

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists
Chapter 19 corrections only on p. 399 (Definitions 19.7 and 19.8) and Chapter 6
corrections only on p. 136 (Example 6.48). None concerns 19.3, 19.4 or 6.44.

The provenance is derived for three reasons:

1. "Semisimple" is the Library's `IsSemisimple` (connected reductive with
   finite centre), not Milne's definition (`R(G_{k^a}) = e`). By Milne 6.44 and
   Proposition 19.10 the two agree for smooth connected affine groups. That
   equivalence is stated separately as
   `SemisimpleRadicalCharacterizationStatement`
   (`Langlands.GroupScheme.Reductive.SemisimpleRadicalCharacterizationStatement`).
2. Milne's "smooth connected normal commutative algebraic subgroup" is a closed
   subgroup `j : H ⟶ G` with `H` smooth, connected and commutative and with
   normal image; "trivial" is `SubgroupFunctor.range j = ⊥`.
3. `k` lies in an arbitrary universe `u`. This is a formalization convention.

## For the proof (not part of this module)

The proof is `semisimpleCommutativeNormalSubgroup` in
`Langlands.GroupScheme.Reductive.SemisimpleCommutativeNormalProof`.

Milne's proof, printed p. 398: "Suppose that G is semisimple, and let H be a
connected normal commutative subgroup variety of G. Then H_{k^a} ⊆ R(G_{k^a}) =
e, and so H = e. For the converse, suppose that k is perfect and that G is not
semisimple. Then R(G) ≠ e, and the last nontrivial term in the derived series
for R(G) is smooth, connected, and commutative (6.19b). It is normal in G
because it is characteristic in R(G) (see 6.19e). Hence G contains a nontrivial
smooth connected normal commutative algebraic subgroup."

In the first step, `H_{k^a}` is a smooth connected commutative, hence solvable,
normal subgroup of `G_{k^a}`. The step "R(G) ≠ e" in the converse uses
Proposition 19.2(a) (`k` perfect). Corollary 6.19, printed p. 129, says, for
`G` affine or smooth: "(b) If G is connected (resp. smooth), then DG is
connected (resp. smooth)" and "(e) DG is a characteristic subgroup of G". The
last nontrivial term `D^n R(G)` is commutative because `D(D^n R(G)) = e`. In
the Library, the radical `R(G)` exists by `solvableRadicalExistence`
(`Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof`), and
Proposition 19.2(a) is stated as `PerfectFieldSemisimpleRadicalStatement`
(`Langlands.GroupScheme.Reductive.PerfectFieldSemisimpleRadicalStatement`).
