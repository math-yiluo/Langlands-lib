# Statement: kernels of torus maps through which every root factors are central

Authors: Worker 1428 and Worker 1416.

This module states one unproved proposition, the `Prop`-valued `def`
`Langlands.GroupScheme.SplitTorusKernelCentralityStatement` with one universe
parameter `u`. Nothing is proved here, and no other declaration is
introduced.

The module imports `Langlands.GroupScheme.Rational.Characters`,
`Langlands.GroupScheme.Torus.Weights` and
`Langlands.GroupScheme.Torus.KernelCocharacters`. It reuses by name the
Library declarations `GroupScheme`, `CommGroupScheme`,
`CommGroupScheme.groupHom`, `CommGroupScheme.kernelι`, `IsSplitTorus`,
`roots`, `characterLattice` and `IsCentral`.

## The statement

```lean
def SplitTorusKernelCentralityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T T' : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp →
    ∀ (i : T.toGrp ⟶ G) (t : T ⟶ T'),
      (∀ α ∈ roots i, ∃ α' : characterLattice T', α = t ≫ α') →
        IsCentral (CommGroupScheme.groupHom (CommGroupScheme.kernelι t) ≫ i)
```

In words: let `k : Type u` be an arbitrary field (no perfectness,
separable-closedness or characteristic hypothesis). Let `G` be a group scheme
over `Spec k` that is smooth, affine and has connected underlying space. Let
`T` be a split torus over `k`, let `i : T ⟶ G` be any homomorphism of group
schemes (it need not be a closed immersion or a maximal torus), let `T'` be
any commutative group scheme over `k`, and let `t : T ⟶ T'` be a homomorphism
of commutative group schemes. Suppose every root `α` of `i` is the pullback
`t ≫ α'` of some character `α'` of `T'`. Then the actual scheme kernel of
`t` is central in `G` after composing with `i`.

The ingredients mean the following.

- `roots i` (`Torus/Weights.lean`) is the set of nonzero characters `χ` of
  `T` whose weight space in the actual Lie algebra `Lie(G)(k)`, for the
  adjoint action of `T` through `i`, is nonzero. The Library proves
  `relativeRoots i = roots i` (`relativeRoots_eq_roots`,
  `Rational/RelativeRoots.lean`).
- `t ≫ α'` is the composite character `T ⟶ T' ⟶ 𝔾_m`, that is, the image of
  `α'` under the character map `X(t)`.
- `CommGroupScheme.kernel t` (`Torus/KernelCocharacters.lean`) is the actual
  scheme kernel of `t`, and `CommGroupScheme.kernelι t` is its inclusion into
  `T`. It is not replaced by its reduced subscheme or its rational points;
  for example it may be `μ_p` in characteristic `p`.
- `IsCentral f` (`Rational/Characters.lean`) says that for every test scheme
  `U` over `Spec k` and every `U`-point `x` of the source, `x ≫ f` lies in
  the scheme-theoretic centre `center G` on `U`: every restriction of it
  commutes with every point of `G` over every `U'` above `U`.

The hypotheses are those of the published
`RootAnnihilatorCentralityStatement` (`Rational/RootAnnihilatorCentralityStatement.lean`):
smoothness, affineness and connectedness of `G`; reductivity of `G` and
maximality of `i` are not assumed. That published statement treats the image
of one cocharacter `ν` with `⟨α, ν⟩ = 0` for all roots; the present statement
treats the kernel of an arbitrary homomorphism `t`, which can be finite and
nonsmooth, so it is not a consequence of the cocharacter statement.

## Why it is true (derived statement)

The statement is derived, not quoted. Milne treats the case of a split
reductive group with a split maximal torus. Source: J. S. Milne, *Algebraic
Groups* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`; printed page = PDF page − 16.

- Proposition 21.7 (printed p.427): for a reductive group `G` with maximal
  torus `T`, the centre `Z(G)` lies in `T` and equals the kernel of
  `Ad : T → GL(𝔤)`.
- Proposition 21.8 (printed p.427): for a split reductive group, since `T`
  acts on `𝔤` through the roots, `Z(G) = ⋂_α Ker(α : T → 𝔾_m)`, the
  diagonalizable subgroup of `T` with character group `X^*(T)/ℤΦ`.

If every root is `t ≫ α'`, every root is trivial on the kernel of `t`, so
`Ker(t) ⊆ ⋂_α Ker(α)`, which Milne's 21.8 identifies with `Z(G)` in the
reductive case. The Lean statement needs only that `i` maps
`⋂_α Ker(α)` into `Z(G)` for smooth connected affine `G`, and this holds without
reductivity by the following argument (not Milne's proof of 21.7, which uses
reductivity).

1. `D = ⋂_{α ∈ roots i} Ker(α)` is a closed subgroup of the split torus `T`,
   hence diagonalizable (Milne Theorem 12.9(c), printed p.233), and
   `Ker(t) ⊆ D`.
2. `T` acts on `Lie(G)` through `i`, and `Lie(G)` is the direct sum of its
   weight spaces, whose nonzero weights are the roots (the Library proves the
   internal direct sum as `isInternal_weightSpace_of_isSplitTorus`). Every
   weight is trivial on `D`, so `D` acts trivially on `Lie(G)`.
3. The subgroup `G^D` of points fixed by the conjugation action of `D` is
   smooth. Milne Theorem 13.1 (printed p.254) proves this for linearly
   reductive group varieties, which are smooth, so it does not cover a
   nonsmooth `D`. The Library's `Diagonalizable.FixedSubgroupSmoothStatement`
   (`Torus/DiagonalizableFixedSmoothStatement.lean`, proved as
   `Diagonalizable.FixedSmooth.fixedSubgroupSmooth`) covers every
   diagonalizable group `D(Λ)` with `Λ` finitely generated, torsion
   included, acting on a smooth affine group.
4. `Lie(G^D) = Lie(G)^D` (Milne Proposition 10.34, printed p.197, applied to
   the centralizer `C_G(D) = G^D`; Milne states it for an algebraic subgroup
   `H` of `G`, and the same computation applies to the conjugation action of
   `D` through `i`). This is all of `Lie(G)` by step 2.
5. A smooth closed subgroup of the smooth connected group `G` with the same
   Lie algebra is all of `G` (the Library's `lieSubgroupEquality`, module
   `Lie/SubgroupEqualityProof`). So `G^D = G`, that is, `D` and hence
   `Ker(t)` are central.

The published proof of `RootAnnihilatorCentralityStatement` follows this
pattern for a cocharacter image, and the Library's
`KernelCentralizerStructureStatement` (`Rational/RootSubgroupStructureStatement.lean`)
treats the centralizer of the kernel of one character. These are suggestions
for a proof, not part of the statement.

The official Milne errata snapshot of 2026-11-02
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for 10.34,
12.9, 13.1, 21.7 or 21.8.

## Use

This statement is meant to supply the centrality of the kernel `N = Ker(t)`
in a proof of the planned statement `SplitCentralTorusQuotientStatement`
(statement task `2ea05a8b-453e-49c8-8d20-9b2ad61ac047`; not yet in the
Library when this module was written), where `G` is connected reductive, `i`
is a split maximal torus and `t` is an isogeny of split tori. Centrality
gives normality of `N`, so the published `NormalSubgroupQuotientStatement`
(`GroupScheme/NormalSubgroupQuotientStatement.lean`) applies.
