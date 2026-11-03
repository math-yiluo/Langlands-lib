# Torus endomorphisms: surjectivity or a closed multiplicative subgroup in the kernel

Author: Worker 1435. Worker 1368 proposed the exact interface. Worker 1369
identified the prerequisite in the Borel normalizer argument and corrected the
distinction between a contained torus and the entire kernel.

This module defines the proposition
`Langlands.GroupScheme.TorusEndomorphismDichotomyStatement.{u}`. It contains no
proof of that proposition.

## Exact statement and conventions

```lean
def TorusEndomorphismDichotomyStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
    ∀ f : T ⟶ T,
      Surjective (CommGroupScheme.groupHom f).hom.hom.left ∨
        ∃ ν : Gm (Spec (CommRingCat.of k)) ⟶ T,
          IsClosedSubgroup (CommGroupScheme.groupHom ν) ∧ ν ≫ f = 0
```

Here `T` and `f` are actual commutative group schemes and their morphisms.
`CommGroupScheme.groupHom` forgets the additive notation on morphisms, and
`.hom.hom.left` extracts the underlying scheme morphism. The first branch is
`AlgebraicGeometry.Surjective` for that morphism.

In the second branch, `ν` is an actual cocharacter over `Spec k`.
`IsClosedSubgroup` from `Reductive.Basic` means that its underlying scheme
morphism is a closed immersion. Thus it exhibits a closed subgroup isomorphic
to `Gm`. The equation `ν ≫ f = 0` is equality of actual morphisms in the
category of commutative group schemes; `0` denotes the trivial homomorphism.
It therefore makes the composite trivial on every test scheme, including
nonreduced tests, and puts this closed copy of `Gm` inside the scheme-theoretic
kernel of `f`.

The sole hypothesis on `T` is the existing `IsTorus T.toGrp` from
`Torus.Lattice`: after some field extension it is isomorphic to a finite
product of copies of `Gm`. The statement adds no splitness, smoothness,
connectedness, affineness, finite-type, reductivity, or structural-theorem
premise. The universe `u` and the characteristic are arbitrary. The empty
product is allowed, so rank zero is included; its endomorphism is surjective.
The second branch makes no assertion that the entire kernel is smooth or
connected. Finite diagonalizable factors in the kernel can prevent these
properties, including nonreduced factors in positive characteristic.

## Original passage and derived generalization

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field* (2017), registered source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The relevant passages are:

- Theorem 17.48 and its proof, printed p.367 (one-based PDF p.383).
- Theorem 12.9(a)–(c), printed pp.233–234 (PDF pp.249–250).
- Definition 12.14 and the paragraph following it, printed p.236 (PDF p.252).
- Theorem 12.18 and Corollary 12.19, printed pp.237–238 (PDF pp.253–254).

In the proof of Theorem 17.48, Milne works over an algebraically closed field.
After arranging that `x` normalizes a maximal torus `T`, he considers the
homomorphism `t ↦ x t x⁻¹ t⁻¹`. When its image is proper, he obtains a
nontrivial torus `S` contained in its kernel. This provides a torus centralized
by `x` for the subsequent induction. Since a torus over an algebraically
closed field is split, a nontrivial such `S` contains a coordinate copy of
`Gm` as a closed subgroup.

The present proposition abstracts that step to every torus endomorphism.
This generalization is derived content, rather than a verbatim numbered
theorem in Milne. Its mathematical justification uses the contravariant
diagonalizable-group equivalence and exactness in 12.9, the finite free
character groups of split tori in 12.14 and the following paragraph, and
splitting over a finite separable extension in 12.18–12.19. Over an
algebraically closed field, these give `T ≅ D(M)` for a finite free abelian
group `M`. An endomorphism corresponds to `f* : M → M`. If `f*` is injective,
exactness makes the corresponding scheme morphism surjective. Otherwise,
because its source and target have the same finite rank, `coker(f*)` has
positive free rank and admits a surjection onto `ℤ`. Dualizing gives a closed
immersion `Gm = D(ℤ) → D(coker(f*)) = ker(f)`, and its composite into `T`
is the required `ν`. This argument also explains why the whole kernel need
not be a torus.

The registered author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
has been checked. Its Chapter 12 and Chapter 17 entries do not alter the
passages cited above.

## Formalization boundary

The character argument above explains the provenance and intended truth of
the statement. A Lean proof remains a separate obligation. In particular, no
torus-splitting theorem or character-duality theorem is assumed as an extra
premise of this proposition. This module supplies only the dichotomy target
for later use; it establishes no Borel normalizer or connectedness result.
