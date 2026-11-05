# Statement: the central quotient of a split reductive group by the kernel of a torus isogeny

Authors: Worker 1428, Worker 1404.

This module states one unproved proposition, the `Prop`-valued `def`
`Langlands.GroupScheme.SplitCentralTorusQuotientStatement` with one universe
parameter `u`. Nothing is proved here.

The module imports `Langlands.GroupScheme.Torus.Maximal` and
`Langlands.GroupScheme.CentralIsogeny.Basic`. It introduces no other
declaration. It reuses by name the Library declarations `GroupScheme`,
`CommGroupScheme`, `CommGroupScheme.groupHom`, `IsConnectedReductive`,
`IsConnectedReductive.isAffineHom`, `IsSplitTorus`, `IsMaximalTorus`,
`characterLattice`, `cocharacterLattice`, `roots` and `IsCentralIsogeny`.

## The statement

```lean
def SplitCentralTorusQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T T' : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → IsSplitTorus T'.toGrp →
    ∀ i : T.toGrp ⟶ G, IsMaximalTorus i → ∀ t : T ⟶ T',
      Function.Injective (fun χ : characterLattice T' => t ≫ χ) →
      Function.Injective (fun ν : cocharacterLattice T => ν ≫ t) →
      (haveI := hG.isAffineHom; ∀ α ∈ roots i, ∃ α' : characterLattice T', α = t ≫ α') →
        ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (_ : IsConnectedReductive Q)
          (q : G ⟶ Q) (i'' : T'.toGrp ⟶ Q),
          IsMaximalTorus i'' ∧ IsCentralIsogeny q ∧ i ≫ q = CommGroupScheme.groupHom t ≫ i''
```

In words: let `k : Type u` be an arbitrary field, with no perfectness,
separable-closedness or characteristic hypothesis. Let `G` be an actual
connected reductive group over `Spec k`, and let `i : T ⟶ G` be a maximal
torus with `T` split. Let `T'` be another split torus and `t : T ⟶ T'` a
homomorphism of commutative group schemes. Suppose that

- the character map `X(t) : X(T') → X(T)`, `χ ↦ t ≫ χ`, is injective;
- the cocharacter map `Y(t) : Y(T) → Y(T')`, `ν ↦ ν ≫ t`, is injective;
- every root `α` of `i` is `t ≫ α'` for some character `α'` of `T'`, that is,
  every root lies in the image of `X(t)`.

Then there are an actual connected reductive group `Q` over `Spec k`, a
homomorphism `q : G ⟶ Q` and a homomorphism `i'' : T' ⟶ Q` such that

- `IsMaximalTorus i''`: `i''` is a maximal torus of `Q`;
- `IsCentralIsogeny q`: the morphism underlying `q` is finite, flat,
  surjective and locally of finite presentation, and the full
  scheme-theoretic kernel of `q` (on all test schemes, nonreduced ones
  included) is central;
- `i ≫ q = groupHom t ≫ i''`: `q` maps `T` into the torus `i''(T')` through `t`.

Conventions, all taken from the Library:

- `characterLattice T = (T ⟶ Gm)` and `cocharacterLattice T = (Gm ⟶ T)` are
  the actual character and cocharacter groups. Composition `t ≫ χ` and
  `ν ≫ t` is composition of homomorphisms of commutative group schemes.
- `roots i` (module `Torus.Weights`) is the set of nonzero characters of `T`
  with a nonzero weight space in the actual Lie algebra `Lie(G)(k)`. It needs
  the instance `IsAffineHom G.X.hom`, which the statement takes from
  `hG.isAffineHom` by `haveI`, as the published statements of
  `Reductive.SplitClassificationStatement` do.
- `IsMaximalTorus i` (module `Torus.Maximal`): `T` is a torus, `i` is a closed
  subgroup, and `i` does not factor through a strictly larger closed torus.
- `IsCentralIsogeny q` (module `CentralIsogeny.Basic`) is compared with
  Milne's central isogenies in `CentralIsogeny/Basic.md`.

Only existence is stated. The statement does not identify the kernel of `q`
or say that `Q` is unique.

## Provenance

This proposition is derived; Milne states no result in exactly this form. It
is the quotient step of a proof of the published
`SplitCentralIsogenyExistenceStatement` (Milne Theorem 23.9, central case)
that avoids Milne's root-group construction. Given a central isogeny of root
data `f`, one realizes `f` on tori by `t`, divides `G` by the kernel of `t`
using this statement, and identifies the quotient `Q` with the target group by
the Isomorphism Theorem. The hypotheses here are the parts of a central
isogeny of root data that this step needs.

All references are to J. S. Milne, *Algebraic Groups* (2017). Printed page =
PDF page − 16.

1. **`t` is an isogeny of tori.** Milne notes after Definition 23.1 (printed
   p.484, PDF p.500) that a homomorphism of lattices is injective with
   finite cokernel exactly when it and its transpose are injective. Over split
   tori the pairing is perfect, so the two injectivity hypotheses say that
   `X(t)` is injective with finite cokernel. By Theorem 12.9 (printed p.233,
   PDF p.249), the anti-equivalence between diagonalizable groups and finitely
   generated commutative groups with its exactness, `t` is then surjective and
   its kernel `N` is the finite diagonalizable group with character group
   `X(T) / X(t)(X(T'))`.
2. **`N` is central.** Proposition 21.7 (printed p.427, PDF p.443) shows that
   the centre `Z(G)` lies in `T` and is the kernel of the adjoint action of `T`.
   Proposition 21.8 (same page) computes it for a split group: `Z(G)` is the
   diagonalizable subgroup of `T` with character group `X(T) / ℤΦ`, that is,
   the intersection of the kernels of the roots. Chapter 21 works over an
   arbitrary field (printed p.424, PDF p.440). Every root lies in the image
   of `X(t)`, so `ℤΦ ⊆ X(t)(X(T'))` and `N ⊆ Z(G)`. Milne's centre is the
   scheme-theoretic centre, so `N` is central as a subgroup scheme, as
   `IsCentralIsogeny` requires.
3. **The quotient.** Theorem 5.14 (printed p.102, PDF p.118) gives a quotient
   map `q : G → Q = G/N` with kernel `N`. It is faithfully flat, and it is
   finite because `N` is finite, so `q` is a central isogeny in the sense of
   Definition 18.1 (printed p.387, PDF p.403) and of `IsCentralIsogeny`.
   `Q` is smooth, connected and affine because `G` is. It is reductive in the
   sense of `IsConnectedReductive`, whose unipotent-radical condition is
   checked over an algebraic closure `k̄`. The base change `G_k̄ → Q_k̄` is
   again a quotient map with kernel `N_k̄`. The reduced identity component of
   the inverse image of the unipotent radical of `Q_k̄` is a smooth connected
   normal subgroup of `G_k̄`. It maps onto that radical with finite kernel.
   Each of its tori maps to a torus in a unipotent group, hence lies in the
   finite kernel, hence is trivial. It is therefore unipotent by
   Theorem 20.1(a) (printed p.407, PDF p.423), hence trivial because `G` is
   reductive, and so the unipotent radical of `Q_k̄` is trivial.
4. **The torus `T'` in `Q`.** The composite `T → G → Q` kills `N`, the kernel
   of the quotient map `t : T → T'`, so it factors as `t` followed by a
   homomorphism `i'' : T' → Q`. This is the equation
   `i ≫ q = groupHom t ≫ i''`. The kernel of `T → Q` is `T ∩ N = N`, so `i''`
   is an isomorphism of `T'` onto the image `q(T)`. It remains to see that
   `q(T)` is a maximal torus of `Q`. Proposition 17.20 (printed p.357,
   PDF p.373) shows that the image of a maximal torus under a quotient map of
   connected group varieties is a maximal torus. Section 17b, which contains
   it, works over an algebraically closed field (printed p.353, PDF p.369),
   so it is applied to `q_k̄ : G_k̄ → Q_k̄`. Theorem 17.82 (printed p.379,
   PDF p.395) says that a torus in a group variety over `k` is maximal if and
   only if it is maximal after any extension of the base field. So `T_k̄` is
   maximal in `G_k̄`, its image `q(T)_k̄` is maximal in `Q_k̄`, and `q(T)` is
   maximal in `Q`. Hence `i''` is a maximal torus of `Q`.

## Sources

- J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
  over a Field* (Cambridge University Press, 2017), source
  `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Printed page = PDF page − 16.
- Milne's official errata list for this book, snapshot source
  `milne-2017-algebraic-groups-errata-2026-11-02`. It has no entry for the
  printed pages cited above (pp.102, 233, 353, 357, 379, 387, 407, 424, 427
  and 484).
