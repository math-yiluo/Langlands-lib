# Split tori over an arbitrary base

Author: Worker 207.

This module constructs the split torus `𝔾_m^I` over an arbitrary scheme `S` as an
actual group scheme. It defines the predicate "is a split torus" for group schemes
over `S` and proves the basic closure properties needed later: invariance under
isomorphism, `𝔾_m` itself, binary products, smoothness and arbitrary base change.
All declarations are in the namespace `Langlands.GroupScheme`. Here
`GroupScheme S` is the published `Grp (Over S)`.

## Sources

- Milne, *Algebraic Groups* (2017), Definition 12.14, printed p.236 (PDF p.252):
  "An algebraic group over k is a torus if it becomes isomorphic to a finite
  product of copies of Gm over some field containing k. A torus over k is split
  if it is isomorphic to a product of copies of Gm over k."
  Source ID `milne-2017-algebraic-groups`, SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
- Conrad, *Reductive group schemes* (2014), Appendix B.1, p.280: for a finitely
  generated `ℤ`-module `M`, `D_S(M) = Spec(O_S[M])`, and a group of multiplicative
  type "is split (or diagonalizable) over S if G ≃ D_S(M) for some M".
  Definition 3.1.1, p.81: "An S-torus is an S-group T → S of multiplicative type
  with smooth connected fibers." Source ID `conrad-2014-reductive-group-schemes`,
  SHA-256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.

## Conventions and comparison with the sources

`splitTorus S I`, for `I : Type u` with `[Finite I]`, is
`pi fun _ : I => (Gm S).toGrp`. This is the categorical product in `GroupScheme S`
of `I` copies of the published multiplicative group scheme
`Gm S = Spec(O_S[x, x⁻¹])`. It is the product of copies of `Gm` in Milne's
Definition 12.14, now over any base scheme.

`IsSplitTorus G` means that there exist a finite index type `I` (in the universe
of `S`) and an isomorphism of group schemes over `S` between `G` and
`splitTorus S I`. The following points compare this with the sources.

- **Finite rank.** Milne's split tori are algebraic groups, so the product has
  finitely many factors. Here finiteness is an explicit hypothesis, and the rank
  is one global index type.
- **General base.** Over a general base this is the split torus `D_S(ℤ^I)` of
  Conrad B.1, the diagonalizable group of the free module `ℤ^I`. Its coordinate
  ring is `O_S[ℤ^I]`, the Laurent polynomials in `I` variables, which is the
  product of `I` copies of `Gm`. This module does not construct `D_S(M)` for a
  general `M`. It does not prove this identification either: it works with the
  product of copies of `Gm` directly.
- **No torus hypothesis.** The predicate has no separate hypothesis that `G` is a
  torus, unlike Milne's wording "a torus over k is split if". Any group scheme
  isomorphic to `𝔾_m^I` is a torus in either source's sense, so nothing is lost.
  The non-split notion of an `S`-torus (Conrad 3.1.1, or Milne 12.14 over a
  field) is not formalized here.
- **Isomorphism type.** The isomorphism is one of group objects in `Over S`,
  that is, of group schemes over `S`, as in both sources.

## Isomorphisms and point models

- `isoPointsEquiv e T` is the multiplicative equivalence on `T`-points induced
  by a group-scheme isomorphism `e`. On a point it is postcomposition with
  `e` (`isoPointsEquiv_apply`).
- `isoOfPointModels` is a convenience wrapper around the published
  `GroupScheme.isoOfPoints`, the group-valued Yoneda reconstruction. Suppose two
  group schemes `G` and `H` have natural point equivalences `eG T` and `eH T` to
  the same model `M T` of groups. Naturality means compatibility with one family
  of restriction homomorphisms `res`. Then `G ≅ H`. The lemmas
  `isoOfPointModels_hom` and `isoOfPointModels_inv` state that the resulting
  isomorphism is the identity on the models.

## Points of split tori

- `splitTorus.unitsRestrict I a` restricts a family `I → Γ(T, 𝒪_T)ˣ` along a
  morphism `a : T' ⟶ T` of test schemes. It applies the global-sections map
  `a.left.appTop` to each unit.
- `splitTorus.pointsEquiv I T : (T ⟶ (splitTorus S I).X) ≃* (I → Γ(T, 𝒪_T)ˣ)`
  composes the published product comparison `piPointsEquiv` with
  `Gm.pointsEquiv` for every factor. `pointsEquiv_apply` gives its value on the
  `i`-th coordinate. `pointsEquiv_naturality` states compatibility with
  `unitsRestrict`, for arbitrary (not necessarily affine) test schemes.
- `splitTorus.affinePointsEquiv I f`, for `f : Spec R ⟶ S`, identifies the
  points over the affine test scheme `Over.mk f` with `I → Rˣ`. It uses
  `Gm.affinePointsEquiv` in each factor.

## Standard isomorphisms

The three isomorphisms below are all built with `isoOfPointModels` from the
point models above. That is, they are built on all test schemes, not only on
affine ones.

- `splitTorus.gmIso S : (Gm S).toGrp ≅ splitTorus S PUnit` says that `𝔾_m` is
  the split torus of rank one. It uses `MulEquiv.piUnique` on the model.
- `splitTorus.prodIso I J : splitTorus S I ⊗ splitTorus S J ≅
  splitTorus S (I ⊕ J)` identifies the cartesian monoidal product with the split
  torus on the disjoint union. The model on the left is
  `prodPointsEquiv I J T`, which combines the published `productPointsEquiv`
  with `sumArrowMulEquiv`, the multiplicative form of
  `Equiv.sumArrowEquivProdArrow`. Its naturality is
  `prodPointsEquiv_naturality`.
- `splitTorus.baseChangeIso b I : (baseChange b).obj (splitTorus S I) ≅
  splitTorus S' I`, for any `b : S' ⟶ S`, uses the published
  `GroupScheme.baseChangePointsEquiv`. A `T`-point of the base change is a point
  of the original torus on `T` regarded over `S`. The point model is
  `baseChangePointsEquiv b I T`, with naturality
  `baseChangePointsEquiv_naturality`.

## Results about `IsSplitTorus`

- `IsSplitTorus.of_iso` and `IsSplitTorus.iso_iff`: the predicate is invariant
  under isomorphism of group schemes over `S`.
- `isSplitTorus_splitTorus`: `splitTorus S I` is split.
- `isSplitTorus_gm`: `𝔾_m` is split.
- `IsSplitTorus.tensor`: the product of two split tori is split, with ranks
  adding (`I ⊕ J`).
- `smooth_splitTorus` and `IsSplitTorus.smooth`: split tori are smooth over the
  base. This uses the published `smooth_pi`, `smooth_gm` and
  `smooth_of_over_iso`.
- `IsSplitTorus.baseChange`: split tori stay split after arbitrary base change,
  with the same index type.

## Scope

The module defines the split notion only. It does not formalize general tori,
groups of multiplicative type, character or cocharacter lattices, or the
anti-equivalence with free `ℤ`-modules. It does not prove that the rank is
unique, or that a split torus over a field is connected, affine or reductive.
Those are separate parts of the host program.
