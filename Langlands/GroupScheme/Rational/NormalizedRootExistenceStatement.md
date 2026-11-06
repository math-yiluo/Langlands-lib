# Existence of normalized simple-root data over arbitrary fields

Author: Worker 1354.

`Langlands.GroupScheme.NormalizedRootExistenceStatement.{u}` is a
proposition definition. For every field `k : Type u`, actual group scheme
`G : GroupScheme (Spec (CommRingCat.of k))`, affineness instance
`[IsAffineHom G.X.hom]`, and supplied `p : SplitPinning G`, it asserts exactly

```lean
Nonempty p.NormalizedSimpleRootParametrizations ∧
  Nonempty p.SimpleReflectionRepresentatives
```

The file states this target and does not prove it. Its only import is the
published `Langlands.GroupScheme.Rational.SteinbergRootProduct`; both
conclusions use that module's data types unchanged.

The affineness instance provides the setting for the actual Lie constructions.
The supplied pinning already includes connected reductivity, a split maximal
torus and its inclusion into `G`, a finite reduced root datum on that torus's
actual character and cocharacter lattices satisfying `IsRootDatumOf`, a base,
and linear trivializations of the actual simple-root Lie weight spaces.
In particular, no root parametrization is part of this hypothesis. There is
no additional restriction on the characteristic, cardinality, or perfection
of `k`. The field and group schemes retain arbitrary universe `u`. Existence
of a pinning for a general group is not asserted.

The first conclusion supplies a family indexed by `a : p.base.support`.
Each `p.NormalizedRootParametrization a` has the following meaning.

- Its `hom` is an actual group-scheme homomorphism from the standard additive
  group `VectorGroup.groupScheme (CommRingCat.of k) 1` to `G`.
- Its `represents` field identifies the complete subgroup functor
  `RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)` with the range
  of this homomorphism, and requires a monomorphism over `Spec k`.
  Thus on every test scheme `T` over `Spec k`, its scalar values are exactly
  the points of the intrinsic root subgroup. The monomorphism makes the
  scalar parameter unique. This includes nonreduced and nonaffine tests.
- Its `isClosedSubgroup` field requires the underlying inclusion to be a
  closed immersion.
- Its `torus_equivariant` field requires
  `t x_a(c) t⁻¹ = x_a(a(t)c)` on every such `T`, every torus point `t`,
  and every `c : Γ(T.left, ⊤)`. Here `x_a(c)` uses
  `VectorGroup.scalarPoint` and `a(t)` uses `VectorGroup.charValue`, with
  the actual root character `p.rootDatum.root a`.
- Its `derivative` field requires
  `Lie.targetMapLinear hom (CommRingCat.of k) (VectorGroup.standardEpsilon k)`
  to equal `p.pinning.rootVector a`. The source vector is the actual
  dual-number identity-kernel point with epsilon coefficient one. The target
  vector is the image of `1` under the supplied simple-root Lie
  trivialization, included in the actual Lie algebra.

The second conclusion supplies one `p.SimpleReflectionRepresentative a`
for each simple root. This consists of a rational point of `G`, an actual
automorphism `torusAut : p.torus ≅ p.torus`, and `IsNormalizingPoint`
for that point and automorphism. The latter says that conjugation by the
point restricts to `torusAut` on the given torus inclusion. Its final field
is `characterAut torusAut = p.rootDatum.reflection a`. The character action
is the Library's inverse-automorphism convention:
`characterAut torusAut χ = torusAut.inv ≫ χ`.
The existential witnesses are already available for every root from
`p.isRootDatum.2.2`; restricting to the simple-root indices and choosing
those witnesses yields the asserted representative family. This observation
does not discharge the first conclusion.

The original source for the substantial existence assertion is A. Borel and
T. A. Springer, *Rationality properties of linear algebraic groups II* (1968),
§§8.1–8.2, printed pp.481–482 (PDF pp.39–40), registered as
`borel-springer-1968-rationality-properties-ii`. Section 8.1 gives the
isomorphism from the additive group onto the root subgroup and its torus
equivariance identity. Theorem 8.2 and its proof show that these maps can be
defined over the base field when the maximal torus is split there. Those
passages do not impose an infinite-field or perfect-field assumption.

The present target is a derived scheme-theoretic and Lie-normalized
translation of those passages. It includes two substantive comparisons.
First, the classical root subgroup must be identified with the Library's
intrinsic orbit-extension functor. In the forward direction, equivariance
provides the required extension by the formula `z ↦ x_a(zc)`, with identity
value at zero, over every test scheme. The converse must identify every
point admitting such an extension with the classical root subgroup, using
the split reduced root structure, for example through its rank-one
centralizer and contracting action. This comparison must hold as subgroup
functors on all scheme tests; equality on rational or geometric points
alone does not establish it. Once the subgroup schemes are identified, the
source's additive-group isomorphism and the closed root-subgroup inclusion
give the required representation and closedness.

Second, the differential of that isomorphism must identify the additive
tangent line with the actual simple-root Lie weight space. It then sends
epsilon to a nonzero vector `v` in that line. The chosen pinning vector is
`c • v` for a unique nonzero scalar `c` in `k`. Precomposing the
parametrization with the additive-group automorphism `z ↦ cz` gives the
required derivative. This rescaling preserves its full subgroup image,
closedness, and torus equivariance, in every characteristic. Identification
with the actual dual-number differential and weight space is part of this
translation. Neither this comparison nor the whole-functor comparison is
proved by the imported supplied-data construction or by this statement file;
they belong to a proof of this exact target. No such comparison is assumed
as an additional premise here.

R. Steinberg, *Regular elements of semi-simple algebraic groups* (1965),
§7, printed pp.66–68 (PDF pp.19–21), registered as
`steinberg-1965-regular-elements-semisimple-groups`, provides the later
ordered-product context. Its Lemma 7.14 uses a normalization involving
rank-one representatives; it is not the literal source of the present
Lie-vector normalization. The two families asserted here are precisely
the supplied inputs to `SplitPinning.steinbergProduct` once an ordering
of the simple roots is chosen. The target imposes no further relation
between the families, braid relations, or Galois compatibility.

This statement establishes no cross-section geometry, invariant-quotient
comparison, or rational lifting result, and does not infer splitness from
quasi-splitness. The parent `QuasiSplitSteinbergQuotientStatement` pair,
every pair it imports, and the `SteinbergRootProduct` pair are unchanged.
