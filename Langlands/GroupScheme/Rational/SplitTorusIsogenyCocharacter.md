# Isogenies of split tori on cocharacters, and killed points of a covering square

Author: Worker 1392.

This module contains one unproved `Prop`-valued statement,
`Langlands.GroupScheme.SplitTorusIsogenyCocharacterStatement`, and four
small proved lemmas comparing killed points in a commutative square. The
statement compares actual integral, rational and real cocharacters along an
isogeny of split tori. The lemmas are the test-scheme comparison between
the kernel of such a torus map and the kernel of a covering map
`π : C ⟶ G`.

## The statement

`SplitTorusIsogenyCocharacterStatement` is a universe-polymorphic
proposition. The Lean file only defines it and contains no proof of it.

### Binders and hypotheses

The universe `u` is arbitrary. The binders range over every `k : Type u`
with `[Field k]`, every pair of commutative group schemes
`A T : CommGroupScheme (Spec (CommRingCat.of k))` and every homomorphism of
commutative group schemes `f : A ⟶ T`. The field can be imperfect or have
positive characteristic.

There are three hypotheses:

- `IsSplitTorus A.toGrp` and `IsSplitTorus T.toGrp`. The published
  predicate from [`Torus.Split`](../Torus/Split.md) says that the
  underlying group scheme is isomorphic to `splitTorus _ I`, the product of
  copies of `𝔾_m` indexed by some finite `I : Type u`.
- `IsIsogeny (CommGroupScheme.groupHom f)`. This is the published predicate
  from `AbelianScheme.Isogeny`: the underlying morphism of schemes
  `(CommGroupScheme.groupHom f).hom.hom.left` is finite, flat and
  surjective. Here `CommGroupScheme.groupHom f : A.toGrp ⟶ T.toGrp` is the
  underlying group-scheme homomorphism.

Every `IsCentralIsogeny` satisfies the second hypothesis through its field
`isIsogeny`. The hypothesis is weaker than central isogeny, so the
statement is stronger than it would be with central isogeny. No hypothesis
mentions cocharacters, so none of the conclusions is assumed.

### Cocharacters and induced maps

The cocharacter lattice `cocharacterLattice T` from
[`Torus.Lattice`](../Torus/Lattice.md) is the type `Gm _ ⟶ T` of
homomorphisms of commutative group schemes from the multiplicative group.
It is written additively with the pointwise group law. The induced maps are
the published ones from
[`Rational.RelativeCentralDirections`](RelativeCentralDirections.md):

- `RealTorusSpace.cocharacterMapInt f : cocharacterLattice A →ₗ[ℤ]
  cocharacterLattice T` sends `ν` to `ν ≫ f`.
- `(RealTorusSpace.cocharacterMapInt f).baseChange ℚ :
  ℚ ⊗[ℤ] cocharacterLattice A →ₗ[ℚ] ℚ ⊗[ℤ] cocharacterLattice T` is its
  rational scalar extension. It is written inline, and no new map is
  defined.
- `RealTorusSpace.cocharacterMapReal f : RealTorusSpace.V A →ₗ[ℝ]
  RealTorusSpace.V T` is by definition
  `(cocharacterMapInt f).baseChange ℝ`. It acts on the published real
  cocharacter spaces `RealTorusSpace.V T = ℝ ⊗[ℤ] cocharacterLattice T`.

### Conclusion

The conclusion is the conjunction of four properties:

1. `Function.Injective (RealTorusSpace.cocharacterMapInt f)`: distinct
   cocharacters of `A` stay distinct after composition with `f`.
2. `Finite (cocharacterLattice T ⧸ LinearMap.range
   (RealTorusSpace.cocharacterMapInt f))`: the cokernel of the integral
   map is finite. The image is a sublattice of finite index. It need not be
   the whole lattice.
3. `Function.Bijective ((RealTorusSpace.cocharacterMapInt f).baseChange ℚ)`:
   the rational map is a linear isomorphism.
4. `Function.Bijective (RealTorusSpace.cocharacterMapReal f)`: the real map
   is a linear isomorphism.

The statement does not assert that cocharacters of `T` lift integrally,
and it does not assert primitivity. For the `p`-th power map
`𝔾_m ⟶ 𝔾_m`, which is finite flat surjective in every characteristic,
the cokernel on cocharacters is `ℤ/pℤ`. The statement also asserts nothing
about the points `A(k) ⟶ T(k)`; a finite surjective morphism of schemes
need not be surjective on `k`-points.

## Killed points of a covering square

The section `KilledPoints` works over an arbitrary base scheme
`S : Scheme.{u}`. It fixes group schemes `C G`, commutative group schemes
`A T`, and homomorphisms `π : C ⟶ G`, `a : A.toGrp ⟶ C`,
`i : T.toGrp ⟶ G` and `f : A ⟶ T`. Each lemma takes the commutative square
`h : a ≫ π = CommGroupScheme.groupHom f ≫ i`, a test object `U : Over S`
and a point `x : U ⟶ A.toGrp.X`. All test schemes are allowed, including
nonreduced ones. The `1` in each formula is the identity point in the
group of points with values in `U`.

- `comp_groupHom_eq_one_iff_of_comp_eq` assumes that the underlying scheme
  morphism `i.hom.hom.left` is a monomorphism. It proves
  `x ≫ (CommGroupScheme.groupHom f).hom.hom = 1 ↔
  (x ≫ a.hom.hom) ≫ π.hom.hom = 1`: a point of `A` is killed by `f`
  exactly when its image in `C` is killed by `π`.
- `mem_range_kernelι_groupHom_iff_of_comp_eq` makes the same assumption.
  It proves the same equivalence for the full scheme-theoretic kernels:
  `x` lies in the range of `kernelι (CommGroupScheme.groupHom f)` exactly
  when `x ≫ a.hom.hom` lies in the range of `kernelι π`. The proof rewrites
  both sides with `mem_range_kernelι_iff` from
  [`CentralIsogeny.Basic`](../CentralIsogeny/Basic.md).
- `comp_groupHom_eq_one_iff_of_comp_eq_of_isClosedSubgroup` and
  `mem_range_kernelι_groupHom_iff_of_comp_eq_of_isClosedSubgroup` replace
  the monomorphism assumption with `IsClosedSubgroup i`, that is,
  `i.hom.hom.left` is a closed immersion. A closed immersion is a
  monomorphism, and the proofs reduce to the two lemmas above.

The proof of the first lemma reads the square on underlying morphisms. If
`x ≫ f = 1`, then `x ≫ a ≫ π = x ≫ f ≫ i = 1 ≫ i = 1`, because the
homomorphism `i` preserves the identity point (`MonObj.one_comp`).
Conversely, if `x ≫ f ≫ i = 1 = 1 ≫ i`, then `x ≫ f = 1`, because `i` is a
monomorphism in `Over S`. That monomorphism is obtained from the one on
underlying schemes by `Over.mono_of_mono_left`.

In the intended application, `π` is the covering map of a supplied
`IsSimplyConnectedCover`, `i` is a maximal split torus of `G`, and `a`
and `f` are a maximal split torus of `C` and the torus map in the
commutative square. `IsMaximalSplitTorus i` contains `IsClosedSubgroup i`
as `hi.1.2`. The lemmas then identify the kernel of `f` on every test
scheme with the part of `A` that lies in the kernel of `π`. The lemmas use
only the square and the closed embedding `i`. They do not identify `A`
with the whole inverse image of the torus of `G`.

## Sources and derived provenance

The statement and its scope come from J. S. Milne, *Algebraic Groups: The
Theory of Group Schemes of Finite Type over a Field* (2017), registered as
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Milne
works over an arbitrary field throughout. Printed page `p` is PDF page
`p + 16`. The relevant passages are:

- Definition 6.6, printed p.126 (PDF p.142): a homomorphism of algebraic
  groups is an isogeny if its kernel is finite and its image has finite
  index.
- The definition of a cocharacter as a homomorphism `𝔾_m → G`, Section
  12.a, printed p.230 (PDF p.246).
- Theorem 12.9, printed pp.233-234 (PDF pp.249-250): `M ↦ D(M)` is a
  contravariant equivalence from finitely generated commutative groups to
  diagonalizable groups, with quasi-inverse `X`, and both functors are
  exact.
- The proof of Proposition 23.5, printed p.485 (PDF p.501): "The
  restriction of φ to T is an isogeny T → T′, and so f: X(T′) → X(T) is
  injective with finite cokernel."
- The remark after Definition 23.1, printed p.484 (PDF p.500): for a
  homomorphism `f : X′ → X` of free `ℤ`-modules of finite rank, the
  following are equivalent: `f` is injective with finite cokernel; `f`
  and its dual `f^∨` are injective; `f_ℚ` is an isomorphism.

The official errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`,
SHA-256 `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was checked. It has no entry for printed pp.126, 230, 233-234 or 484-485.
Its Chapter 12 entries concern 12.41 and 12.57 only.

The statement on cocharacters is derived from these passages as follows.
A finite flat surjective homomorphism of split tori has finite kernel and
full image, so it is an isogeny in the sense of Definition 6.6. For a split
torus `D(M)`, Theorem 12.9(a) with `𝔾_m = D(ℤ)` identifies the
cocharacters `Hom(𝔾_m, D(M))` with `Hom(M, ℤ)`, naturally in `M`. Under
this identification, composition with `f` on cocharacters is the dual
`X(f)^∨` of the character map `X(f) : X(T) → X(A)`. By the proof of
Proposition 23.5, `X(f)` is injective with finite cokernel. By the
equivalence after Definition 23.1, `X(f)_ℚ` is an isomorphism, hence so is
its dual `(X(f)^∨)_ℚ`. Applying the equivalence again to `X(f)^∨` gives
injectivity and finite cokernel on cocharacters. Bijectivity after `⊗ ℝ`
follows from bijectivity after `⊗ ℚ`. This derivation explains the scope.
The Lean file does not prove the statement.

The application is Tasho Kaletha and Gopal Prasad, *Bruhat-Tits Theory: A
New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. In
the proof of Lemma 2.6.29, printed p.106 (PDF p.137), `S_sc` is the
maximal torus in the preimage of `S` in `G_sc`: "Since `S_sc → S′` is an
isogeny, `X_*(S_sc)` is of finite index in `X_*(S′)`". The authors'
corrections, `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF
p.25, add before Definition 2.6.20 that the field there is Henselian with
perfect residue field. That restriction belongs to the valued-field
application. It is not imported here, because the algebraic facts above
hold over every field.

The killed-point lemmas are internal. They record the comparison of
kernels that the KP passage uses implicitly, and they hold by the
two-line argument above.
