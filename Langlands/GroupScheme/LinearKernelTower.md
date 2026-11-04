# Finite equivariant fppf quotient towers with character-linear additive kernels

Worker 1521 implemented this module for the task published by Worker 669. It
is a definition prerequisite for the structural triangular splitting statement
and its section-existence successors. The module only packages supplied
quotient and action data. It does not assert that a tower exists, and it does
not assert that any extension splits.

## Setting

Everything works over an arbitrary field `k : Type u` in an arbitrary universe
`u`. Put `R := CommRingCat.of k` and `B := Spec R`. Fix any actual commutative
group scheme `D : CommGroupScheme B`. `D` does not need a diagonalizable
presentation, and no smoothness, connectedness, algebraic-closure or
characteristic hypothesis is imposed anywhere. Every group scheme in a tower
is an actual `GroupScheme B` in the same universe `u`, and every map is an
actual homomorphism of group schemes over `B`.

The module reuses these existing Library notions without modification:

- `kernel p` and `kernelι p` from `Langlands.AbelianScheme.Kernel`: the actual
  group-scheme kernel of `p`, built as the pullback of `p` along the unit of the
  target, together with its inclusion into the source;
- `IsClosedSubgroup a` from `Langlands.GroupScheme.Reductive.Basic`: the
  underlying morphism of schemes of `a` is a closed immersion;
- `AutomorphicAction H G` from `Langlands.GroupScheme.AutomorphicAction`: one
  actual action morphism `H.X ⊗ G.X ⟶ G.X` that acts by group automorphisms on
  every test scheme. `b.act h x` is its value on test points;
- `VectorGroup.groupScheme R 1` and `VectorGroup.weightAction χ` from
  `Langlands.GroupScheme.VectorGroupQuotient`. The first is the additive group
  `𝔾ₐ` over `B`. For `χ : characterLattice D` (a homomorphism `D ⟶ Gm B`), the
  second is the action of `D` on `𝔾ₐ` in which a test point `d` multiplies the
  coordinate by the unit value of `χ` at `d`. This is the "linear action through
  the natural action of `Gm` on `Ga`" in Milne's sense;
- `RelativeRoot.IsFppfQuotient N p` from
  `Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`. It requires
  the underlying scheme morphism of `p` to be flat, surjective and locally of
  finite presentation, and it requires the all-test image of the actual kernel
  `kernelι p` to equal `N`.

## `IsCharacterLinearKernel D q p`

Let `E Q : GroupScheme B`, `q : E ⟶ D.toGrp` and `p : E ⟶ Q`, and put
`K := kernel p`. The proposition `IsCharacterLinearKernel D q p` holds exactly
when there exist

- an actual homomorphism `a : K ⟶ VectorGroup.groupScheme R 1` with
  `IsClosedSubgroup a`,
- a character `χ : characterLattice D`, and
- an automorphic action `b : AutomorphicAction D.toGrp K`,

such that for every test `T : Over B`:

1. for all `g : T ⟶ E.X` and `x : T ⟶ K.X`,
   `b.act (g ≫ q.hom.hom) x ≫ (kernelι p).hom.hom = g * (x ≫ (kernelι p).hom.hom) * g⁻¹`;
2. for all `d : T ⟶ D.X` and `x : T ⟶ K.X`,
   `b.act d x ≫ a.hom.hom = (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom)`.

The first equation says that conjugation by a point `g` of `E` on the full
actual kernel `K` is the action of `D` at the image point `g ≫ q`. So
conjugation by `E` on `K` factors through `q`. The second equation says that
the closed embedding `a` of `K` into `𝔾ₐ` is equivariant for `b` on `K` and
for the action of `D` on `𝔾ₐ` through the character `χ`. Both equations are
required on every test scheme over `B`, not only on field-valued points.

`K` may be finite or nonreduced, for example a Frobenius kernel inside `𝔾ₐ`,
and `χ` may be the trivial character. The definition also does not require
`K` to be nontrivial.

## `HasTower D n q`

`HasTower D n q` is defined for `n : ℕ` and `q : E ⟶ D.toGrp`, with `E`
implicit, by structural recursion on `n`:

- `HasTower D 0 q` holds when `E.X.hom` is locally of finite type, `E.X.hom` is
  affine (`IsAffineHom`), and `q` is an actual isomorphism of group schemes
  (`IsIso q` in the category of group schemes over `B`).
- `HasTower D (n + 1) q` holds when `E.X.hom` is locally of finite type and
  affine, and there exist `Q : GroupScheme B`, `p : E ⟶ Q` and
  `r : Q ⟶ D.toGrp` such that
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι p)) p`,
  `p ≫ r = q`, `IsCharacterLinearKernel D q p` and `HasTower D n r` all hold.

**Direction.** Unfolding the recursion, a tower of length `n` is a chain of
quotient maps
`E = E₀ --p₀--> E₁ --p₁--> ⋯ --pₙ₋₁--> Eₙ`
with structural homomorphisms `qᵢ : Eᵢ ⟶ D`. Here `q₀ = q` and
`qᵢ = pᵢ ≫ qᵢ₊₁`, so every structural map stays over the fixed `D`. The last
structural map `qₙ : Eₙ ⟶ D` is an actual isomorphism. The tower therefore
starts at the large group `E` and passes through smaller and smaller quotients
down to `D`.

**Every stage.** Each `Eᵢ`, for `0 ≤ i ≤ n` and including the terminal one, is
affine over `B` and locally of finite type over `B`. Over a field, these two
conditions together describe affine algebraic groups in Milne's sense. The
module does not prove this comparison.

**Each transition.** Each `pᵢ` is an fppf quotient by its own full actual
kernel `kernel pᵢ`. The subgroup functor in `RelativeRoot.IsFppfQuotient` is
the all-test range of `kernelι pᵢ`, so its kernel clause holds automatically.
What the step really requires is that the underlying morphism of `pᵢ` is flat,
surjective and locally of finite presentation. `pᵢ` does not need to be
surjective on the group of `T`-points for each test `T`.

**Each kernel.** The kernel condition at step `i` is
`IsCharacterLinearKernel D qᵢ pᵢ`. It uses the structural map `qᵢ` of the
current stage `Eᵢ`. So conjugation by `Eᵢ` on `kernel pᵢ` acts through `qᵢ`,
and under some closed embedding into `𝔾ₐ` this action becomes the action
through a character of `D`. The character, the embedding and the action may
differ from step to step.

**Length zero.** A length-zero tower is exactly an affine, locally
finite-type `E` together with an actual isomorphism `q : E ⟶ D`. The
`IsIso q` clause concerns the given structural homomorphism. An abstract
isomorphism `Nonempty (E ≅ D.toGrp)` would not be enough.

## `AdmitsTower D q`

`AdmitsTower D q := ∃ n : ℕ, HasTower D n q`: the map `q` has a tower of some
finite length.

## Basic laws

- `hasTower_zero_iff` and `hasTower_succ_iff` (both `@[simp]`) are the zero
  and successor unfolding equations displayed above. Both are proved by
  `Iff.rfl`, so the recursion unfolds definitionally.
- `admitsTower_iff` unfolds `AdmitsTower`, also by `Iff.rfl`.
- `HasTower.zero` and `HasTower.succ` build towers from the corresponding
  data.
- `HasTower.locallyOfFiniteType` and `HasTower.isAffineHom` read off the
  finite-type and affineness conditions of the source of a tower of any length,
  by case analysis on the length.
- `AdmitsTower.of_hasTower` turns a tower of a given length into
  `AdmitsTower`.

## Provenance

This is an internal, derived definition, not a verbatim source definition.
It reformulates, for actual Library group schemes, the structure used in

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over
a Field*, corrected reprint (2022), registered as
`milne-2022-algebraic-groups`, SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`:

- **Theorem 16.21**, printed pp.330–331 (zero-based PDF indices 340–341). For a
  trigonalizable algebraic group `G` it gives a normal series
  `G ⊃ G₀ ⊃ G₁ ⊃ ⋯ ⊃ G_r = e` with `G₀ = G_u`. For each `i`, the action of
  `G` on `Gᵢ/Gᵢ₊₁` by inner automorphisms factors through `G/G_u`, and there is
  an embedding `Gᵢ/Gᵢ₊₁ ↪ Ga` that is equivariant for a linear action of
  `G/G_u` on `Ga`.
- **Proof of Theorem 16.26(a)**, printed pp.332–333 (zero-based PDF indices
  342–343). It takes the last nontrivial group `N` of that series, splits the
  smaller extension `G/N → D` by induction on the length of the series, pulls
  `G → G/N` back along the resulting section (diagram (118)), and splits the
  pulled-back extension using Theorem 15.34(d).

From Milne's series, write `D := G/G_u`. The successive quotients
`G = G/G_r → G/G_{r-1} → ⋯ → G/G₀ = D` form a tower in the sense above. The
kernel of `G/Gⱼ₊₁ → G/Gⱼ` is `Gⱼ/Gⱼ₊₁`, which embeds into `Ga`, and the
induced conjugation action factors through `D` and is linear, that is, given
by a character of `D` acting on `Ga`. This is how the definition differs from
the source:

- it is quotient-oriented rather than subgroup-oriented;
- it fixes an arbitrary commutative target `D` with explicit structural maps,
  instead of the diagonalizable quotient `G/G_u` of a trigonalizable group;
- it states the action conditions as all-test equations on actual kernels;
- it records fppf quotient maps explicitly and requires affineness and local
  finite type at every stage;
- it does not drop duplicate (trivial) steps.

The first step of a successor tower matches the quotient by the last
nontrivial `N` in Milne's proof of 16.26. The remaining tower `Q → ⋯ → D` is
the smaller quotient that is split by induction. A section of the remaining
tower is meant to pull `E → Q` back to an extension of `D` whose kernel
carries the character-linear action that a one-step splitting statement
needs. This explains why the interface was chosen. Neither this pull-back
argument nor any existence or splitting theorem is stated or proved in this
module. They belong to later statement and proof tasks.

The official 2022 errata page for the book
(`https://www.jmilne.org/math/Books/iagerrata2022.html`, consulted on
2026-11-03) has no entry for printed pp.330–333. The Library has no errata
note for this source.

## Relation to existing series predicates

`RelativeRoot.HasSplitSeries` and `SplitSolvable.HasSeries` are
subgroup-oriented series of smooth connected closed normal subgroups with
`Ga` (or `Gm`) quotients. They cannot express the present towers, because the
additive kernels here may be finite or nonreduced and need not be isomorphic
to `Ga`. This module does not relate the new predicates to those series.
