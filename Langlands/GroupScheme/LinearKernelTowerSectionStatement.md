# Homomorphic sections for finite character-linear kernel towers

Worker 1437.

`Langlands.GroupScheme.LinearKernelTower.SectionExistenceStatement.{u}` is
a Prop-valued definition recording a section-existence assertion. This
module contains no proof of that assertion. It reuses the published
[`LinearKernelTower.AdmitsTower`](LinearKernelTower.md) without modification.

The universe `u` is arbitrary. The statement quantifies over every
`k : Type u` with `Field k` and `IsAlgClosed k`, and every `Λ : Type u`
with `AddCommGroup Λ` and `AddGroup.FG Λ`. Put `R := CommRingCat.of k`,
`B := Spec R`, and `D := Diagonalizable.groupScheme R Λ`, the actual
diagonalizable group scheme with coordinate algebra `R[Λ]`. The group
`Λ` may be trivial or have torsion. There is no restriction on the
characteristic of `k`.

For every actual `E : GroupScheme B` and every actual homomorphism
`q : E ⟶ D.toGrp`, the sole further hypothesis is
`LinearKernelTower.AdmitsTower D q`. The conclusion is

```text
∃ s : D.toGrp ⟶ E, s ≫ q = 𝟙 D.toGrp.
```

Thus the given `q` has a section in the category of group schemes over
`B`. In particular `s` preserves the group law, and the equation is an
equality of actual group-scheme homomorphisms.

The tower hypothesis already contains affineness and local finite type
at every stage. The statement adds no separate hypotheses on `E` or its
kernels. It requires no smoothness, connectedness, reducedness, or
previously supplied section of schemes. Finite and nonreduced additive
kernels and trivial characters remain allowed. The one-step splitting
assertion is not a proposition premise of this definition.

The complete tower hypothesis has the following meaning. All objects
and maps below are group schemes and their homomorphisms over `B`, in
universe `u`.

- `AdmitsTower D q` means `∃ n : ℕ, HasTower D n q`. The length can be
  zero. Unfolding it gives quotient maps
  `E = E₀ → E₁ → ⋯ → Eₙ` with structural maps `qᵢ : Eᵢ ⟶ D.toGrp`,
  where `q₀ = q`.
- Every `Eᵢ`, including `E₀` and the terminal `Eₙ`, has affine structural
  morphism to `B` and is locally of finite type over `B`. Together these
  express the affine finite-type setting over the field.
- At length zero the given structural map is an isomorphism:
  `HasTower D 0 q` is exactly
  `LocallyOfFiniteType E.X.hom ∧ IsAffineHom E.X.hom ∧ IsIso q`.
- At a successor, there are `Q`, `p : E ⟶ Q`, and
  `r : Q ⟶ D.toGrp` with `p ≫ r = q` and `HasTower D n r`.
  The first quotient satisfies
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι p)) p`.
  This says that the underlying scheme map is flat, surjective, and
  locally of finite presentation, with the prescribed subgroup functor
  equal to the all-test range of its full actual kernel. It does not
  require surjectivity on each group of test points.
- That successor also requires `IsCharacterLinearKernel D q p`. Write
  `K := kernel p`, the scheme-theoretic kernel defined by pullback along
  the unit of `Q`, with inclusion `kernelι p`. There exist a homomorphism
  `a : K ⟶ VectorGroup.groupScheme R 1` with `IsClosedSubgroup a`,
  a character `χ : characterLattice D`, and an action
  `b : AutomorphicAction D.toGrp K`. Thus `a` is a closed embedding of
  the full kernel into the one-dimensional additive group, and `b` is
  an actual scheme action by group automorphisms.

The last kernel clause requires these two equations for every test
`T : Over B`:

```text
∀ (g : T ⟶ E.X) (x : T ⟶ K.X),
  b.act (g ≫ q.hom.hom) x ≫ (kernelι p).hom.hom
    = g * (x ≫ (kernelι p).hom.hom) * g⁻¹

∀ (d : T ⟶ D.X) (x : T ⟶ K.X),
  b.act d x ≫ a.hom.hom
    = (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom).
```

The first says that conjugation in the current stage on its full kernel
factors through its structural map to `D` as the action `b`. The second
says that the embedding into the additive group is equivariant for
scaling by the character `χ`. These conditions apply on all test
schemes. At different steps the kernel, embedding, character, and action
can differ. A kernel may be trivial, finite, or nonreduced; the
character may be trivial. The recursion ends with `IsIso qₙ` for the
actual terminal structural map.

This is an internal derived assertion motivated by J. S. Milne,
*Algebraic Groups: The Theory of Group Schemes of Finite Type over a
Field*, corrected reprint (2022), registered as
`milne-2022-algebraic-groups`, SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The original proof of Theorem 16.26(a), printed pp.332–333 (zero-based
PDF indices 342–343), first splits the smaller quotient by induction
on a finite normal series and then forms the pullback in diagram (118).
It splits the top extension using Theorem 15.34(d), printed pp.319–320
(PDF indices 329–330). That theorem gives vanishing of the extension
classes for an algebraic group of multiplicative type acting on a
closed subgroup of the additive group, when the field is algebraically
closed and the action restricts a linear action on the additive group.

Here the target is the diagonalizable group of an arbitrary finitely
generated abelian `Λ`. The assertion abstracts the induction argument
to any supplied tower with the stated quotient and action properties.
It does not require an embedding of `E` into a triangular matrix group
or identify a maximal unipotent subgroup. Milne's theorem motivates
this interface; it does not literally state this arbitrary-tower
proposition.

The intended proof proceeds by induction on the supplied length. At
length zero, the inverse of the given isomorphism `q` is a section.
At a successor, write `q = p ≫ r`. Induction supplies a homomorphic
section `t : D.toGrp ⟶ Q` of `r`. Form the actual group-scheme pullback
`P := E ×_Q D` along `t`, with projections `e : P ⟶ E` and
`d : P ⟶ D.toGrp`. The pullback equation and `t ≫ r = 𝟙 D.toGrp`
give `e ≫ q = d`. The map `d` is the pulled-back fppf quotient.

To apply the linear additive-kernel splitting theorem, a proof must
establish the affineness and finite type of `P`, compare `kernel d`
with `kernel p`, and transport the closed embedding and the two
all-test action equations through that comparison. These are
obligations derived from the tower and pullback, not extra hypotheses
of `SectionExistenceStatement`. Once that theorem supplies a
homomorphic section `v : D.toGrp ⟶ P` of `d`, the composite `v ≫ e`
is a section of the original `q`.

The published one-step target is
`Langlands.GroupScheme.LinearAdditiveExtensionSplittingStatement`,
explained in
[`LinearAdditiveExtensionSplittingStatement.md`](LinearAdditiveExtensionSplittingStatement.md).
Its proof and the pullback/induction proof above are separate
obligations. Defining `SectionExistenceStatement` proves neither of
them and asserts no unconditional existence of an `AdmitsTower`
presentation. Constructing towers for actual triangular diagonal
maps is a separate branch.
