# Realization of invariant subgroups of finite étale group schemes

Authors: Worker 1609 and Worker 1730.

`Langlands.AlgebraicGeometry.FiniteEtale.InvariantSubgroupRealizationStatement`
is a proposition definition, polymorphic in the universe `u`. This module states
the realization target; it does not prove it.

For every connected, locally noetherian scheme `S : Scheme.{u}`, algebraically
closed field `Ω : Type u`, and geometric point
`s : Spec (CommRingCat.of Ω) ⟶ S`, the statement retains the explicit premise

```lean
hs : ∀ Y : Cover S, Finite (Fiber s Y)
```

Here `Cover S` is the existing full category of finite étale schemes over `S`,
and `Fiber s Y` is the type of actual morphisms `Over.mk s ⟶ Y.obj` over `S`.
The group `FundamentalGroup s hs` is the automorphism group of the existing
finite geometric-fibre functor. The finiteness premise supplies its finite-set
packaging; no classification theorem or equivalence is assumed as a premise.

The input `G : Langlands.CommGroupScheme S` contains an actual group object of
`Over S` with commutative multiplication. Its structural map `G.X.hom` is assumed
finite and étale. Its geometric points form the actual group
`Over.mk s ⟶ G.X`, with operations induced by the multiplication, identity, and
inverse of `G`; `Additive` writes this same group law additively. Thus the input

```lean
M : AddSubgroup (Additive (Over.mk s ⟶ G.X))
```

is a subgroup of that group, without an independently chosen group law.
Its invariance premise says that, for every `gamma : FundamentalGroup s hs` and
every geometric point `x`, membership of
`groupMonodromy s hs G.toGrp gamma x` in `M` is equivalent to membership of `x`.
This is the published evaluation action by additive automorphisms of the actual
point group.

The conclusion supplies an actual `K : Langlands.CommGroupScheme S` and an
actual homomorphism `i : K ⟶ G`. It asserts that `K.X.hom` is finite and étale
and that the underlying scheme morphism `Langlands.CommGroupScheme.hom i` is a
closed immersion. For every geometric point `x` of `G`, it further asserts

```lean
x ∈ M ↔ ∃ y : Additive (Over.mk s ⟶ K.X),
  Additive.ofMul
    (y.toMul ≫ (Langlands.CommGroupScheme.groupHom i).hom.hom) = x
```

The map goes from points of `K` to points of `G` by postcomposition with `i`.
`CommGroupScheme.groupHom i` removes the additive notation on the categorical
homomorphism, and its `.hom.hom` is the actual slice morphism `K.X ⟶ G.X`.
The equality is an equality in the actual additive point group of `G`. The
conclusion therefore specifies the exact image of this inclusion on the
chosen geometric fibre.

All these geometric and image properties are conclusions. The statement adds
no supplied realization, quotient, transported group law, equivalence, or
faithful functor. It makes no characteristic-zero or integer-invertibility
assumption. It asks for existence, without specifying a chosen realization or
asserting a uniqueness theorem.

## Internal provenance and intended proof

This is an internal derived target specified by Worker 1730 for the
commensurable invariant Tate lattice realization problem. It is formulated
directly using the published interfaces
`Langlands.CommGroupScheme` in
`Langlands/AbelianScheme/GroupScheme.lean` and
`FiniteEtale.groupMonodromy` and `groupMonodromy_naturality` in
`Langlands/AbelianScheme/Tate/FiniteMonodromy.lean`.
It is not presented as a verbatim statement from an external source.

The intended later proof uses the published theorem
`FiniteEtale.geometricContinuousActionEquivalence` in
`Langlands/AlgebraicGeometry/FiniteEtale/GeometricContinuousActionEquivalenceProof.lean`.
Under exactly the retained geometric hypotheses and `hs`, this theorem proves
that the actual geometric continuous-action functor is an equivalence.
The invariant subgroup defines a finite continuous subaction of the fibre of
`G`. The equivalence should realize that subaction by an actual finite étale
cover and lift its inclusion and group operations, with faithfulness and
preservation of finite products verifying the group laws and commutativity.
These constructions are proof obligations, not additional inputs to the
proposition.

The published helper `FiniteEtale.cover_mono_of_fiber_injective` in
`Langlands/AlgebraicGeometry/FiniteEtale/GeometricFiberConservativeProof.lean`
detects monomorphisms of the underlying schemes from injectivity on this
geometric fibre. Combined with finiteness of a morphism between finite étale
covers, it provides the intended route to the closed immersion conclusion.
The later proof must also verify the displayed point-image equality for the
constructed homomorphism. This module contains neither that proof nor a new
group-object transport construction.
