# The fold morphism of an induced space on the copies

Author: Worker 5254.

This module proves facts about the fold morphism `foldHom H X : X_{G/H} → X`
(module `InducedSiteFaithful`) of Berkovich's induced space `X_{G/H}` (module
`InducedAnalyticSpace`). It is a helper for the proof of Berkovich's Example
1.2.1(i), `InducedSpace.QuasiEtaleSiteEquivalenceStatement`: fullness and
essential surjectivity of induction use the last lemma below. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace`.

Throughout, `G : Type z` is a group, `H` a subgroup and `X` an `H`-object of
`LocalizedCategory` (Lean type `Action (LocalizedCategory …) H`). Points are
elements of the underlying topological space `localizedSpaceFunctor.obj`.
`pointCoset H X p` (module `InducedSpacePoints`) is the coset indexing the copy
of `X` that contains the point `p` of `X_{G/H}`.

## Declarations

- `unitHom_foldHom H X : unitHom H X ≫ foldHom H X ≫ X.ρ (baseRep H) = 𝟙 X.V`.
  Here `unitHom H X = X.ρ r⁻¹ ≫ copy H X H` is the underlying morphism of the
  unit `X → X_{G/H}` and `r = baseRep H ∈ H` is the chosen representative of
  the coset `H`. So the unit is a split monomorphism.
- `mono_unitHom H X`: the instance `Mono (unitHom H X)`.
- `copyDomain H X c`: the open analytic domain of `X_{G/H}` whose carrier is
  the image of the copy `copy H X c`. It is open by `isOpen_range_copy_space`.
- `mem_copyDomain_iff H X c p`: a point `p` lies in `copyDomain H X c` if and
  only if `pointCoset H X p = c`.
- `copy_mem_copyDomain H X c x`: the copy `c` maps every point into
  `copyDomain H X c`.

The remaining statements take a hypothesis
`hP : OpenPartitionCoproductStatement.{u, v, z}` (module
`OpenPartitionCoproductStatement`): an analytic space whose underlying space is
the disjoint union of open subsets `U_j` is the coproduct of the open domains
`U_j`. They hold for every such `hP`; the statement itself is not proved here.

- `nonempty_isColimit_copyDomain H X hP`: the canonical morphisms
  `domainι (copyDomain H X c)` of the open domains of the copies make
  `X_{G/H}` a coproduct.
- `domainι_copyDomain_foldHom_copy H X hP c`: on the domain of the copy `c`,
  the fold morphism followed by the copy `c` is the canonical morphism:
  `domainι (copyDomain H X c) ≫ foldHom H X ≫ copy H X c = domainι (copyDomain H X c)`.
- `foldHom_copy_of_pointCoset H X hP f c hf`: let `f : T ⟶ X_{G/H}` be a
  morphism of `LocalizedCategory` such that every point `t` of `T` satisfies
  `pointCoset H X (f t) = c`. Then `f ≫ foldHom H X ≫ copy H X c = f`.

## Proof

`unitHom_foldHom`: unfold `unitHom`, use `copy_foldHom` (the fold morphism is
the identity on each copy) and `ρ(r⁻¹) ≫ ρ(r) = ρ(r r⁻¹) = 𝟙`. A morphism with a
left inverse is a monomorphism.

`nonempty_isColimit_copyDomain`: apply `hP` to the family of images of the
copies. By `mem_range_copy_space_iff`, a point lies in the image of the copy
`c` exactly when its coset is `c`. So these open sets are pairwise disjoint,
and every point `p` lies in the image of the copy `pointCoset H X p`.

`domainι_copyDomain_foldHom_copy`: let `φ_d` be the morphism
`domainι (copyDomain d) ≫ foldHom ≫ copy d`, and let `ψ : X_{G/H} → X_{G/H}`
be the morphism given by the family `φ_d` and the coproduct of the previous
lemma. Then `ψ = 𝟙`, by the coproduct property of the copies
(`copies_hom_ext`). Indeed `copy d` factors as
`domainLift (copy d) ≫ domainι (copyDomain d)`, so
`copy d ≫ ψ = domainLift (copy d) ≫ φ_d = copy d ≫ foldHom ≫ copy d = copy d`
by `copy_foldHom`. The equation for `ψ` on the domain `c` then reads
`domainι (copyDomain c) = domainι (copyDomain c) ≫ foldHom ≫ copy c`.

`foldHom_copy_of_pointCoset`: by `mem_copyDomain_iff`, the image of `f` lies
in `copyDomain H X c`, so `f = domainLift f ≫ domainι (copyDomain c)`
(`domainLift_comp`). Apply the previous lemma.

## Original source and provenance

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.1.2, printed p.2, defines `X_{G/H}` as the disjoint union of copies `X_i` of
`X` indexed by `G/H`. Example 1.2.1(i) (§1.2, printed p.3) states without proof
that induction gives an isomorphism of sites. The lemmas here are internal
helpers derived for this formalization; they are not stated in the source. The
coproduct property of an open partition is the separate statement
`OpenPartitionCoproductStatement`, taken here as a hypothesis.
