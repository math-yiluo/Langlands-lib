# Statement: fibre products along étale morphisms of `G`-spaces are `G`-spaces

`EtalePullbackGSpaceStatement K` is an unproved, Prop-valued statement. It is an internal
analytic prerequisite for the equivariant half of
`QuasiEtaleToEtaleStatement`, the morphism of sites
`μ_G : X(G)_qét → X(G)_ét` (Berkovich 1996, §1.2). The cofiltered categories
needed for representable flatness of `Ét(X(G)) → Qét(X(G))` are built from
fibre products `V₁ ×_X V₂` of `G`-spaces étale over `X`. Those fibre products
must again be `G`-spaces, that is, objects of the Library category `GSpace`.

## Exact statement

Fix a complete ultrametric normed field `K : Type u`. For every group
`G : Type z` with a topology (no topological-group axioms are required), and all
objects `A`, `B`, `Y`, `P` of `LocalizedCategory.{u, v, v}`, suppose:

- `f : A ⟶ Y` is étale (the Library predicate `etale`) and `g : B ⟶ Y` is an
  arbitrary morphism;
- `p : P ⟶ A` and `q : P ⟶ B` form a categorical pullback square
  `IsPullback p q f g` in the localized category;
- the underlying topological spaces (`localizedSpaceFunctor.obj`) of `A`, `B` and
  `Y` are Hausdorff;
- `σ : G →* Aut P`, `σA : G →* Aut A` and `σB : G →* Aut B` are actions by
  analytic automorphisms, with `σA` and `σB` continuous in the Library sense
  `IsContinuousAction` (Berkovich's test triples `(U, f, t)`);
- `p` and `q` are equivariant: `(σ a).hom ≫ p = p ≫ (σA a).hom` and
  `(σ a).hom ≫ q = q ≫ (σB a).hom` for every `a : G`.

Then the underlying topological space of `P` is Hausdorff and `σ` is a continuous
action. In other words, together with `σ` the pullback `P` satisfies the Library's
`gSpaceProperty`.

No action on `Y` is assumed, and no compatibility of `σ` with an action on `Y`.
Where the statement is used, the action `σ` comes from
`CategoricalPullback.pullbackAction` applied to actions on `A`, `B` and `Y` with
equivariant `f` and `g`, but the statement holds for any `σ` making both
projections equivariant. The statement asserts nothing about the existence of the
pullback. That existence, with étale base change, is the separate published
statement `LocalizedEtalePullbackStatement`.

## Provenance

This statement is internal (derived). Berkovich does not state it as a separate
result. It is the implicit step that lets his definition of `μ_G` and of the
étale site of a `G`-space use fibre products of `G`-spaces.

- Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (1995–1996
  manuscript), §1.1, printed p.1: "In what follows all analytic spaces considered
  are assumed to be Hausdorff." Printed p.2: a `G`-space is "an analytic space X
  endowed with a continuous action of a topological group G". So a fibre product
  can be an object of `Ét(X(G))` only when it is Hausdorff and its induced action
  is continuous.
- The same manuscript, §1.2, printed p.3: "There is a morphism of sites
  µG : X(G)qét → X(G)ét". The same paragraph uses fibre products of `G`-spaces,
  "F′((X′ ×X U)(G′))" for `U` étale or quasi-étale over `X`.
- Hausdorffness is classical. Berkovich, *Étale cohomology for non-Archimedean
  analytic spaces* (1993), §1.4, printed pp.30–31, and §3.1.1, printed p.54,
  explain it. An étale morphism is quasifinite, and "quasifinite morphisms are
  locally separated" (p.54). Proposition 1.4.2 says that a locally separated morphism
  is separated if and only if the induced map of underlying spaces is Hausdorff,
  which holds for a map out of the Hausdorff space `A`. Separatedness is stable
  under base change, so `q` is separated. Then `|P| → |B|` is Hausdorff (p.31) and
  `B` is Hausdorff, so `P` is Hausdorff. The hypothesis that `Y` is Hausdorff is
  kept for convenience of proof; every application supplies it.
- Continuity is the non-compact, étale-leg analogue of the Library statement
  `CompactPullbackActionContinuityStatement`. That statement assumes all four
  spaces compact and only concludes continuity.

The Library's `LocalizedCategory` is the category of analytic spaces in which the
étale sites are defined. The pullback here is the categorical pullback there, as in
`LocalizedEtalePullbackStatement`. It is not a pointwise fibre product of
underlying spaces.
