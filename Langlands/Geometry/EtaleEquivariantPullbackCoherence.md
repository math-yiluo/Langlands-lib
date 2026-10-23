# Equality transport and coherence of equivariant étale pullback

This module constructs canonical equality transport for geometric equivariant
pullback and proves the unit and associativity equations for its published
identity and composition comparisons. It also proves that ordinary cohomology
and section pullback maps respect equality transport. The declarations are in
`Langlands.Geometry.EtaleCohomologyAction`.

## Inputs and notation

The schemes `X`, `Y`, `Z`, and `W` and the commutative coefficient ring `R`
have universe `u`. The group `G` has independent universe `w`. Its actions are
supplied as homomorphisms `ρ`, `τ`, `υ`, and `σ` into the multiplicative
opposites of the respective scheme automorphism groups. This retains the
published convention that `aut ρ (g * h)` executes `aut ρ g` followed by
`aut ρ h`. No topology on `G` is required.

The geometric maps for the associativity law are actual étale morphisms

```text
f : Y → X,    k : Z → Y,    l : W → Z.
```

Each has a supplied equivariance equation, for example
`hf(g) : f ≫ aut(ρ,g).hom = aut(τ,g).hom ≫ f`.
The maps `k` and `l` have the corresponding equations for `τ,υ` and `υ,σ`.
The published `equivariantMap_id` and `equivariantMap_comp` provide all
identity and composite equivariance proofs used below.

Write `Q_f` for the functor `equivariantPullback R ρ τ f hf` and `P_f`
for its underlying ordinary restriction functor. Write
`e_X : Q_idX ≅ Id` and `d_(f,k) : Q_f ⋙ Q_k ≅ Q_(k≫f)` for the
published `equivariantPullbackId` and `equivariantPullbackComp`.
These act on the category of genuine small-étale module sheaves equipped with
the published translation-equivariance structure.

## Equality transport

For equal étale maps `f,k : Y → X`, supplied equivariance proofs `hf,hk`,
and `h : f = k`, `equivariantPullbackCongr` constructs

```text
c_h : Q_f ≅ Q_k.
```

Its implementation eliminates `h` and uses the identity natural isomorphism.
The typeclass proofs of étaleness and the equivariance proofs are propositions;
proof irrelevance identifies the two presentations after the scheme maps are
identified. Thus the construction imposes no equality of chosen proofs as an
additional assumption, and its inverse laws and naturality come from the
identity natural isomorphism.

`equivariantPullbackCongr_hom_app_hom` proves that the underlying sheaf map
of `c_h.hom` at a coefficient sheaf `F` is exactly
`(restrictionCongr R h).hom.app F.obj`.
`equivariantPullbackCongr_refl` identifies the reflexive comparison with the
identity natural isomorphism.

For every degree `q : ℕ`, `equivariantPullbackCohomology_congr` proves

```text
a_f^q(F) ≫ H_Y^q(c_h.hom(F)) = a_k^q(F),
```

where `a_f^q` is `equivariantPullbackCohomology ... q` and `H_Y^q` is
`pullbackCohomologyFunctor R τ q`. This is an equality of morphisms of
`G`-actions on ordinary small-étale module cohomology.
`equivariantPullbackSections_congr` gives the parallel law for ordinary
section actions. Both proofs eliminate `h` and then apply the functor identity
and category identity laws.

## Unit equations

For every equivariant coefficient sheaf `F` on `X`,
`equivariantPullbackComp_id_target` proves

```text
d_(idX,f).hom(F) ≫ c_(f≫idX=f).hom(F) = Q_f(e_X.hom(F)).
```

Thus comparing the two successive pullbacks with pullback along `f ≫ idX`
and transporting along the scheme right-unit equation gives the same map as
pulling back the identity comparison on `X`.

The other equation, `equivariantPullbackComp_id_source`, is

```text
d_(f,idY).hom(F) ≫ c_(idY≫f=f).hom(F) = e_Y.hom(Q_f(F)).
```

It identifies the comparison at the other end with the identity comparison
on the already pulled-back coefficient sheaf. The suffixes `target` and
`source` refer to the target `X` and source `Y` of the scheme map `f`.
Both equations are proved in the equivariant coefficient category.

## Associativity equation

`equivariantPullbackComp_assoc` identifies the two comparison paths starting
at the triple pullback `Q_l(Q_k(Q_f(F)))`. With
`h_assoc : (l ≫ k) ≫ f = l ≫ (k ≫ f)`, it proves

```text
d_(k,l).hom(Q_f(F)) ≫ d_(f,l≫k).hom(F) ≫ c_h_assoc.hom(F)
  = Q_l(d_(f,k).hom(F)) ≫ d_(k≫f,l).hom(F).
```

The final equality transport on the left is essential to the type: the two
parenthesizations of the composite scheme map need not be definitionally
equal. The displayed equation includes the actual equivariance proofs for
each composite, constructed from `hf`, `hk`, and `hl`.

## Implemented coherence proofs

The helper `restrictionCongr_hom_component` expresses a forward ordinary
equality comparison at `U : Y.Etaleᵒᵖ` as the presheaf image of the opposite
of the inverse component of `MorphismProperty.Over.mapCongr`. Its proof
eliminates the equality and uses preservation of identity by the presheaf.
It complements the published inverse-component formula.

Each of the three coherence proofs first uses extensionality of equivariant
morphisms, then sheaf and natural-transformation extensionality. The published
underlying-map formulas replace `Q_f`, `d`, and `e` by ordinary restriction
and its comparison maps. The new equality-component formula handles `c_h`.
After unfolding ordinary restriction, `restrictionComp`, and `restrictionId`,
presheaf functoriality combines consecutive maps. The resulting site arrows
are equal because the components of `Over.mapId`, `Over.mapComp`, and
`Over.mapCongr` have identity underlying scheme morphisms. This proves the
equations from the existing constructions; no coherence equation is supplied
as an input.

## Provenance and scope

This is an internal derived extension of
[EtaleEquivariantPullbackFunctoriality](EtaleEquivariantPullbackFunctoriality.md),
[EtaleEquivariantPullback](EtaleEquivariantPullback.md),
[EtaleCohomologyDiagram](EtaleCohomologyDiagram.md), and
[EtalePullback](EtalePullback.md). The site comparisons come from the pinned
Mathlib module `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`.
The module does not claim to transcribe a named theorem of Harris or Berkovich.

The unit and associativity results are component equations for the supplied
geometric inputs and natural comparison isomorphisms. This module does not
package a pseudofunctor or a varying-scheme equivariant coefficient category.
The schemes, their actions, and the equivariant étale maps remain inputs.
No analytic site, smooth group action, compactly supported cohomology, trace,
Shimura tower, or actual Harris specialization is constructed here.
