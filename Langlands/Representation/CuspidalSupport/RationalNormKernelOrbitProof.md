# Renard VI.3.2(i)

This module proves
`Langlands.CuspidalSupport.rationalNormKernelOrbit`, whose type is the
unchanged published statement
`Langlands.CuspidalSupport.RationalNormKernelOrbitStatement.{u,uV}` from
`Langlands.Representation.CuspidalSupport.RationalNormKernelOrbitTwistStatement`.
The proof has no hypotheses beyond those of the statement. The field and
representation-carrier universes `u` and `uV` stay independent, and the
field is any nonarchimedean local field.

The proof installs the instances the statement itself specifies:
affineness and smoothness from the actual connected reductive group
scheme, the topology `rationalPointTopology F G.X`, and the proved
`rationalPoint_isTopologicalGroup F G`. It uses the actual subgroup
`Plancherel.rationalCommonNormKernel G` and its published normality
instance `rationalCommonNormKernel_normal`. Every restricted action keeps
the original carrier.

## First conclusion: an irreducible constituent exists

The published lemma `rationalNormKernelConstituent_of_finiteRestriction`
is applied to the published proof of Renard VI.3.2(ii),
`Langlands.CuspidalSupport.rationalNormKernelFiniteRestriction`
(module `RationalNormKernelFiniteRestrictionProof`), and then to the field,
group and irreducible smooth representation. The finite-family clause of
VI.3.2(ii) gives finitely many irreducible subrepresentations whose
supremum is the whole carrier. Ambient irreducibility gives a nontrivial
carrier, through the irreducible group-algebra module and
`IsSimpleModule.nontrivial`. If the index type were empty, the supremum
would be the bottom submodule, which contradicts nontriviality. So some
member of the family is an irreducible subrepresentation. Only this
conclusion uses VI.3.2(ii).

## Second conclusion: translates

The published helper `Langlands.NormalRestrictionOrbit.covariance` takes
an irreducible subrepresentation `W` of the restriction and an ambient
point `g`. The published `FiniteIndexRestriction.translate` is defined as
a preimage under the ambient action, so its parameter `g⁻¹` gives the
image `ρ(g)W`. Normality makes this image invariant under the subgroup.
The map `w ↦ ρ(g)w`, with inverse `ρ(g⁻¹)`, intertwines the action
`h ↦ σ(g⁻¹hg)` on `W` with the action on the image. `translateEquiv`
packages this map as a representation equivalence. The translation order
automorphism preserves atoms, so the image is again irreducible. The image
and the equivalence give exactly the occurrence assertion of the
statement, in its inverse-conjugation direction.

## Third conclusion: one orbit

The published helper `Langlands.NormalRestrictionOrbit.singleOrbit`
starts from irreducible subrepresentations `W₁` and `W₂`.
`FiniteIndexRestriction.exists_ne_zero` gives a nonzero vector of `W₁`.
`FiniteIndexRestriction.span_orbit_eq_top` shows that the ambient orbit of
this vector spans the irreducible ambient representation. Each orbit
vector `ρ(g)v` lies in `ρ(g)W₁`, so the supremum of the translates of `W₁`
is the whole carrier. The order isomorphism
`Subrepresentation.subrepresentationSubmoduleOrderIso` carries this
identity over to the subgroup group-algebra module.

Each translated module is simple, because translation preserves
irreducibility and because of the identity-on-vectors comparison
`NormalRestrictionOrbit.subrepresentationAsModuleEquiv`. Mathlib's
`Submodule.linearEquiv_of_sSup_eq_top` (in
`Mathlib.RingTheory.SimpleModule.Isotypic`) then identifies the simple
submodule `W₂` with one member of this spanning family of simple
submodules. The helper reverses this equivalence and uses
`equivOfAsSubmoduleEquiv` to obtain an equivalence of the original
subrepresentation actions.
`Representation.IntertwiningMap.equivLinearMapAsModule` supplies the
comparison between modules and intertwiners, and bijectivity gives a
representation equivalence. Composing with `translateEquiv` gives an
equivalence from `h ↦ σ₁(g⁻¹hg)` to the action on `W₂`. This conclusion
does not use VI.3.2(ii).

## Source and route

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, VI.3.1(ii) and
VI.3.2(i)–(ii), printed pp.142–144 / PDF pp.148–150, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The norm kernel is defined in V.2.3, printed pp.105–106 / PDF
pp.111–112. The corrections to the 2010 edition (PDF p.10) fix the
inverse exponent in the conjugation action and the indexing by all of
`Irr(⁰G)`. The 2026 text includes both corrections.

Renard obtains finiteness of the restriction from the finite group Γ,
Schur's lemma and V.2.6, and then argues with isotypic components. This
Lean proof takes finiteness from the published VI.3.2(ii) theorem. For the
pairwise relation it uses a spanning family of simple submodules
directly, not isotypic components. The Markdown of the helper modules
explains the elementary module constructions used along this route.

This module does not prove VI.3.2(iii), and it uses no inertia
decomposition, Howe theorem, Bernstein decomposition or classification
theorem.
