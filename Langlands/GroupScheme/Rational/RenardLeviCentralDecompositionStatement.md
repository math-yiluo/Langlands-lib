# Central and relative directions for compatible Levi data

Worker 1222. Module
`Langlands.GroupScheme.Rational.RenardLeviCentralDecompositionStatement`.
The sole declaration
`Langlands.GroupScheme.RenardLeviCentralDecompositionStatement.{u}` is a
`Prop`-valued definition. This file states the decompositions and proves none
of them.

## Source and scope

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, V.3.6, printed p.111 / PDF p.117. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read the original passage, together with the V.2.6 Lemma and
proof on printed pp.107–108 / PDF pp.113–114.

For a parabolic `P = MN`, the source uses the inclusions
`A_G ⊂ A_M ⊂ M ⊂ G`. Restriction of rational characters gives a commuting
square after tensoring with the real numbers. Its two horizontal maps,
from group characters to characters of the corresponding split component,
are isomorphisms by V.2.6. The kernel of restriction from `A_M` to `A_G` is
`(𝔞_M^G)^*`. The source then gives

```text
𝔞_M^* = 𝔞_G^* ⊕ (𝔞_M^G)^*,
𝔞_M   = 𝔞_G   ⊕ 𝔞_M^G.
```

The algebraic statement here quantifies over every field `k : Type u`,
connected reductive group schemes `G` and `M` over `Spec k`, a morphism
`j : M ⟶ G`, their split components
`aG : AG.toGrp ⟶ G`, `aM : AM.toGrp ⟶ M`, and a morphism `f : AG ⟶ AM`
satisfying

```text
CommGroupScheme.groupHom f ≫ aM ≫ j = aG.
```

These are actual group-scheme objects and morphisms from the shared
algebraic-groups program. There is no additional record of structural
assertions. The hypotheses include `IsSplitComponent aG`,
`IsSplitComponent aM`, `IsConnectedReductive G` and
`IsConnectedReductive M`.

This is a derived algebraic generalization of the source's local-field
statement: its linear algebra uses only this compatible split-component
diagram, so neither a topology on `k` nor a parabolic or unipotent radical
occurs in the target. In particular it applies to every actual Levi
inclusion with the displayed compatible components, without requiring that
the Levi be minimal, standard, split or a subgroup of a general linear
group. It does not construct those components or their factorization for
an arbitrary Levi. The published `LeviSplitComponentStatement` supplies
such data for actual dynamic centralizers; identifying every source Levi
with those models is a separate geometric assertion. No decomposition,
character isomorphism or perfect-pairing comparison is assumed here.

## Actual spaces and maps

All spaces and maps below are already published. Write

```text
X_G = ℝ ⊗[ℤ] rationalCharacters G,
X_M = ℝ ⊗[ℤ] rationalCharacters M,
r_G = rationalCharacterRestrictReal aG,
r_M = rationalCharacterRestrictReal aM,
r   = rationalCharacterRestrictReal (CommGroupScheme.groupHom f),
g   = rationalCharacterRestrictReal (aM ≫ j).
```

`r_G : X_G →ₗ[ℝ] Vstar AG` and `r_M : X_M →ₗ[ℝ] Vstar AM` are the two
horizontal maps. Here `Vstar A = ℝ ⊗[ℤ] characterLattice A`; the published
identification of rational characters of a commutative group scheme with
its character lattice is definitional.

`r : Vstar AM →ₗ[ℝ] Vstar AG` is restriction along `f`. The map
`g : X_G →ₗ[ℝ] Vstar AM` is the composite restriction from `G`, through `M`,
to `A_M`. The compatibility of the actual morphisms makes `r ∘ g = r_G`.
The cocharacter inclusion is the published
`cocharacterMapReal f : V AG →ₗ[ℝ] V AM`, obtained by tensoring
postcomposition of actual cocharacters.

The pairing is the published `RealTorusSpace.pair AM`. For a subspace `W`
of `Vstar AM`, its published `cocharacterAnnihilator W` consists exactly of
the `v : V AM` for which `pair AM x v = 0` for every `x ∈ W`.

## Clauses of the statement

1. Both `r_G` and `r_M` are bijective. These are exactly the horizontal
   real restriction isomorphisms, expressed for the actual linear maps.
2. There exists a linear map `s : Vstar AG →ₗ[ℝ] Vstar AM` such that
   `s ∘ r_G = g` and `r ∘ s = id`. Thus `s` is the central-character
   inclusion determined by the diagram, rather than an arbitrary
   complement. Its range is explicitly required to equal `g.range`.
3. `s.range` and `r.ker` are complementary. A linear equivalence
   `Vstar AG × r.ker ≃ₗ[ℝ] Vstar AM` has the specified formula
   `(x,y) ↦ s x + y`. The relative summand is the literal restriction
   kernel, as in the source.
4. `cocharacterMapReal f` is injective. Its range is complementary to
   `cocharacterAnnihilator s.range`. A linear equivalence
   `V AG × cocharacterAnnihilator s.range ≃ₗ[ℝ] V AM` has the specified
   formula `(x,y) ↦ cocharacterMapReal f x + y`. This realizes the dual
   source decomposition on actual cocharacters, with its relative
   summand defined by the existing pairing.

The equations determine `s` uniquely because `r_G` is surjective.
Existence of `s` and of the displayed equivalences is part of the
conclusion, never a supplied comparison hypothesis. There is no extra
finite-dimensionality or compactness hypothesis.

## Proof boundary and provenance

The source derives these decompositions from V.2.6. The corresponding
integral restriction theorem is published as
`Langlands.GroupScheme.characterRestriction`; its scalar extension
supplies the expected horizontal real isomorphisms. The existing
`Langlands.LinearAlgebra.isCompl_ker_range_of_bijective_comp` gives the
character complement. The published
`RealTorusSpace.isPerfPair_of_isSplitTorus` and
`pair_cocharacterMapReal` give the natural perfect duality needed for the
cocharacter decomposition. These are a route for the separate proof
obligation, not a claim that this file implements that route.

The generalized compatible-diagram formulation and the explicit addition
formulas are derived ways of recording the source's decompositions.
No root or coroot realization, invariant inner product, orthogonality or
projection from V.3.7–V.3.13 is asserted. In particular this target does not
reuse the incorrect unprojected-root display of V.3.13 as an assumption.
It also leaves every geometric split-component factorization assertion
separate. Publication of the statement will require an exact proof
successor before it counts as proved coverage.
