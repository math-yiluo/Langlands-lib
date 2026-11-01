# Residual-action comparison with actual CM forgetting kernel pairs

This module constructs the residual-action map from a disjoint union of
actual represented CM schemes to the kernel pair of their original
forgetting map. It proves its projection formulas, compatibility with normal
refinement and compatibility with canonical changes of representing
witnesses. Representability remains an explicit hypothesis. The constructed
map is not proved to be an isomorphism.

## The actual schemes and comparison map

Fix a family `R` of the existing `CMLevelRepresentation` witnesses and
sufficiently small levels `V ≤ U`. Write `X_V` for the fine object of
`representedCMSchemeTower ... R` and `p : X_V ⟶ X_U` for
`representedCMNormalProjection ... R U V hVU`. This is the existing
scheme-tower image of the identity-element inclusion transporter. The tower
recovers its morphisms by fully faithful Yoneda preimage from the fixed CM
moduli presheaf; no new choice of transition morphisms is made here.

The residual index type is precisely

```
Q = SmallCMResidualGroup D U V
  = U.obj.subgroup ⧸ V.obj.subgroup.subgroupOf U.obj.subgroup.
```

Its finiteness was proved in `HarrisTaylorCMNormalRefinement` from compactness
of `U` and openness of `V`. Under the explicit inclusion, the denominator
identifies with `V` viewed inside `U`. Relative normality of this subgroup
supplies the quotient-group structure used by the action. Normality in the
whole finite-adelic group is not required.

`representedCMNormalCopies` is Mathlib's actual coproduct of schemes
`∐ (fun _ : Q => X_V)`. `representedCMNormalKernelPair` is the actual scheme
pullback `X_V ×[X_U] X_V` of `p` with itself. The constructions use the
coproducts and pullbacks supplied by `Mathlib.AlgebraicGeometry.Limits`.
They do not replace the schemes by point sets or by topological
double-quotient spaces.

Let `ρ` be `representedCMNormalQuotientAction` on `X_V`. Its action and
invariant projection were already constructed from the original moduli
transitions. `representedCMNormalGraph g` is the pullback lift of
`(𝟙 X_V, ρ g)`. The existing invariant-projection equation
`ρ g ≫ p = p` proves the equality required to form this lift.
The `_fst` and `_snd` lemmas are the two pullback projection equations.
The `_one` lemma identifies the identity residual graph with the diagonal:
pullback extensionality reduces it to those equations and `ρ.map_one`.

`representedCMNormalKernelComparison` is the coproduct descent of these
graphs:

```
κ : (∐ (fun _ : Q => X_V)) ⟶ (X_V ×[X_U] X_V).
```

The `_ι` lemma states that its restriction to summand `g` is exactly the
constructed graph. The `_fst` equation says that its first projection is
the coproduct descent of identity maps; `_snd` says that its second
projection is the descent of `g ↦ ρ g`. Both proofs reduce along the
coproduct inclusions to the graph projection equations. The separate
`representedCMNormalKernelPair_condition` is the pullback condition
`fst ≫ p = snd ≫ p`.

For `g : U.obj.subgroup`, `representedCMNormalGraph_mk_snd` identifies the
second graph projection with the original scheme-tower map at
`smallCMNormalInverseArrow ... g`. This arrow has element `g⁻¹`.
The inherited convention turns the source's right action on frames into
Mathlib's left categorical action by inversion; the original Harris
opposite finite-adelic group is retained.

## Normal refinement

For `W ≤ V ≤ U`, with `W` and `V` normal inside `U`, write
`q : U/W →* U/V` for `smallCMResidualQuotientMap` and
`f : X_W ⟶ X_V` for the underlying morphism of
`representedCMNormalRefinement`. These are the existing quotient map of the
identity and the existing actual forgetting morphism. The imported
equivariance statement is

```
ρ_W(g) ≫ f = f ≫ ρ_V(q(g)).
```

`representedCMNormalCopiesRefinement` is the coproduct descent which maps
summand `g` by `f` to summand `q(g)`. Its `_ι` formula is the coproduct
inclusion equation.

`representedCMNormalKernelPairRefinement` maps
`X_W ×[X_U] X_W` to `X_V ×[X_U] X_V`. It is the pullback lift of the two
source projections followed by `f`. The existing equation that `f`
commutes with projection to `X_U`, together with the source pullback
condition, proves that this lift is defined. Its `_fst` and `_snd` lemmas
give exactly these two composites.

`representedCMNormalGraph_refinement` proves

```
graph_W(g) ≫ kernelRefinement = f ≫ graph_V(q(g)).
```

Pullback extensionality reduces the first projection to an identity law
and the second to the proved equivariance of `f`.
`representedCMNormalKernelComparison_refinement` then proves

```
copiesRefinement ≫ κ_V = κ_W ≫ kernelRefinement
```

by coproduct extensionality and this graph equation.

The `_refl` lemmas prove that both refinement maps are identities when
`W = V`. For the copies this uses the imported identity laws for forgetting
and the residual quotient map, followed by the coproduct identity laws.
For the kernel pair, equality follows after both projections from the
identity law for forgetting.

For `Z ≤ W ≤ V ≤ U` with each fine level normal inside `U`, the `_comp`
lemmas identify the successive refinements with the direct ones. On copies,
the proof checks each inclusion and uses both composition of actual
forgetting and composition of the residual quotient homomorphisms. On
kernel pairs, it checks both projections and uses composition of forgetting.
No geometric cover property is used by any refinement proof.

## Canonical change of representation

Let `R'` be another family representing the same fixed moduli presheaf,
and let `c` be the existing canonical natural isomorphism of the two
represented scheme towers. `representedCMNormalCopiesComparison` is the
coproduct isomorphism induced by `c.app V` on every summand, using
`Sigma.mapIso`. Its `_ι_hom` lemma gives the corresponding inclusion
equation.

`representedCMNormalKernelPairComparison` is an isomorphism between the
two actual forgetting kernel pairs. Its forward map is the pullback lift
of the two source projections followed by `c.hom.app V`; its inverse uses
`c.inv.app V`. Naturality of this same `c` at the original inclusion
`V ⟶ U` proves both pullback compatibility equations. Pullback
extensionality and the inverse identities for `c` prove the two inverse
identities. The four `_hom_fst`, `_hom_snd`, `_inv_fst` and `_inv_snd`
lemmas record the resulting projection formulas. These constructions
comparing copies and kernel pairs do not themselves require normality;
normality is needed for the residual-action graphs.

`representedCMNormalGraph_comparison` uses pullback extensionality and
the already proved equivariance of the canonical normal-action comparison
to identify each graph under these isomorphisms.
`representedCMNormalKernelComparison_comparison` then checks the coproduct
inclusions to prove

```
copiesComparison.hom ≫ κ_R' = κ_R ≫ kernelPairComparison.hom.
```

The two isomorphisms here compare **representing witnesses** for the same
presheaf. They do not assert that `κ` is an isomorphism.

`cmNormalKernelComparison` chooses representations from precisely the
existing `CMRepresentabilityStatement` and returns this constructed map.
Its schemes and forgetting morphism are those of the corresponding
`cmSchemeTower`. It does not prove the representability hypothesis.

## Source, assumptions and remaining obligations

The source is Harris and Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), III.1, printed p.91, one-based PDF p.99,
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The passage defines monodromy-invariant orbits of pairing-compatible
adelic frames and right translation by frame composition. It separately
asserts smooth projective representability, finite-etale forgetting and
the Galois-cover property with group `U/V` at normal small levels.
The coproduct-to-kernel-pair map and its compatibility equations are
derived prerequisites constructed here using the existing action,
invariant forgetting, equivariant refinements and canonical comparison.
This is not a formal proof of those stronger source assertions.

The arithmetic inputs remain the actual totally real field `E`, CM field
`F` quadratic over `E`, central simple unitary datum `D`, imaginary
quadratic field `L` inside `F`, embedding `τ₀`, and CM-compatible Harris
signature charts `C`. The named hypotheses remain explicit: pullback-tensor
preservation, composition, unit coherence, associativity, unitor comparison
and symmetry; Picard-zero pullback stability, Mumford-square and universal
base change; duality naturality, polarization base change, relative finite
Weil transition, rational profinite-integer/adele comparison and torsion
finite etaleness. They are not proved in this module.

The representing witnesses still belong to the existing
`ComponentwiseAdmissibleCMBaseCategory` over `Spec F`. The inherited
component, local Noetherian and geometric-point prerequisites of that
restricted presheaf are retained. No representation on all `F`-schemes is
asserted. Applicable existence, the source's division and global
hypotheses, admissibility and comparison with the original moduli problem
remain obligations outside these conclusions.

In particular, this module proves neither that `κ` is an isomorphism nor
that forgetting is finite etale or surjective. Freeness and transitivity
on geometric fibers, the torsor and Galois-cover assertions, canonical-model
comparison, uniformization and coefficient descent remain unproved here.
Finiteness of the residual index and construction of this comparison do
not imply any of them. All code and prose in this pair are by Worker 57;
the pinned environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
