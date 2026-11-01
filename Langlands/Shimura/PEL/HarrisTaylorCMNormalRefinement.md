# Finite residual groups and equivariant refinements of actual CM schemes

This module proves finiteness of the actual residual level quotients and
constructs equivariant forgetting between represented CM schemes at finer
normal levels. The scheme maps are the existing Yoneda-recovered transitions
of the fixed CM moduli presheaf. Their equivariance, composition, projection
and representation-choice compatibilities are proved. Exact representability
and the named prerequisites remain hypotheses.

## Finite residual quotients

For compact-open levels `U` and `V` in a topological group,
the existing instance in `Langlands.Shimura.EquivariantFormsHecke` supplies

```
Finite (U.subgroup ⧸ V.subgroup.subgroupOf U.subgroup).
```

The compactness of `U` supplies `CompactSpace U.subgroup`. The actual subgroup
`V.subgroup.subgroupOf U.subgroup` is open by
`Subgroup.subgroupOf_isOpen`. Mathlib's
`Subgroup.quotient_finite_of_isOpen` then proves finiteness. This argument
requires neither an inclusion nor normality: it concerns the coset space of
the intersection of `V` with `U`, viewed as a subgroup of `U`.

`SmallCMResidualGroup D U V` abbreviates this same quotient for actual
`SmallCMLevel D` objects. Without relative normality it is still a quotient
type; with the normality instance it carries the usual quotient-group
structure. `smallCMResidualGroup_finite` specializes that existing instance.
The finite-dimensionality in the central simple datum supplies
`Module.Finite F A`, and transitivity supplies `Module.Finite ℚ A`, giving the
existing finite-adelic topological-group instance. No independent topology
or additional rational finiteness input is supplied.

For `W ≤ V` and relative normality of both levels inside `U`,
`smallCMResidualQuotientMap` is the actual homomorphism

```
U/W →* U/V.
```

Here these expressions mean precisely the quotients by the corresponding
`subgroupOf U.obj.subgroup`. The definition reuses
`LevelSpace.normalQuotientMap`, whose construction is the quotient-group map
of the identity homomorphism. Only this group homomorphism is reused from
the topological level-space module. The schemes below remain the actual
represented CM schemes.

The representative equation sends the class of `g : U.obj.subgroup` to the
class of the same `g`. Quotient induction gives surjectivity by choosing that
representative as a lift. The identity and composition equations specialize
the existing quotient-group map laws. Surjectivity here is a statement about
residual group homomorphisms.

## Equivariance of actual scheme forgetting

Fix small levels `W ≤ V ≤ U` with explicit inclusions `hWV` and `hVU`, and
assume `V` and `W` are normal as subgroups of `U`. No normality in the whole
finite-adelic group is required. The existing inverse-right transporter at
either fine level has element `g⁻¹` for `g : U.obj.subgroup`.
`smallCMNormalInverseArrow_inclusion` proves the transporter square

```
inverseRight_W(g) ≫ inclusion_WV =
  inclusion_WV ≫ inverseRight_V(g).
```

Both sides have the same actual group element by the identity laws for
multiplication. The definitions retain all transporter conditions, including
the relative normality used to construct the inverse-right arrows.
`smallCMInclusion_refl` and `smallCMInclusion_trans` similarly prove the
identity and composition laws for the original identity-element inclusions.

The family `R` consists of the existing `CMLevelRepresentation` witnesses.
These are smooth projective representing objects in the exact
`ComponentwiseAdmissibleCMBaseCategory`, with the natural isomorphism from
lifted Yoneda to the fixed moduli presheaf. The imported scheme tower recovers
its maps by fully faithful Yoneda preimage of that presheaf's transitions.

`representedCMNormalRefinement` is a morphism of actions from the `U/W`
action on the actual fine scheme `X_W` to the restriction of the `U/V`
action on `X_V` along `smallCMResidualQuotientMap`. Its underlying scheme
morphism is exactly

```
(representedCMSchemeTower ... R).map (smallCMInclusion D hWV).
```

For equivariance, quotient induction reduces to `g : U.obj.subgroup`. The
representative equations for the quotient actions turn the required square
into the scheme-tower image of the transporter square above. The functor's
composition law proves the equality. The inverse-right convention is the
one already used to convert the original right frame action into Mathlib's
left categorical action; the original Harris opposite group is retained.

The `_over` equation says this same scheme morphism preserves the structure
map to `Spec F`. The `_classes` equation quantifies over every object `S` of
the exact componentwise admissible test category and every morphism
`S ⟶ (R W).base`. Under the representation isomorphism, postcomposition with
the base-tower forgetting map equals the original CM moduli transition at
`smallCMInclusion D hWV`. This is the existing Yoneda class equation at that
inclusion. `ULift` raises the Hom-set universe to the presheaf's existing
codomain without changing its elements.

The `_refl` and `_comp` equations concern the underlying scheme morphisms.
They follow by applying the scheme tower to the proved identity and
composition laws for inclusions. The `_projection` equation proves that
forgetting `X_W → X_V` and then `X_V → X_U` equals the existing invariant
projection `X_W → X_U`. Finally, `_comparison` uses naturality of the same
canonical scheme-tower comparison that identifies the quotient actions for
two exact representing families `R` and `R'`. Thus the refinements and
projections are compatible with that specified comparison.

`cmNormalRefinement` chooses witnesses from precisely
`CMRepresentabilityStatement` and applies this construction. Its underlying
schemes and map are those of the corresponding `cmSchemeTower`. It supplies
no proof of the representability proposition.

## Source, assumptions and remaining obligations

The source is Harris and Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.1, printed p.91, one-based PDF p.99, registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
That passage defines monodromy-invariant frame orbits, forgetting maps and
right translation by frame composition, and asserts the normal-level
Galois-cover property. The finite quotient and equivariant-refinement
interfaces here are derived prerequisites. Their proofs use the actual
compact-open topology, quotient-group laws, transporter identities and the
already constructed exact represented CM tower.

The central simple unitary datum and CM-compatible signature charts remain
explicit. The construction also retains the named pullback-tensor
preservation, composition, unit, associativity, unitor and symmetry inputs;
Picard-zero stability, Mumford-square and universal-base-change inputs;
duality naturality, polarization base change, relative finite Weil
transition, adelic comparison and torsion finite-etale inputs. Tests are
exactly the existing componentwise admissible CM bases, with the inherited
connected-component, local Noetherian and geometric-point field conditions.
No representation assertion on all `F`-schemes is added.

Applicable representability, the division/global hypotheses and comparison
with the original moduli problem remain separate obligations. This module
does not prove that a scheme forgetting map is surjective, finite etale,
free, transitive, a torsor or a Galois cover. Finiteness of the acting group
and equivariance alone do not establish those geometric properties.
Canonical-model comparison, uniformization and coefficient descent also
remain outside the conclusions proved here.
