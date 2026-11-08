# Original coarse Harris coefficients along nested CM levels

Author: Worker 57.

This internal construction compares the existing restrictions of the original
Harris coefficient diagram at `U` to nested small CM levels `T ≤ V ≤ U`.
Its maps come from the literal inclusions `T ∩ U_k ≤ V ∩ U_k`.
It preserves the original full lattice quotient, every exponent reduction and
the original residual actions. It supplies the arithmetic input for a subsequent
comparison of the actual coarse covers under geometric inverse image.

All declarations lie in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Inputs and original objects

All arithmetic carriers have universe zero. Let `E` be a totally real number
field, and `F` a totally complex CM number field, with an `E`-algebra structure
and `IsQuadraticExtension E F`. The ring `A` has compatible `E`, `F` and rational
algebra structures, with scalar towers `E → F → A`, `ℚ → E → A` and `ℚ → F → A`.
Fix `D : CentralSimpleUnitaryData E F A n` and `Module.Finite ℚ A`.

Let `K` be a number field and `W` a finite-dimensional `K`-module, with
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`.
Fix a rational finite place `p`, a natural scalar `m`, and `hm : m ≠ 0`.
Write `R = HarrisCoefficientIntegers K p`.

The levels `U V T : SmallCMLevel D` satisfy
`hVU : V.obj.subgroup ≤ U.obj.subgroup` and
`hTV : T.obj.subgroup ≤ V.obj.subgroup`; put `hTU = hTV.trans hVU`.
No normality of these level inclusions is assumed.

Let `U_k` denote the original `cmHarrisCoefficientLevel` at `U`. The original
`cmHarrisCoarseCoefficientLevel` constructions give

```text
N_V,k = V ∩ U_k,          N_T,k = T ∩ U_k.
```

The intersections mean equality of the actual subgroups, with the existing
`SmallCMLevel D` objects. Let `N_V` and `N_T` be their existing opposite-natural
level diagrams, and let

```text
G_V,k = V / N_V,k,        G_T,k = T / N_T,k
```

mean `SmallCMResidualGroup` with the corresponding normal subgroup inside its
coarse level. Normality follows from the original restricted coefficient-action
kernels. It does not require normality of `T` in `V` or of `V` in `U`.
Let `M_V` and `M_T` be the existing `cmHarrisCoarseCoefficientDiagram` for
`(U,V,hVU)` and `(U,T,hTU)`. Their underlying module diagrams are the same original
`cmHarrisCoefficientDiagram` at `U`, with its full ideal-power quotients and
unchanged exponent maps.

## Actual level and group maps

`cmHarrisCoarseTowerLevel_le` proves `N_T,k ≤ N_V,k` by monotonicity of intersection.
`cmHarrisCoarseTowerLevelComparison` packages the original identity-transporter
level inclusions as `N_T → N_V`. Its naturality follows by composing these actual
inclusions. The two `...LevelComparison_projection` and
`...LevelComparison_original` identities state, for every exponent, that

```text
N_T,k → N_V,k → V = N_T,k → T → V,
N_T,k → N_V,k → U_k = N_T,k → U_k.
```

The selected definition `cmHarrisCoarseTowerGroupMap` constructs the natural map
`φ : G_T → G_V` using `QuotientGroup.quotientMapSubgroupOfOfLe` on the actual
level refinement and `T ≤ V`. Naturality follows by quotient induction: both
exponent routes retain the same representative. `...GroupMap_mk` states

```text
φ_k([t]) = [inclusion(T ≤ V)(t)].
```

`cmHarrisCoarseTowerGroupMap_injective` proves injectivity. If the image of `[t]`
is trivial, its representative belongs to `V ∩ U_k`, hence to `U_k`; membership
in `T` gives membership in `T ∩ U_k`, so `[t]` is trivial.
This is injectivity of the residual group map, with no claim about injectivity
of any reduced lattice inclusion.

`cmHarrisCoarseTowerGroupMap_original` proves equality of the full natural
transformations to the original `U/U_k` residual diagram:

```text
φ ; cmHarrisCoarseCoefficientGroupMap(U,V)
  = cmHarrisCoarseCoefficientGroupMap(U,T).
```

Its proof is quotient induction at each exponent.

## Unchanged coefficient diagram

Write `res_φ` for `EquivariantDiagram.groupRestriction (ModuleCat R) φ`.
`cmHarrisCoarseTowerCoefficient_action` proves

```text
(res_φ M_V).ρ k g = M_T.ρ k g.
```

Quotient induction reduces both actions to the same original `U` action.
`cmHarrisCoarseTowerCoefficientIso` constructs

```text
res_φ M_V ≅ M_T
```

with identity underlying natural transformations in both directions.
Its equivariance fields use the proved action equality; the inverse laws are
the identity laws. The `...CoefficientIso_hom` and `...CoefficientIso_inv`
identities explicitly retain the full unchanged underlying coefficient diagram.
All constructions quantify over `ℕᵒᵖ`, including exponent zero.

## Internal provenance and remaining scope

This is derived from `HarrisTaylorCMCoefficientCoarseRestriction` and the
existing group-restriction functor in `VaryingSystemGroupCoverChange`.
Subgroup intersection monotonicity constructs the level maps, actual quotient
maps construct the residual embeddings, and quotient induction identifies their
actions. The coefficient isomorphism changes no original module or reduction.
No external-literature assertion or desired geometric comparison is introduced.

Actual geometric coarse-cover maps, their inverse-image isomorphisms,
normalization of the upper-pair second endpoint, and the original own-system
inverse-image lattice-map composition law remain further obligations.
General commensurability, rational adic independence, Hecke compatibility,
the full source-specific unitary geometry, existence, representability and
canonical-model theorems remain open or separately assigned. This arithmetic
prerequisite does not complete the containing task.
