# Original CM coefficient actions over ordered small levels and all exponents

Author: Worker 57.

This internal construction assembles the original CM Harris coefficient actions
and actual canonical-lattice inclusions over the existing ordered category of
sufficiently small CM levels. It retains the full original exponent inverse
system, its scalar ring and its inverse-unop action convention. The ordinary
coefficient levels and their group equivalences are natural in the CM level,
and every original exponent reduction is natural across all level inclusions.

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, in universe zero.

## Exact arithmetic inputs and existing level index

The inputs are number fields `E` and `F`, with `E` totally real, `F` totally
complex and CM, an `E`-algebra structure on `F`, and
`IsQuadraticExtension E F`. The ring `A` has its compatible `E`, `F` and
rational algebra structures and scalar towers `E → F → A`, `ℚ → E → A`,
and `ℚ → F → A`. Fix `n : ℕ`,
`D : CentralSimpleUnitaryData E F A n`, and `Module.Finite ℚ A`.
Write `σ = D.rationalInvolution` and `G = σ.FiniteAdelicPoints`.
The finite rational algebra premise supplies the existing topological-group
structure needed by the inverse-opposite constructions.

The coefficient data are a number field `K`, a finite-dimensional `K`-module
`W`, an algebraic representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`, and a
rational finite place `p`. Put `R = HarrisCoefficientIntegers K p`.
The normalizing lemmas omit the unused `IsCMField F` and two scalar-tower
class arguments exactly as indicated in their Lean declarations.

The index is the already constructed `OrderedSmallCMLevel D` from
`HarrisTaylorCMSmallLevelIndex`. Its objects are the original compact open
levels of `Gᵐᵒᵖ` with their actual `σ.LevelSufficientlySmall` certificate;
its arrows retain only subgroup inclusions. For an object `U`, let

```text
small(U) = (orderedSmallCMLevelToSmallCMLevel D).obj U.
```

This is the existing object in the original small transporter category, with
the same underlying compact open subgroup and smallness certificate. The
construction uses the existing `orderedSmallCMLevelForget` functor to the
ordered compact levels. It neither introduces another smallness predicate
nor requires a premise that this index is nonempty.

## Ordinary levels and natural inverse-unop groups

Write `U^o = CompactOpenLevel.inverseOpposite U.val`. This is the existing
ordinary compact open level obtained by inverse image under the continuous
group equivalence `G → Gᵐᵒᵖ`, `g ↦ op(g⁻¹)`.

`cmHarrisOrdinaryLevelFunctor` sends `U` to `U^o` in
`CompactOpenLevel.Ordered G`. For an inclusion `f : U → V`, its map is the
ordered arrow supplied by
`CompactOpenLevel.inverseOpposite_mono (leOfHom f)`. Identity and composition
hold because the target category is thin. Its `obj` lemma identifies the
exact ordinary level by reflexivity.

`cmHarrisOrderedGroups` is exactly

```text
orderedSmallCMLevelForget D ⋙ orderedSubgroupFunctor Gᵐᵒᵖ.
```

Thus its vertex is the original opposite-level subgroup, and each arrow is
its actual same-element inclusion. The ordinary subgroup diagram instead
composes `cmHarrisOrdinaryLevelFunctor` with `orderedSubgroupFunctor G`.

`cmHarrisOrderedGroupIso` is a natural isomorphism from the original group
diagram to that ordinary subgroup diagram. Its component is exactly the
existing `CompactOpenLevel.inverseOppositeEquiv U.val`, packaged as a group
isomorphism. On an original opposite-group element `g`, this is the original
inverse-unop value `(unop g)⁻¹`. Group-morphism extensionality reduces
naturality under a level inclusion to reflexivity on each `g`. The
`hom_app` lemma identifies the original component homomorphism by reflexivity.
The new natural isomorphism is in `GrpCat`.

## Actual coefficient diagrams and the entire exponent functor

For any `m : ℕ`, put `I = harrisCoefficientScalarIdeal K p m`, the span of
the natural scalar `m` in the full integral coefficient ring `R`. Let `Λ_U`
be the original canonical full Harris lattice constructed at `U^o`. At
`k : ℕᵒᵖ`, the coefficient module is the original reduction

\[
 M_{U,k}=\Lambda_U/(I^{k.unop}\,\Lambda_U),
\]

with the precise submodule `I ^ k.unop • ⊤` and the unchanged scalar ring `R`.

`cmHarrisCoefficientLevelDiagram m k` has underlying level functor exactly

```text
cmHarrisOrdinaryLevelFunctor D ⋙
  ((harrisTorsionLevelSystem ρ p m).obj k).obj
```

That is, its `.obj` is the composite of the ordinary-level functor with the
entire underlying generic torsion-level diagram. Its action at `U` is
exactly the original
`((cmHarrisTorsionSystem D ρ p (small U) m).obj k).ρ`.
Its transition-equivariance field is the `comm` field of the original
`cmHarrisTorsionSystemInclusion` for `small(U) ≤ small(V)`. The latter
compares the independently constructed canonical lattices and restricts the
target action along the actual original subgroup inclusion.

The entry definition `cmHarrisCoefficientLevelSystem m` constructs a functor

\[
 \mathbb N^{op}\longrightarrow
 \operatorname{EquivariantDiagram}
   (\operatorname{cmHarrisOrderedGroups}(D),R\text{-Mod}).
\]

Its value at `k` is the preceding level diagram. For `f : i → j`, the
component at `U` is precisely the underlying linear map of the original
`(cmHarrisTorsionSystem D ρ p (small U) m).map f`. Applying
`congrArg Action.Hom.hom` to naturality of the original CM inclusion and
reversing the equality proves naturality across level inclusions. The
original reduction's `comm` field gives equivariance. Extensionality for
equivariant-diagram morphisms and natural transformations reduces exponent
identity and composition to those of the same original CM torsion system.

The `obj_forget` lemma identifies the complete underlying level functor with
the generic diagram reindexed through the ordinary-level functor, including
its maps. The `obj_obj`, `level_map` and `exponent_map` lemmas identify each
vertex, actual CM included-vector map and unchanged original exponent
reduction by reflexivity.

## Original actions, representatives and coherence

The `action` lemma gives exactly

\[
 \rho^{CM}_{U,k}(g)
  =\rho^{ordinary}_{U^o,k}
     (\operatorname{inverseOppositeEquiv}(U)(g)).
\]

The `action_mk` lemma identifies its value on an original lattice class
with the class of the original ambient lattice operator at that same
inverse-unop element. The `level_map_mk` lemma sends the class of `x ∈ Λ_U`
to the class of
`harrisLatticeInclusion ρ p V^o U^o ... x`. Thus it retains the same ambient
tensor coefficient vector in the two original lattices.

For a level arrow `h : U → V`, write `j_k(h)` for the actual coefficient
inclusion at exponent `k`. For an exponent arrow `f : i → j`, write
`r_U(f)` for the original CM exponent reduction. The `square` theorem is
naturality of the constructed exponent map:

\[
 j_i(h)\,;\,r_V(f)=r_U(f)\,;\,j_j(h).
\]

This holds for every level and exponent arrow with the original CM actions
already retained in the equivariant-diagram fields.

`cmHarrisTorsionSystemInclusion_comp` concerns the named original maps at
arbitrary small CM levels `T ≤ V ≤ U`:

\[
 j_{T,V,k}\,;\,j_{V,U,k}=j_{T,U,k}.
\]

`cmHarrisTorsionSystemInclusion_refl` identifies the original reduced
inclusion at an unchanged small level with the identity. Both statements
are equalities of the underlying integral module maps; their actions vary
with the actual level groups as assembled above. Their proofs directly
apply the generic composition and identity theorems at the original
inverse-opposite ordinary levels, using the proved monotonicity of those
levels. They do not choose additional comparison maps.

Every natural scalar `m`, including zero, and every exponent, including
zero, is admitted. No finiteness or invertibility assertion for the reduced
lattice maps is made here.

## Provenance and remaining scope

This is an internal deduction from the direct imports
`Coefficients.HarrisLatticeLevelSystem`,
`HarrisTaylorCMCoefficientLatticeComparison` and
`HarrisTaylorCMSmallLevelIndex`. They supply the full generic level/exponent
coherence, the actual original CM inclusion maps and inverse-unop actions,
and the existing ordered sufficiently small CM index. Monotonicity constructs
the ordinary-level functor; pointwise extensionality proves the natural group
isomorphism. Reindexing the generic underlying coefficients and using the
original CM action and naturality fields constructs the complete exponent
functor. Reflexivity and the generic inclusion laws give the displayed
normalizations and composition identities. No additional external-source
assertion is introduced.

This unit supplies arithmetic coherence for the original CM level actions
and canonical coefficient lattices. Further descended geometric
coarse-refinement coherence, Hecke transporter compatibility and rational
adic independence remain separate. The exact representability, named moduli,
arithmetic-existence, source-comparison and canonical-model obligations of
the containing task remain explicit or unfinished. This focused arithmetic
construction does not complete that task.
