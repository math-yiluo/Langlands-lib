# Ordinary sections and degree-zero cohomology base change

This internal construction identifies the published cohomology base-change
maps in degree zero with the maps on ordinary sections induced by the actual
sheaf pullback unit. All comparisons use the canonical zeroth-right-derived
identifications.

For a commuting square
`g ≫ f = f' ≫ Spec.map φ`, where `f : X → Spec R`,
`f' : X' → Spec R'`, and `φ : R → R'`, the definition
`sectionsBaseChangeMap` is the composite

`Γ_R(M) → Γ_R(g_*g^*M) → Γ_R(X',g^*M) → Res_R^{R'} Γ_{R'}(g^*M)`.

The first arrow applies relative global sections to the pullback adjunction
unit. The second is `relativeGlobalSectionsCompIso.hom`; the third is the
inverse of `relativeGlobalSectionsBaseRingIso.hom`. Here `Γ_R` denotes
the actual relative global sections functor attached to the indicated
structure map. `sectionsBaseChangeMap_apply` proves that the resulting
map on underlying sections is the component of the pullback unit at the
whole open set.

The selected definition `scalarSectionsBaseChangeMap` is the adjunct of
this map under `ModuleCat.extendRestrictScalarsAdj φ.hom`. Its source is
`R' ⊗_R Γ_R(M)` and its target is `Γ_{R'}(g^*M)`, in the categorical
scalar convention of `ModuleCat.extendScalars`. The accompanying
`_homEquiv` and `_unit` lemmas recover the ordinary sections map.
The `_one_tmul` lemma sends `1 ⊗ x` to the actual pullback-unit image of
`x`. Ordinary and scalar maps are natural in every coefficient
morphism `M → N`, as stated by the two `_naturality` lemmas. These
definitions and identities require no quasi-coherence, flatness, Cartesian
square, or vanishing hypothesis. The schemes and rings lie in arbitrary
universe `u`.

The generic lemma `rightDerivedCompIso_zero` treats abelian categories
with independent object and morphism universes and additive functors
`Φ : C → E`, `P : E → E'`, `T : C → D`, `Ψ : D → E'`, together with
`e : Φ ⋙ P ≅ T ⋙ Ψ`. Its hypotheses are injective resolutions in
`C` and `D`, preservation of homology by `P` and `T`, preservation of
injective objects by `T`, and preservation of finite limits by `Φ`
and `Ψ`. In degree zero the actual comparison is
`P.map(Φ.rightDerivedZeroIsoSelf.hom)`, followed by `e.hom`, then
`Ψ.rightDerivedZeroIsoSelf.inv` at `T.obj X`. The proof cancels the
mapped inverse zeroth-derived isomorphism and applies the published
augmentation identity
`toRightDerivedZero_comp_rightDerivedCompIso` from
`Langlands.Cohomology.SupercuspidalExt.Reciprocity`.

Specializing to global sections and restriction of scalars gives
`relativeCohomologyRestrictScalarsIso_zero` and its inverse formula.
Naturality of the restriction-of-scalars composition isomorphism then
gives `relativeCohomologyBaseRingIso_zero`. These formulas fix the
directions of the canonical identifications used by the cohomology map.

For an actual coefficient sheaf `M`, `baseChangeMap_zero` proves

`baseChangeMap(0) = relativeCohomologyZeroIso(f).hom ≫
sectionsBaseChangeMap ≫ Res( relativeCohomologyZeroIso(f').inv )`.

It retains the hypotheses in the published definition: the positive higher
direct images of `g^*M` along `g` vanish, and pushforwards of injective
coefficient sheaves are acyclic for positive relative cohomology along
`f`. The proof expands the published map, applies
`pushforwardComparison_zero` and the base-ring formula, cancels the
comparison isomorphisms, and uses naturality of the zeroth-derived
identification on the pullback unit.

Finally, `scalarBaseChangeMap_zero` proves

`scalarBaseChangeMap(0) = extendScalars.map(
relativeCohomologyZeroIso(f).hom) ≫ scalarSectionsBaseChangeMap ≫
relativeCohomologyZeroIso(f').inv`.

It requires only the same vanishing of positive higher direct images of
`g^*M`; the published scalar map supplies the injective-pushforward
acyclicity from `pushforwardInjectiveAcyclic`. The proof applies the
injective scalar-adjunction Hom-equivalence to both sides and uses the
semilinear formula and adjunction naturality.

The provenance is internal: the file derives compatibility formulas from
the published comparison, relative-sections, and scalar-adjunction
constructions and pinned Mathlib. It asserts no new external geometric
theorem. In particular, these formulas alone establish neither
invertibility of base change nor the relative cube theorem.
