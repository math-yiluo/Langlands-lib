# Laws for the transport maps of Harris's coefficient systems

## Purpose and provenance

Harris (1999), *Galois properties of cohomological automorphic forms on GL(n)*,
Sections 3-4, printed pp. 306-311, lets the finite-adelic group act on the
cohomology `H^d(S, W)` of the Shimura tower with coefficients in the systems
`ℒ̃_m` attached to `(ρ, W)` and a lattice `ℒ_W`. The Library's level-change maps
for these systems are the transport maps `cmHarrisTransportSheafMap` of
[HarrisTaylorCMLevelTransport](HarrisTaylorCMLevelTransport.md), indexed by
morphisms of scaled levels (`CMScaledLevel`, see
[HarrisTaylorCMScaledLevels](HarrisTaylorCMScaledLevels.md)). This file defines
the stage transition of the coefficient system at a fixed level, read through
the restriction along a scheme map equal to the identity
(`cmHarrisStageTransportMap`), and proves four laws for the transport maps in
terms of it. They are needed to pass from the diagram of transport maps
to an action of the levels on the cohomology of the fixed-level systems:

* along an identity of levels, the transport map is the stage transition, that
  is, the transition map of the coefficient system `cmHarrisCoefficientSystem`
  of that level;
* shifting the exponents of a morphism of scaled levels does not change its
  transport maps;
* raising the exponent of a level multiplies the stage transition by a power of
  `ℓ`;
* a self-transporter of a level by an element of that level has the same
  transport map as the identity. This is the sheaf-level reason why the
  level `U` acts trivially on the cohomology at level `U`.

The file is derived: its definition is a composite of Library maps, it states
and proves properties of Library constructions, and no theorem from the
literature is assumed or transcribed. The generic
inputs are `sheafMap_eq_nsmul_of_refines` of
[EtaleAssociatedTransport](../Coefficients/EtaleAssociatedTransport.md) and the
two laws `sheafMap_id_transition` and `sheafMap_eq_of_twist` of
[EtaleAssociatedTransportLaws](../Coefficients/EtaleAssociatedTransportLaws.md).

## Notation and hypotheses

The variables are those of
[HarrisTaylorCMLevelTransport](HarrisTaylorCMLevelTransport.md): the CM data
`D`, the Library's representability inputs, `q`, `existence`, `geometry`, and
the rigidity hypothesis at every small level,
`hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity ... U.obj`. As there,
`ℓ = harrisCoefficientPrime p`, `R = HarrisCoefficientIntegers K p`,
`X_U = (cmSchemeTower ... q).obj U`, and `U_k` is the coefficient level
`cmHarrisCoefficientLevel D ρ p U ℓ hℓ k`. In the Lean file:

* `transportMap f hk φ hφ` abbreviates `cmHarrisTransportSheafMap ... p ρ f hk φ hφ`,
  for a morphism `f : X ⟶ Y` of scaled levels, stages `k' ≤ k` (`hk`), and a
  scheme map `φ` with `hφ : φ = (cmSchemeTower ...).map f.hom`. It maps the
  restriction along `φ` of the stage-`k` coefficient sheaf of the level of `Y`
  to the stage-`k'` coefficient sheaf of the level of `X`;
* `system U` abbreviates `cmHarrisCoefficientSystem ... U ρ p ℓ hℓ existence
  geometry (hRigid U)`, the coefficient system of the level `U` as a functor of
  the stage, and `(system U).map (homOfLE hk).op` is its transition from stage
  `k` to stage `k'`;
* `stageMap U hk φ e` abbreviates `cmHarrisStageTransportMap ... p ρ U hk φ e`
  (defined below);
* `transportDatum b φ hφ U' hU' V' hV' T hT hTV' hTU' M M' c hc` abbreviates
  `cmNormalTransportDatum`, the transport datum along a transporter `b` of
  small CM levels with common level `T` and coefficient map `c`.

Every statement with a scheme map `φ` assumes `[Etale φ]`, as
`cmHarrisTransportSheafMap` does. Write `ρ_e = (EtalePullback.restrictionCongr R e).hom.app _`
for the identification of the restrictions along `φ` and `𝟙` given by
`e : φ = 𝟙`, and `ι = (EtalePullback.restrictionId (ModuleCat R)).hom.app _` for
the identification of the restriction along the identity.

The whole file uses the finite heartbeat limit `800000`
(`set_option maxHeartbeats 800000`).

## The stage transition at a fixed level

`cmHarrisStageTransportMap ... p ρ U hk φ e` is defined for a small CM level
`U`, stages `k' ≤ k` (`hk`), a scheme map `φ : X_U ⟶ X_U` with `[Etale φ]`, and
`e : φ = 𝟙`. It is the morphism of étale sheaves of `R`-modules on `X_U`

```text
ρ_e ≫ ι ≫ (system U).map (homOfLE hk).op :
  (restriction along φ) ((system U).obj (op k)) ⟶ (system U).obj (op k'),
```

where `restriction along φ` is `EtalePullback.restriction φ (ModuleCat R)`.
Since `φ = 𝟙`, it is the transition of the coefficient system of `U` from stage
`k` to stage `k'`, written with the source of a transport map along `φ`. It is
the right side of the laws below. Unfolding it is
`rw [cmHarrisStageTransportMap]`.

## Transport along an identity

`cmHarrisTransportSheafMap_id_le`: for a scaled level `Y`, stages `k' ≤ k`, and
`φ : X_{Y.level} ⟶ X_{Y.level}` with `hφ : φ = (tower).map (𝟙 Y).hom` and
`e : φ = 𝟙`,

```text
transportMap (𝟙 Y) hk φ hφ = stageMap Y.level hk φ e.
```

This extends `cmHarrisTransportSheafMap_id` of `HarrisTaylorCMLevelTransport`
(the case `k' = k`) to different stages: the transitions of the scaled diagram
along pure stage changes are the transitions of the fixed-level coefficient
system.

Proof. After unfolding `stageMap`, `cmHarrisTransportDatumAt_sheafMap_congr` replaces `φ` by `𝟙` at the
cost of `ρ_e`. Then `sheafMap_id_transition` is applied to the standard datum
of `𝟙 Y` along `𝟙`, with

* `ψ` the map `Y.level / Y_k →* Y.level / Y_{k'}` of the coefficient groups
  (`cmHarrisCoefficientGroups`),
* `a` the transition `(cmHarrisCoefficientEtaleDiagram ...).transition` of the
  normal torsors `X_{Y_k} → X_{Y_{k'}}`,
* `c` the transition of the torsion coefficients
  (`cmHarrisCoefficientDiagram`),
* `w` the tower map of the inclusion of the standard common level `T` into
  `Y_k`.

The comparison map `K(a, 𝟙)` is invertible by
`cmHarrisCoefficientSystem_comparison_isIso`. The three hypotheses of
`sheafMap_id_transition` are checked as follows. The source map followed by the
identification of base change along the identity has first projection the
tower map of the transporter `T ⟶ Y_k` with element `1`, which is the
inclusion (`cmNormalTransportToSource_fst`). The target map is the tower map of
`T ≤ Y_{k'}`, which is `w` followed by `a` (`smallCMInclusion_trans`). The
torsion map of `𝟙 Y` is the stage transition (`cmHarrisTorsionTransport_id`).
The resulting right side is the transition of `cmHarrisCoefficientSystem` by
definition (reduction along `c` followed by the inverse comparison).

## Shifting and raising exponents

* `cmHarrisTorsionTransport_shift`: for `f : X ⟶ Y`, `k₀ : ℕ` and `k' ≤ k`, the
  torsion map of `CMScaledLevel.Hom.shift f k₀` equals that of `f`. It is
  checked on lattice representatives using `cmHarrisTorsionTransport_mk` and
  `cmHarrisLatticeTransport_shift`.
* `cmNormalTransportDatum_sheafMap_congr`: two transport data along the same
  transporter that differ only in their coefficient maps `c₁ = c₂` (with their
  equivariance proofs) have equal transport maps. The proof is `subst` and
  `rfl`. Comparing such data by `sheafMap_eq_of_refines` instead makes the kernel
  unfold the data and time out.
* `cmNormalTransportDatum_sheafMap_nsmul`: if `c₁ = m • c₂` for `m : ℕ`, the
  transport map of the datum with `c₁` is `m` times that of the datum with
  `c₂`. This is `sheafMap_eq_nsmul_of_refines` with the identity of the common
  cover.
* `cmHarrisTransportSheafMap_shift`: for `f : X ⟶ Y`, `k₀`, `k' ≤ k` and `φ` with
  `hφ : φ = (tower).map f.hom`,
  `transportMap (shift f k₀) hk φ hφ = transportMap f hk φ hφ`. The two data have
  the same transporter, levels and common level, so the equality follows from
  `cmNormalTransportDatum_sheafMap_congr` and `cmHarrisTorsionTransport_shift`.
* `cmHarrisTransportSheafMap_raise`: for a small level `U`, exponents
  `n ≤ n'`, stages `k' ≤ k`, and `φ` with
  `hφ : φ = (tower).map (CMScaledLevel.raise U hn).hom` and `e : φ = 𝟙`,

  ```text
  transportMap (CMScaledLevel.raise U hn) hk φ hφ = ℓ ^ (n' - n) • stageMap U hk φ e.
  ```

  The torsion map of the raise is `ℓ ^ (n' - n)` times that of `𝟙 ⟨U, n⟩`
  (`cmHarrisTorsionTransport_raise`, `cmHarrisTorsionTransport_id`), so
  `cmNormalTransportDatum_sheafMap_nsmul` reduces the claim to
  `cmHarrisTransportSheafMap_id_le` for `⟨U, n⟩`.

## Transporters by elements of the level

For a transporter `b : U ⟶ U` write `a_b = b.hom.element` for its translating
element (in the opposite of the finite-adelic group).

* `cmSchemeTower_map_eq_id_of_mem`: if `a_b ∈ U`, the tower map of `b` is the
  identity. This restates `representedCMSchemeTower_map_eq_id_of_mem` for
  `cmSchemeTower`.
* `cmNormalTransportDatum_toTarget_left`: the underlying morphism of the target
  map of `cmNormalTransportDatum` is the tower map of the inclusion `T ≤ V'`. It
  holds by `rfl` and is used to compare target maps of data with different
  transporters without unfolding them.
* `cmNormalTransportDatum_sheafMap_eq_of_mul`: take transporters
  `b₁ b₂ : U ⟶ U`, one scheme map `φ` equal to the tower maps of both, the same
  levels `U' ≤ U`, `V' ≤ U` (normal) and common level `T ≤ U` (normal,
  `T ≤ V'`, with `a_{b_i}⁻¹ T a_{b_i} ⊆ U'` for `i = 1, 2`), and the same
  representations `M` of `U / U'` and `M'` of `U / V'`. Suppose
  `a_{b₂} = a_{b₁} · w` for some `w ∈ U`, and the coefficient maps satisfy
  `c₂ = M.ρ [w] ≫ c₁`, where `[w]` is the class of `w` in `U / U'`. Then the
  transport maps of the two data agree.

  Proof. `sheafMap_eq_of_twist` with `w = 𝟙` on the common cover and the deck
  element `g = [w⁻¹]`. The coefficient condition is `hc` after
  `[w⁻¹]⁻¹ = [w]`. The target maps agree by
  `cmNormalTransportDatum_toTarget_left`. For the source maps it suffices to
  compare first projections (`etaleObjectPullback_hom_ext`). By
  `etaleTorsorPullbackFunctor_ρ_fst` and `cmNormalTransportToSource_fst`, these
  are the tower maps of the transporter `T ⟶ U'` with element `a_{b₂}`, and of
  the transporter `T ⟶ U'` with element `a_{b₁}` followed by the deck map
  `smallCMNormalInverseArrow U U' [w⁻¹]`. Both composite transporters have
  element `a_{b₂} = a_{b₁} · (w⁻¹)⁻¹`.
* `cmHarrisTransportSheafMap_eq_of_mem`: for a scaled level `Y`, a morphism
  `f : Y ⟶ Y` with `a_{f.hom} ∈ Y.level`, stages `k' ≤ k`, and `φ` with
  `hφ : φ = (tower).map f.hom` and `e : φ = 𝟙`,

  ```text
  transportMap f hk φ hφ = stageMap Y.level hk φ e.
  ```

  By `cmSchemeTower_map_eq_id_of_mem` such a `φ` and `e` exist.

  Proof. The standard common level `T` of `𝟙 Y` is contained in that of `f`:
  for `x ∈ T`, `x ∈ Y_k` and `Y_k` is normal in `Y.level`, so
  `a_f⁻¹ x a_f ∈ Y_k`. By `cmHarrisTransportDatumAt_sheafMap_eq`, the transport
  map of `f` may therefore be computed with common level `T`. The torsion map of
  `f` is the action of the class of `a_f` followed by the torsion map of `𝟙 Y`:
  on lattice representatives both send `x` to the class of
  `ρ.harrisAdelic p (smallCMArrowElement D f.hom) x`. For the left side this is
  `cmHarrisLatticeTransport_coe` with exponent difference `0`; for the right side
  it is `cmHarrisCoefficientDiagram_action_mk` and `cmHarrisLatticeTransport_id`,
  and the two lattice actions agree by definition. So
  `cmNormalTransportDatum_sheafMap_eq_of_mul` with `b₁ = 𝟙`, `b₂ = f.hom` and
  `w = a_f` identifies the transport map of `f` with that of `𝟙 Y` along the
  same `φ`, and `cmHarrisTransportSheafMap_id_le` computes the latter.

## Scope

Apart from the composite `cmHarrisStageTransportMap`, the file proves
equalities of sheaf maps only. It constructs no cohomology, no
Galois action and no action of levels on cohomology; those constructions use
these laws separately.
