# Descent of geometric connectedness to finitely generated subalgebras (proof)

Author: Worker 299, for task `ab019f66-cba5-4921-aa53-b9cfb52e5456`. The lemma used in `of_ring`
(module `GeometricallyConnectedOfGenericFibre`) is by Worker 946.

## Statement proved

`Langlands.AlgebraicGeometry.NoetherianApproximation.geometricallyConnectedSubalgebraDescent :
GeometricallyConnectedSubalgebraDescentStatement.{u}`, for an arbitrary universe `u`, with no further
hypotheses. The proposition is the published one of module
`Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements` (statement artifact
`a25bcdd5-03da-45b4-a0d3-100bb603e7c5`). Take a noetherian commutative ring `A₀` and a commutative
`A₀`-algebra `A`, both in `Type u`. Let `f : X ⟶ Spec A₀` be proper and smooth, with geometrically connected base
change `pullback.snd f (Spec.map (algebraMap A₀ A))`. Then for every finite set `s ⊆ A` there is a
finitely generated `A₀`-subalgebra `T ⊇ s` of `A` such that the base change
`pullback.snd f (Spec.map (algebraMap A₀ ↥T))` is geometrically connected.

The statement module's Markdown cites the source: Stacks Project, *More on Morphisms*, tag 0E0N,
together with *Limits of Schemes*, Lemma 32.4.10 (tag 05F4). The implemented proof does not follow
that route. It follows the FLT proof described below.

## Proof

The module first proves four auxiliary lemmas and two theorems in the namespace
`Langlands.AlgebraicGeometry.NoetherianApproximation.GeometricallyConnectedSubalgebraDescentProof`.
The main theorem, in `Langlands.AlgebraicGeometry.NoetherianApproximation`, comes last.

Auxiliary lemmas:

- `iff_of_isPullback`: for a property `P` of morphisms that respects isomorphisms and a pullback square
  with sides `g` and `f`, `P (pullback.snd f ι) ↔ P g`.
- `exists_isPullback_of_fac`, `exists_isPullback_comp`: take ring maps `β : A₀ → B`, `δ : B → C` and
  `γ = δ ∘ β`. Then the base change of `f` along `γ` is a pullback of its base change along `β`,
  along `Spec δ`.
- `surjective_specMap_of_field`: `Spec L ⟶ Spec K` is surjective for every map of fields `K → L`.
- The scoped instance `descendsAlong` registers the ported FLT theorem
  `AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective`: geometric connectedness
  descends along surjective morphisms.

`of_ring`. Take ring maps `τ : A₀ → T`, `φ : T → R` and an injective `ψ : R → L`, where `R` is a
noetherian integrally closed domain and `L` is a field, with `f` proper and smooth. Assume that the
base change of `f` along `ψ ∘ φ ∘ τ` is geometrically connected. Then for every point `c` of `Spec R`
with image `t` in `Spec T`, the fibre over `t` of the base change `f_T` of `f` to `T` is
geometrically connected. Proof:

1. Let `K = Frac R` and `ψK : K → L` the extension of `ψ`. The base change of `f` to `L` is a pullback
   of its base change `f_K` to `K`, along the surjection `Spec L ⟶ Spec K`. So `f_K` is geometrically
   connected, by descent.
2. Let `f_R` be the base change of `f` to `R` (along `φ ∘ τ`). Its generic fibre, its base change
   along `R → K`, is `f_K` up to a pullback square, so it is geometrically connected
   (`iff_of_isPullback`). `f_R` is proper and smooth, as a base change of `f`.
3. Worker 946's lemma
   `Langlands.AlgebraicGeometry.NoetherianApproximation.geometricallyConnected_of_smooth_of_geometricallyConnected_pullback_snd`
   then makes `f_R` geometrically connected. So is its fibre over `c`, by Mathlib's instance for
   fibres of geometrically connected morphisms.
4. The base change of `f` to `R` is a pullback of `f_T` along `Spec φ`
   (`exists_isPullback_comp`). By Mathlib's `isPullback_fiberToSpecResidueField_of_isPullback`, the
   fibre of `f_R` over `c` is therefore the base change of the fibre of `f_T` over `t`, along
   `Spec κ(c) ⟶ Spec κ(t)`. This map is surjective, so descent finishes the proof.

`exists_ring`. Take an injective ring map `ι : T → A` with `T` noetherian, and a point `t` of
`Spec T`. Then there are a noetherian integrally closed domain `R`, a field `L`, maps `φ : T → R`,
`ψ : R → L` with `ψ` injective and `α : A → L`, with `ψ ∘ φ = α ∘ ι`, and a point `c` of `Spec R`
over `t`. Construction:

- Choose a minimal prime `η ⊆ t` of `T` (Mathlib's `Ideal.exists_minimalPrimes_le`). Since `ι` is
  injective, `η` is the contraction of a prime `𝔮` of `A`
  (`Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective`). Let `L = Frac(A/𝔮)` and
  `α : A → A/𝔮 → L`.
- If `t = η`, take `R = L`, `ψ = id`, `φ = α ∘ ι` and `c` the unique point.
- Otherwise `P = t (T/η)` is a nonzero prime of the domain `D = T/η`, so the local ring `D_P` is not a
  field. The ported FLT theorem
  `IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates` gives a discrete valuation
  ring `V` of `Frac D` that contains `D_P` and dominates it. Take `R = V` and `c` its closed point.
  `φ` is `T → D → D_P → V`, and `ψ` is `V ⊆ Frac D → L`, induced by the injection `D → A/𝔮`.
  Domination shows that `c` lies over `t`.

Main theorem. Let `T = A₀[s]`, the `A₀`-subalgebra generated by `s`. It is finitely generated, hence
noetherian. By Mathlib's `GeometricallyConnected.iff_geometricallyConnected_fiber`, it suffices to
show that the fibre of `f_T` over each point `t` of `Spec T` is geometrically connected. Apply
`exists_ring` to the inclusion `T → A` and `t`. The base change of `f` along
`ψ ∘ φ ∘ (A₀ → T) = α ∘ (A₀ → A)` is a base change of the geometrically connected base change of `f`
to `A`, so it is geometrically connected. Then `of_ring` gives the claim.

## Source and licence

Adapted from `P2M/Sol/S_AlgebraicGeometry_GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd.lean`
of the Anthropic Lean formalisation of Fermat's Last Theorem, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (literature id
`anthropic-flt-complete-lean-source-6e837e75`). Apache License 2.0, Copyright 2026 Anthropic, PBC.
See `licenses/Anthropic-FLT/` (`LICENSE`, `NOTICE`, `ATTRIBUTION.md`) in the Library. The Lean file
begins with an attribution header stating that it was modified.

## Changes against the FLT file

- Generic fibre step of `of_ring`. In FLT, `f_K` is smooth, hence geometrically integral
  (`AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected`). So the generic
  fibre of `f_R` is geometrically reduced. `f_R` is proper and flat, so
  `AlgebraicGeometry.geometricallyConnected_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_pullback_snd`
  makes it geometrically connected. Here the code instead records that `f_R` is smooth and applies
  `geometricallyConnected_of_smooth_of_geometricallyConnected_pullback_snd`. That lemma's proof uses
  the Library theorem `Langlands.AlgebraicGeometry.fieldSmoothProperConnectedGlobalFunctions` and the
  ported FLT theorem
  `AlgebraicGeometry.geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd`.
  The two FLT imports for the replaced step, and their chain of regular-local-ring modules, are
  therefore not used. The unused `let fT` of the FLT proof is also removed.
- The FLT theorem `solution`, with explicit binders, becomes
  `geometricallyConnectedSubalgebraDescent : GeometricallyConnectedSubalgebraDescentStatement.{u}`.
  Its proof starts with `intro A₀ _ _ A _ _ X f _ _ _ s`. After that, the FLT proof text is
  unchanged.
- Imports. The statement module and `GeometricallyConnectedOfGenericFibre` are added. The two
  remaining FLT `Theorems` imports are renamed to their ported modules `Langlands.AnthropicFLT.…`.
  `P2M.Util` and the explicit `import Mathlib` are dropped; Mathlib is still imported through the
  imported modules.
- The five FLT `attribute [-instance]` and `attribute [-simp]` lines are dropped. They switch
  off instances and simp lemmas declared in other FLT modules. Some of the named declarations, such
  as `RegularLocalRingQuotientAscent.dualNumberFst_apply`, are not in this module's import closure,
  and the module compiles without these lines.
- The FLT lakefile option `set_option backward.isDefEq.respectTransparency.types false` is set in the
  file. A test compile without it gave five errors: failed instance syntheses of `t.asIdeal.IsPrime`,
  of `MorphismProperty.RespectsIso @GeometricallyConnected` and of
  `MorphismProperty.IsStableUnderBaseChangeAlong` for `@IsProper` and `@Smooth`, plus a resulting
  `rcases` failure.
- Namespaces. The FLT file opens the namespace
  `P2MW.S_AlgebraicGeometry_GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd`
  (written `P2MW.<module>` below) at the top and never closes it. The auxiliary declarations move from
  `P2MW.<module>.GeomConnDesc` to
  `Langlands.AlgebraicGeometry.NoetherianApproximation.GeometricallyConnectedSubalgebraDescentProof`.
  `solution` moves from `P2MW.<module>` to `Langlands.AlgebraicGeometry.NoetherianApproximation`,
  under its new name.
- Between `end GeomConnDesc` and `solution`, FLT runs `p2m_reactivate` (from `P2M/Util.lean`). It
  reactivates the scoped extensions of `P2MW.<module>.GeomConnDesc`, among them the scoped instance
  `descendsAlong`. FLT then states `solution` under `open GeomConnDesc in`. The port drops
  `p2m_reactivate` and replaces `open GeomConnDesc in` by a section-level
  `open GeometricallyConnectedSubalgebraDescentProof` before the main theorem. This open makes the
  scoped instance `descendsAlong` available there.
- Cosmetic changes: `haveI` becomes `have`, long lines are wrapped at 100 columns, blank lines in
  proofs are removed, and docstrings are added to `of_ring`, `exists_ring` and the main theorem.

## Dependencies

- `Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements` (Library).
- `Langlands.AlgebraicGeometry.NoetherianApproximation.GeometricallyConnectedOfGenericFibre` (same
  contribution).
- The ported FLT modules
  `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective`
  and
  `Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates`,
  with their import closures. The 24 ported FLT modules of this contribution (12 `Theorems` modules,
  each with its `P2M/Sol` proof module) are new; the rest of the closure is the Library FLT port of
  task `69435287-9f1e-4abd-8483-5e65ff23668a`.
