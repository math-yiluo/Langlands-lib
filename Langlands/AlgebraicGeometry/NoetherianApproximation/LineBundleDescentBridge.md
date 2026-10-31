# Shared lemmas for the line bundle descent bridges

This module contains no ported FLT code. It supplies what both bridge proofs need:
`LineBundleIsoSubalgebraDescentProof.md` (proof of `LineBundleIsoSubalgebraDescentStatement`) and
the proof of `LineBundleSubalgebraDescentStatement` that task `77b7fc2e-2a25-41e0-9a83-e4fe509968de`
prepares in module `LineBundleSubalgebraDescentProof`. Both bridges apply ported FLT theorems (Anthropic FLT Lean source at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, Apache-2.0). Those theorems are stated for an
arbitrary directed system of rings with a direct limit (FLT's predicate `IsDirectLimit`, from
`Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`) and for FLT's notion
`Scheme.Modules.IsInvertible` (from
`Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor`). Every result
below is internal infrastructure. None is a statement taken from the literature.

## Invertible modules

1. **`Langlands.AlgebraicGeometry.Picard.isInvertible_of_isLocallyFreeRankOne`.**
   This direction is imported from `Picard.NoetherianLineBundleSeesawProof`.
   FLT's `IsInvertible M` asks every point to have
   an open `U` with `(Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit _`.
   The Library's `IsLocallyFreeRankOne M` gives the same with `M.restrict U.ι` in place of the
   pullback. Composing with the inverse of Mathlib's `Scheme.Modules.restrictFunctorIsoPullback U.ι`,
   applied at `M`, turns one into the other.
2. **`isLocallyFreeRankOne_of_isInvertible`.** The converse, composing with
   `Scheme.Modules.restrictFunctorIsoPullback U.ι` applied at `M`.

## Pullbacks of modules

3. **`nonempty_iso_pullback_of_fac`.** Let `c ≫ b = a`. If the pullbacks of `M` and `N` along
   `b` are isomorphic, then so are their pullbacks along `a`. Pull the isomorphism back along
   `c` and conjugate it by `Scheme.Modules.pullbackComp c b` at `M` and at `N`.
4. **`nonempty_iso_pullback_pullback_iff`.** The iterated pullbacks along `g`, then `f`, are
   isomorphic exactly when the pullbacks along `f ≫ g` are. Both directions conjugate by
   `Scheme.Modules.pullbackComp f g`.
5. **`nonempty_iso_pullback_of_section`.** Let `e : P ⟶ X` and `e' : X ⟶ P` with `e' ≫ e = 𝟙 X`,
   and let `w : X ⟶ Q`. If `(pullback (e ≫ w)).obj L ≅ (pullback e).obj M`, then
   `(pullback w).obj L ≅ M`. Pull the given isomorphism back along `e'`. On the left,
   `Scheme.Modules.pullbackComp e' (e ≫ w)` and `Scheme.Modules.pullbackCongr` for
   `e' ≫ e ≫ w = w` identify the result with `(pullback w).obj L`. On the right,
   `Scheme.Modules.pullbackComp e' e`, `Scheme.Modules.pullbackCongr` for `e' ≫ e = 𝟙 X` and
   `Scheme.Modules.pullbackId X` identify it with `M`.

## The directed system of finitely generated subalgebras

- `FGIndex A₀ A` is `{T : Subalgebra A₀ A // T.FG}` with the induced order. `FGStage T` is
  the ring `↥T.1`. The index type is nonempty (it contains `⊥`, by `Subalgebra.fg_bot`) and
  directed (the supremum `S ⊔ T` is finitely generated, by `Subalgebra.FG.sup`).
- `fgTransition S T h` is the inclusion `Subalgebra.inclusion` as a ring homomorphism, and
  `fgToLimit T` is `T.1.val`, the inclusion into `A`. The `DirectedSystem` laws hold by `rfl`.
- `fgIsDirectLimit`: `A` is the direct limit in FLT's sense. Every `m : A` lies in the finitely
  generated subalgebra `Algebra.adjoin A₀ {m}` (`Subalgebra.fg_adjoin_finset`). Two elements of
  stages `S` and `T` with equal images in `A` become equal in `S ⊔ T`. Compatibility holds by
  `rfl`.
- `algebraMap_fgStage`: the structure map `algebraMap (FGStage T) A` of the subalgebra is
  `fgToLimit T`, by `rfl`.
- `spec_map_fgToLimit_comp`, `spec_map_fgTransition_comp` and `spec_map_fgToLimit_fgTransition`
  record three identities of morphisms of affine schemes:
  `Spec.map (fgToLimit T) ≫ Spec.map (algebraMap A₀ T) = Spec.map (algebraMap A₀ A)`,
  `Spec.map (fgTransition S T h) ≫ Spec.map (algebraMap A₀ S) = Spec.map (algebraMap A₀ T)`, and
  `Spec.map (fgToLimit T) ≫ Spec.map (fgTransition S T h) = Spec.map (fgToLimit S)`.
  Each follows from `Spec.map_comp` and `CommRingCat.ofHom_comp`, and the composites of ring maps
  agree by `rfl`.

## Direct-limit presentation

The FLT implementation lead suggests the `SubalgebraStages` presentation from the port of
scheme-descent task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`. That port (candidate `57b4d321-06cc-40f3-af43-291f12e845c7` of task
80ab0ad1) describes the cofiltered diagram of schemes `X₀ ×_{A₀} Spec (S i)` and its cone. It has no
ring-level `IsDirectLimit` instance, and the FLT line-bundle theorems need exactly that. So this
module builds its own small presentation (`FGIndex`, `fgTransition`, `fgToLimit`,
`fgIsDirectLimit`) on the whole system of finitely generated subalgebras. It uses FLT's
`IsDirectLimit` from `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`. That
module belongs to task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83` and is imported from its port, not
ported again.
