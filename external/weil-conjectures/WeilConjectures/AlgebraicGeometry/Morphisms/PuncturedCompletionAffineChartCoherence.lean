/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineChartTransitions
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionChartGeneratorCoherence

/-!
# Coherence of affine chart section transitions

## References

* Stacks Project, Tag 0BLH, first two proof paragraphs
* Tag 05EL, item (1)
* Stacks Project, Tag 0BLH, second proof paragraph (the object check)
* Tag 05EL, item (1), its square and cocycle clauses
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace FormalGlueing

variable {R S : Type u} [CommRing R] [CommRing S]

private noncomputable def scalarEndHom (ρ : R →+* S) (M : ModuleCat.{u} S) :
    S →+* Module.End R (restrict ρ M) where
  toFun s :=
    { toFun := fun m ↦ s • (m : M)
      map_add' := smul_add s
      map_smul' := fun r m ↦ smul_comm s (ρ r) m }
  map_one' := by ext m; exact one_smul S m
  map_mul' s t := by ext m; exact mul_smul s t m
  map_zero' := by ext m; exact zero_smul S m
  map_add' s t := by ext m; exact add_smul s t m

private theorem piece_units (f : R) (M : ModuleCat.{u} (Localization.Away f))
    (a : Submonoid.powers f) :
    IsUnit (algebraMap R (Module.End R (piece f M)) a) := by
  change IsUnit (scalarEndHom (algebraMap R (Localization.Away f)) M
    (algebraMap R (Localization.Away f) a))
  exact (IsLocalization.map_units (Localization.Away f) a).map
    (scalarEndHom (algebraMap R (Localization.Away f)) M)

private noncomputable def localEndHom (f : R) (M : ModuleCat.{u} R) :
    Module.End R M →+* Module.End R (localize f M) where
  toFun := IsLocalizedModule.map (Submonoid.powers f)
    (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ M)
  map_one' := IsLocalizedModule.map_id _ _
  map_mul' h k := IsLocalizedModule.map_comp' _ _ _ _ k h
  map_zero' := map_zero _
  map_add' := map_add _

private theorem localEndHom_scalar (f : R) (M : ModuleCat.{u} R) (r : R) :
    localEndHom f M (algebraMap R (Module.End R M) r) =
      algebraMap R (Module.End R (localize f M)) r := by
  ext x
  induction x using LocalizedModule.induction_on with
  | _ m t =>
    change IsLocalizedModule.map (Submonoid.powers f)
      (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ M)
      (algebraMap R (Module.End R M) r) (LocalizedModule.mk m t) =
      r • LocalizedModule.mk m t
    rw [IsLocalizedModule.map_LocalizedModules]
    exact (LocalizedModule.smul'_mk r m t).symm

private theorem localize_units (f : R) (M : ModuleCat.{u} R) (r : R)
    (h : IsUnit (algebraMap R (Module.End R M) r)) :
    IsUnit (algebraMap R (Module.End R (localize f M)) r) := by
  rw [← localEndHom_scalar]
  exact h.map (localEndHom f M)

private noncomputable def baseEndHom (φ : R →+* S) (M : ModuleCat.{u} R) :
    Module.End R M →+* Module.End R (restrict φ (extend φ M)) := by
  letI : Algebra R S := φ.toAlgebra
  exact
    { toFun := fun h ↦ restrictMap φ (extendMap φ h)
      map_one' := by
        ext x
        simp [extendMap, restrictMap]
      map_mul' := fun h k ↦ by
        simp only [Module.End.mul_eq_comp, extendMap, LinearMap.baseChange_comp]
        rfl
      map_zero' := by
        ext x
        simp [extendMap, restrictMap]
      map_add' := fun h k ↦ by
        ext x
        simp [extendMap, restrictMap] }

private theorem baseEndHom_scalar (φ : R →+* S) (M : ModuleCat.{u} R) (r : R) :
    baseEndHom φ M (algebraMap R (Module.End R M) r) =
      algebraMap R (Module.End R (restrict φ (extend φ M))) r := by
  let : Algebra R S := φ.toAlgebra
  ext x
  change (LinearMap.baseChange S (algebraMap R (Module.End R M) r)) x = r • x
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [Module.algebraMap_end_apply, TensorProduct.tmul_smul]
  | add x y hx hy => simp [hx, hy, smul_add]

private theorem extend_units (φ : R →+* S) (M : ModuleCat.{u} R) (r : R)
    (h : IsUnit (algebraMap R (Module.End R M) r)) :
    IsUnit (algebraMap R (Module.End R (restrict φ (extend φ M))) r) := by
  rw [← baseEndHom_scalar]
  exact h.map (baseEndHom φ M)

end FormalGlueing

namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The section transition maps satisfy the two coherence equations of formal glueing.
This checks maps already supplied; it constructs no section module or equivalence.
-/
theorem affine_chart_transition_coherence
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U)
    (hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)))
    (T : AffineChartTransitions D t f) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let F := T.F
    (∀ i j : Fin t,
      (FormalGlueing.extendMapR φ (F.alpha_overlap i j).toLinearMap).comp
          ((FormalGlueing.compare φ (f j) (FormalGlueing.piece (f i) (F.M i))).comp
            (FormalGlueing.localMap (f j) (F.alpha i).toLinearMap)) =
        (FormalGlueing.compare φ (f i) (FormalGlueing.piece (f j) (F.M j))).comp
          ((FormalGlueing.localMap (f i) (F.alpha j).toLinearMap).comp
            (FormalGlueing.swap (f i) (f j) (FormalGlueing.restrict φ F.M')))) ∧
    (∀ i j k : Fin t,
      (FormalGlueing.localMap (f i) (F.alpha_overlap j k).toLinearMap).comp
          ((FormalGlueing.swap (f i) (f k) (FormalGlueing.piece (f j) (F.M j))).comp
            (FormalGlueing.localMap (f k) (F.alpha_overlap i j).toLinearMap)) =
        (FormalGlueing.swap (f i) (f j) (FormalGlueing.piece (f k) (F.M k))).comp
          ((FormalGlueing.localMap (f j) (F.alpha_overlap i k).toLinearMap).comp
            (FormalGlueing.swap (f j) (f k) (FormalGlueing.piece (f i) (F.M i))))) := by
  obtain ⟨hsquare, hcocycle⟩ := affine_chart_transition_generator_coherence D t f hf hV T
  constructor
  · intro i j
    apply IsLocalizedModule.ext (Submonoid.powers (f j))
      (LocalizedModule.mkLinearMap _ (FormalGlueing.localize (f i)
        (FormalGlueing.restrict _ T.F.M')))
    · intro a
      exact FormalGlueing.extend_units (algebraMap A
          (AdicCompletion (IsLocalRing.maximalIdeal A) A)) _ (a : A)
        (FormalGlueing.localize_units (f i) _ a
          (FormalGlueing.piece_units (f j) (T.F.M j) a))
    · apply IsLocalizedModule.ext (Submonoid.powers (f i))
        (LocalizedModule.mkLinearMap _ (FormalGlueing.restrict _ T.F.M'))
      · intro a
        exact FormalGlueing.extend_units (algebraMap A
          (AdicCompletion (IsLocalRing.maximalIdeal A) A)) _ (a : A)
          (IsLocalizedModule.map_units
            (LocalizedModule.mkLinearMap _ (FormalGlueing.piece (f j) (T.F.M j))) a)
      · ext m
        exact hsquare i j m
  · intro i j k
    apply IsLocalizedModule.ext (Submonoid.powers (f k))
      (LocalizedModule.mkLinearMap _
        (FormalGlueing.localize (f j) (FormalGlueing.piece (f i) (T.F.M i))))
    · intro a
      exact FormalGlueing.localize_units (f i) _ a
        (FormalGlueing.localize_units (f j) _ a
          (FormalGlueing.piece_units (f k) (T.F.M k) a))
    · apply IsLocalizedModule.ext (Submonoid.powers (f j))
        (LocalizedModule.mkLinearMap _ (FormalGlueing.piece (f i) (T.F.M i)))
      · intro a
        exact FormalGlueing.localize_units (f i) _ a
          (IsLocalizedModule.map_units
            (LocalizedModule.mkLinearMap _ (FormalGlueing.piece (f k) (T.F.M k))) a)
      · ext m
        exact hcocycle i j k m

end AlgebraicGeometry.Scheme.CompletionGluingData
