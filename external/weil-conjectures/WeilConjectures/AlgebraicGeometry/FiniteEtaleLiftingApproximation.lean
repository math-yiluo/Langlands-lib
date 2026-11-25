/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.FiniteEtaleCompletionStage
import WeilConjectures.RingTheory.HenselianApproximationAlgHom
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Finite étale lifting by henselian G-ring approximation

Source: Stacks Project, Fundamental Groups, proof of Lemma 0GS2, the essential-surjectivity
paragraph for a Noetherian G-ring (blueprint: lem-weil-pbc-finite-etale-lifting-approximation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every finite étale cover of the closed fibre of a proper scheme over a henselian G-ring
lifts to a finite étale cover of the scheme, with an isomorphism over the closed fibre.
Source: Stacks Project, proof of Lemma 0GS2, Noetherian G-ring essential-surjectivity paragraph
(blueprint: lem-weil-pbc-finite-etale-lifting-approximation).

Proof:
1. Apply `exists_finiteEtale_completion_stage`: complete at I, lift V by the complete-case
   theorem, and descend its finite presentation to a finite étale cover W over Y_R for a
   finitely presented A-algebra R mapping to the completion. It supplies a map k from Y₀
   to Y_R, both projection identities, and the isomorphism W ×_{Y_R} Y₀ ≅ V.
2. Apply `exists_algHom_approximation_mod_ideal` to the map from R to the completion.
   Its proof presents R by finite generators and relations and applies polynomial
   approximation with N = 1, then descends evaluation through the presentation.
3. The resulting A-algebra map σ : R → A induces s : Y → Y_R by the pullback universal
   property. Equality modulo I and the projection identities of k show that the composite
   Y₀ → Y → Y_R is k, by pullback extensionality.
4. Set U = W ×_{Y_R} Y along s. Base-change stability makes U finite étale. Pullback
   pasting and the equality of the closed-fibre maps give an isomorphism U ×_Y Y₀ ≅
   W ×_{Y_R} Y₀ over Y₀; compose it with the stage-cover isomorphism to V. -/
theorem exists_finiteEtale_lift_of_henselianPair_of_isGRing
    {A : Type u} [CommRing A] (hA : IsGRing A) (I : Ideal A) [HenselianRing A I]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y,
      Nonempty
        (Over.mk (pullback.snd U.hom
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) ≅
          Over.mk V.hom) := by
  let : IsNoetherianRing A := hA.1
  obtain ⟨R, hR, hAR, hfp, c, W, k, hkfst, hksnd, ⟨e⟩⟩ :=
    exists_finiteEtale_completion_stage I f V
  let : CommRing R := hR
  let : Algebra A R := hAR
  let : Algebra.FinitePresentation A R := hfp
  obtain ⟨σ, hσ⟩ := exists_algHom_approximation_mod_ideal I hA c
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let b := Spec.map (CommRingCat.ofHom (algebraMap A R))
  let s : Y ⟶ pullback f b := pullback.lift (𝟙 Y)
    (f ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
      dsimp [b]
      rw [Category.id_comp, Category.assoc, ← Spec.map_comp]
      have hc : σ.toRingHom.comp (algebraMap A R) = RingHom.id A := by
        ext a
        exact σ.commutes a
      change f = f ≫ Spec.map (CommRingCat.ofHom (σ.toRingHom.comp (algebraMap A R)))
      rw [hc]
      simp)
  have hs : pullback.fst f q ≫ s = k := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, s, pullback.lift_fst, Category.comp_id] using hkfst.symm
    · simp only [Category.assoc, s, pullback.lift_snd]
      rw [← Category.assoc, pullback.condition, Category.assoc]
      dsimp [q]
      rw [← Spec.map_comp, hksnd]
      change _ ≫ Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk I).comp σ.toRingHom)) = _
      rw [hσ]
  have : IsFinite W.hom := W.prop.1
  have : Etale W.hom := W.prop.2
  let U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
    MorphismProperty.Over.mk ⊤ (pullback.snd W.hom s) ⟨inferInstance, inferInstance⟩
  refine ⟨U, ⟨?_⟩⟩
  let a := pullbackLeftPullbackSndIso W.hom s (pullback.fst f q)
  let d : pullback W.hom (pullback.fst f q ≫ s) ≅ pullback W.hom k :=
    pullback.congrHom rfl hs
  refine Over.isoMk (a ≪≫ d) ?_ ≪≫ e
  dsimp [a, d]
  simp [U, q]
  rfl

end AlgebraicGeometry.Scheme
