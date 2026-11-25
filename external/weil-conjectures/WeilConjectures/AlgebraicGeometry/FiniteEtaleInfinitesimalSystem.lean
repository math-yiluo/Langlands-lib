/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Comma
import WeilConjectures.AlgebraicGeometry.FiniteEtaleThickeningLift
import WeilConjectures.AlgebraicGeometry.InfinitesimalTransitionThickening

/-!
# Compatible finite étale covers of the infinitesimal fibres

Source: Stacks Project, Fundamental Groups, Tag 0GS2, complete Noetherian
essential-surjectivity paragraph, construction before algebraization
(blueprint: lem-weil-pbc-finite-etale-infinitesimal-system).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite étale cover of the closed fibre extends to a compatible system of
finite étale covers of all finite infinitesimal fibres. No completeness,
Noetherianity, or properness is needed for this construction.
Source: Stacks Project, Tag 0GS2, complete Noetherian essential-surjectivity
paragraph, using Tags 039R and 09ZW(8).
(blueprint: lem-weil-pbc-finite-etale-infinitesimal-system).

Proof:
1. Write X_n = X ×_A Spec(A/I^(n+1)). The transition X_n → X_(n+1)
   is a closed immersion defined by a nilpotent ideal. Likewise X_0 → X_n
   is a finite order thickening: the ideal I/I^(n+1) has zero (n+1)st power.
   These facts persist under base change. The transition maps are therefore
   surjective closed immersions and universal homeomorphisms.
2. Set the initial cover to the given V, transporting along I^1 = I.
   Inductively use the essential surjectivity of the étale base-change
   equivalence along X_n → X_(n+1) to choose an étale cover of X_(n+1)
   whose pullback is isomorphic to the previously chosen cover.
3. Compose the inverse of that pullback isomorphism with the projection
   to obtain g_n. The square is cartesian by the pullback isomorphism.
   Iterating these squares identifies every cover's restriction to X_0
   with V. Finiteness follows from isFinite_iff_of_finiteOrderThickening
   applied to X_0 → X_n. Choose the system by recursion on n; retain the
   initial isomorphism over X_0 in the conclusion. -/
theorem exists_finiteEtale_infinitesimal_system
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ (Yn : ℕ → Scheme.{u})
      (fnY : ∀ n, Yn n ⟶ pullback f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
      (gn : ∀ n, Yn n ⟶ Yn (n + 1)),
      (∀ n, IsFinite (fnY n) ∧ Etale (fnY n)) ∧
      (∀ n, IsPullback (fnY n) (gn n)
      (pullback.map f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
        f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) (𝟙 X)
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))))
        (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              Ideal.Quotient.factor_comp_mk]))
      (fnY (n + 1))) ∧
      Nonempty (Over.mk (show Yn 0 ⟶ pullback f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) from
          by rw [← pow_one I]; exact fnY 0) ≅ Over.mk V.hom) := by
  classical
  let B (n : ℕ) := pullback f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  let j (n : ℕ) : B n ⟶ B (n + 1) :=
    pullback.map f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
        f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) (𝟙 X)
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))))
        (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              Ideal.Quotient.factor_comp_mk])
  let C (n : ℕ) := (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ (B n)
  have lift (n : ℕ) (W : C n) :
      ∃ W' : C (n + 1), ∃ g : W.left ⟶ W'.left, IsPullback W.hom g (j n) W'.hom := by
    have hj := infinitesimal_transition_thickening I f n
    have : IsUniversalHomeomorphism (j n) := hj.2
    exact exists_finiteEtale_thickening_lift (j n) hj.1 W
  have hB : B 0 = pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
    dsimp only [B]
    rw [Nat.zero_add, pow_one]
  let W0 : C 0 := MorphismProperty.Over.mk ⊤ (V.hom ≫ eqToHom hB.symm) (by
    have : IsFinite V.hom := V.prop.1
    have : Etale V.hom := V.prop.2
    exact ⟨inferInstance, inferInstance⟩)
  let W : ∀ n, C n := fun n ↦ Nat.rec W0 (fun n Wn ↦ (lift n Wn).choose) n
  have hg (n : ℕ) :
      ∃ g : (W n).left ⟶ (W (n + 1)).left,
        IsPullback (W n).hom g (j n) (W (n + 1)).hom :=
    (lift n (W n)).choose_spec
  refine ⟨fun n ↦ (W n).left, fun n ↦ (W n).hom, fun n ↦ (hg n).choose,
    fun n ↦ (W n).prop, fun n ↦ (hg n).choose_spec, ?_⟩
  dsimp only [W, Nat.rec_zero, W0]
  let Y := V.left
  change Nonempty (Over.mk (show Y ⟶ pullback f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) from
      by rw [← pow_one I]; exact V.hom ≫ eqToHom hB.symm) ≅ Over.mk V.hom)
  refine ⟨Over.isoMk (Iso.refl V.left) ?_⟩
  change (𝟙 V.left) ≫ V.hom =
    (congrArg (fun T : Scheme.{u} ↦ Y ⟶ T) hB.symm).mpr (V.hom ≫ eqToHom hB.symm)
  rw [Category.id_comp, congrArg_mpr_hom_right (V.hom ≫ eqToHom hB.symm) hB.symm]
  simp

end AlgebraicGeometry
