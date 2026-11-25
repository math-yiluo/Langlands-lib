/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying

import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemComparison

/-! # Quotients of formal systems remain adic

Source: Stacks Project, Tag 088A, the systems F_n/K^e F_n.
(blueprint: lem-weil-pbc-formal-second-ideal-quotient-adic).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem quotientProjection_map {X : Scheme.{u}} (J : X.IdealSheafData)
    {F G : X.Modules} (f : F ⟶ G) (n : ℕ) :
    formalModuleQuotientπ J n F ≫ formalModuleQuotientMap J f (Nat.le_refl n) =
      f ≫ formalModuleQuotientπ J n G := by
  simp only [formalModuleQuotientπ, formalModuleQuotientMap, cokernel.π_desc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Termwise K-quotients of an I-adic coherent system are I-adic.
Source: Stacks Project, Tag 088A, construction of G_e.
(blueprint: lem-weil-pbc-formal-second-ideal-quotient-adic).

Proof: Each term is a coherent quotient by the coherent completion construction.
The I-power product of the quotient is zero: precomposing its multiplication with
the epimorphic K-quotient projection reduces this to the original I-annihilation.
Interchange the I and K quotients using the canonical double-quotient comparison,
then apply the K-quotient functor to the original I-adic transition isomorphism.
The projection identity of the comparison and the original transition identity,
after cancellation of the K-quotient projection, identify the resulting map with
the actual transition. -/
theorem formalSecondIdealQuotient_coherent
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I) (e : ℕ) :
    IsCoherentFormalModule I ((M.obj ⋙ formalCompletionFunctor K).flip.obj (op e)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact (formalCompletionSystem_coherent K ⟨_, M.property.1 n⟩).1 e
  · intro n
    let F := M.obj.obj (op n)
    let Q := formalModuleQuotient K (e + 1) F
    let q := formalModuleQuotientπ K (e + 1) F
    have : Epi q := inferInstanceAs (Epi (cokernel.π _))
    let j := (Scheme.idealSheafPower I.toModulesι (n + 1)).2
    have hi : Scheme.idealModuleProductι j F = 0 :=
      (M.property.2.1 n).eq_zero_of_src _
    have hz : Scheme.idealModuleProductι j Q = 0 := by
      have h := (idealModuleProduct_quotient_comp_zero_iff j q (𝟙 Q)).mpr
        (by simp only [hi, zero_comp])
      change Scheme.idealModuleProductι j Q ≫ 𝟙 Q = 0 at h
      rwa [Category.comp_id] at h
    have := idealModuleProduct_mono j Q
    exact IsZero.of_mono_eq_zero (Scheme.idealModuleProductι j Q) hz
  · intro n
    obtain ⟨a, ha⟩ := M.property.2.2 n
    let F := M.obj.obj (op (n + 1))
    obtain ⟨θ, hθ⟩ := grothendieckDevissage_secondAdicSystem_comparison I K F
    let s : formalModuleQuotient I (n + 1) (formalModuleQuotient K (e + 1) F) ≅
        formalModuleQuotient K (e + 1) (formalModuleQuotient I (n + 1) F) :=
      (θ.app (op e)).app (op n)
    let b : formalModuleQuotient K (e + 1) (formalModuleQuotient I (n + 1) F) ≅
        formalModuleQuotient K (e + 1) (M.obj.obj (op n)) :=
      ((formalCompletionFunctor K).mapIso a).app (op e)
    refine ⟨s ≪≫ b, ?_⟩
    have : Epi (formalModuleQuotientπ K (e + 1) F) := by
      dsimp only [formalModuleQuotientπ]
      infer_instance
    apply (cancel_epi (formalModuleQuotientπ K (e + 1) F)).mp
    change formalModuleQuotientπ K (e + 1) F ≫
        formalModuleQuotientπ I (n + 1) (formalModuleQuotient K (e + 1) F) ≫
        s.hom ≫ b.hom =
      formalModuleQuotientπ K (e + 1) F ≫
        formalModuleQuotientMap K (M.obj.map (homOfLE (Nat.le_succ n)).op)
          (Nat.le_refl (e + 1))
    rw [← Category.assoc _ _ b.hom]
    change (formalModuleQuotientπ K (e + 1) F ≫
      formalModuleQuotientπ I (n + 1) (formalModuleQuotient K (e + 1) F) ≫
      (θ.hom.app (op e)).app (op n)) ≫ b.hom = _
    rw [hθ e n]
    change (formalModuleQuotientπ I (n + 1) F ≫
        formalModuleQuotientπ K (e + 1) (formalModuleQuotient I (n + 1) F)) ≫
        formalModuleQuotientMap K a.hom (Nat.le_refl (e + 1)) =
      formalModuleQuotientπ K (e + 1) F ≫
        formalModuleQuotientMap K (M.obj.map (homOfLE (Nat.le_succ n)).op)
          (Nat.le_refl (e + 1))
    rw [Category.assoc, quotientProjection_map, quotientProjection_map,
      ← Category.assoc, ha]

end AlgebraicGeometry
