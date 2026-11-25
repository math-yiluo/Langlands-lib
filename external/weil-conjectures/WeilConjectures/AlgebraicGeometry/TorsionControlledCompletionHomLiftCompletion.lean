/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TorsionControlledFiniteGraphEpi
import WeilConjectures.AlgebraicGeometry.FormalMapTorsionFiniteDetection

/-! # A completion lift constructed from the prescribed formal map

Source: Stacks Project, Tag 0889(1), comparison morphisms.
The finite graph retains a component of θ, and a separating quotient makes its
first projection invertible. Both compatibility equations belong to this construction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- At a separating depth the finite graph has monomorphic first projection.
Proof: a map with zero first projection has second projection in ker(a'). The
kernel equation for the graph kills its image in the separating quotient, so
this second projection is zero as well. Pullback extensionality finishes.
Source: Stacks Project, Tag 0889(1), comparison argument.
(blueprint: lem-weil-pbc-torsion-controlled-completion-hom-lift-completion). -/
theorem torsionControlledGraphFst_mono
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (θ : (completion X J).obj F ⟶ (completion X J).obj F') (n : ℕ)
    (hsep : Mono (kernel.ι a'.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj)) :
    Mono (torsionControlledGraphFst J a a' θ n) := by
  let := hsep
  apply Preadditive.mono_of_cancel_zero
  intro T z hz
  have hs : z ≫ torsionControlledGraphSnd J a a' θ n ≫ a'.hom = 0 := by
    dsimp [torsionControlledGraphSnd]
    simp only [Category.assoc, ← pullback.condition]
    change (z ≫ torsionControlledGraphFst J a a' θ n) ≫ a.hom = 0
    rw [hz, zero_comp]
  let k := kernel.lift a'.hom (z ≫ torsionControlledGraphSnd J a a' θ n) hs
  have hk : k ≫ kernel.ι a'.hom = z ≫ torsionControlledGraphSnd J a a' θ n := by
    simp [k]
  have hq : torsionControlledGraphSnd J a a' θ n ≫
      formalModuleQuotientπ J (n + 1) F'.obj =
      torsionControlledGraphFst J a a' θ n ≫
        formalModuleQuotientπ J (n + 1) F.obj ≫ θ.hom.app (op n) := by
    have he := kernel.condition (torsionControlledGraphError J a a' θ n)
    simpa only [torsionControlledGraphError, Preadditive.comp_sub, sub_eq_zero,
      torsionControlledGraphSnd, torsionControlledGraphFst, Category.assoc] using he
  have hkzero : k = 0 := by
    apply (cancel_mono (kernel.ι a'.hom ≫
      formalModuleQuotientπ J (n + 1) F'.obj)).mp
    rw [← Category.assoc, hk, Category.assoc, hq, ← Category.assoc, hz]
    simp
  have hzsecond : z ≫ torsionControlledGraphSnd J a a' θ n = 0 := by
    rw [← hk, hkzero, zero_comp]
  apply (cancel_mono (kernel.ι (torsionControlledGraphError J a a' θ n))).mp
  apply pullback.hom_ext
  · simpa only [torsionControlledGraphFst, Category.assoc, zero_comp] using hz
  · simpa only [torsionControlledGraphSnd, Category.assoc, zero_comp] using hzsecond

/-- The first projection is invertible: surjectivity is the affine finite-graph
lemma, and injectivity is the separating-quotient argument above.
Source: Stacks Project, Tag 0889(1).
(blueprint: lem-weil-pbc-torsion-controlled-completion-hom-lift-completion). -/
theorem torsionControlledGraphFst_isIso
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (ha' : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom)))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a)
    (n : ℕ) (hsep : Mono (kernel.ι a'.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj)) :
    IsIso (torsionControlledGraphFst J a a' θ n) := by
  let := torsionControlledGraphFst_epi J a a' ha' θ hθ n
  let := torsionControlledGraphFst_mono J a a' θ n hsep
  exact isIso_of_mono_of_epi _

/-- The lift is inverse(first graph projection) followed by second projection.
The only choice is the unique inverse of the stated isomorphism; the graph itself
is an actual kernel of an actual pullback discrepancy containing θ.
Source: Stacks Project, Tag 0889(1).
(blueprint: lem-weil-pbc-torsion-controlled-completion-hom-lift-completion). -/
noncomputable def torsionControlledCompletionHomLift
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (ha' : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom)))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a)
    (n : ℕ) (hsep : Mono (kernel.ι a'.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj)) :
    F ⟶ F' :=
  let := torsionControlledGraphFst_isIso J a a' ha' θ hθ n hsep
  ObjectProperty.homMk
    (inv (torsionControlledGraphFst J a a' θ n) ≫ torsionControlledGraphSnd J a a' θ n)

set_option backward.isDefEq.respectTransparency false in
/-- Both equations hold for the lift constructed with the prescribed θ.
Source: Stacks Project, Tag 0889(1), comparison morphisms.
Proof: the pullback condition gives the equation with a'. The graph kernel
condition gives the prescribed component of θ after cancelling the quotient
projection. Functoriality gives the completed equation with a'; finite torsion
detection then identifies all components with θ.
(blueprint: lem-weil-pbc-torsion-controlled-completion-hom-lift-completion). -/
theorem torsionControlled_completion_hom_lift_constructed
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    {H F F' : CoherentModules X} (a : F ⟶ H) (a' : F' ⟶ H)
    (ha' : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom)))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a)
    (n : ℕ) (hsep : Mono (kernel.ι a'.hom ≫ formalModuleQuotientπ J (n + 1) F'.obj)) :
    torsionControlledCompletionHomLift J a a' ha' θ hθ n hsep ≫ a' = a ∧
      (completion X J).map
        (torsionControlledCompletionHomLift J a a' ha' θ hθ n hsep) = θ := by
  let := torsionControlledGraphFst_isIso J a a' ha' θ hθ n hsep
  let g := torsionControlledCompletionHomLift J a a' ha' θ hθ n hsep
  have hg : g ≫ a' = a := by
    apply ObjectProperty.hom_ext
    change (inv (torsionControlledGraphFst J a a' θ n) ≫
      torsionControlledGraphSnd J a a' θ n) ≫ a'.hom = a.hom
    have hp : torsionControlledGraphSnd J a a' θ n ≫ a'.hom =
        torsionControlledGraphFst J a a' θ n ≫ a.hom := by
      dsimp [torsionControlledGraphSnd, torsionControlledGraphFst]
      simp only [Category.assoc, pullback.condition]
    rw [Category.assoc, hp, IsIso.inv_hom_id_assoc]
  refine ⟨hg, ?_⟩
  apply formalMap_torsion_finite_detection J F' H a'
    (by obtain ⟨s, hs, hk, hc⟩ := ha'; exact ⟨s, hs, hk⟩) n hsep
    ((completion X J).obj F)
  · rw [← Functor.map_comp, hg, hθ]
  · change formalModuleQuotientMap J g.hom (Nat.le_refl (n + 1)) = θ.hom.app (op n)
    apply (cancel_epi (cokernel.π
      (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (n + 1)).2
        F.obj))).mp
    change formalModuleQuotientπ J (n + 1) F.obj ≫
      formalModuleQuotientMap J g.hom (Nat.le_refl (n + 1)) = _
    simp only [formalModuleQuotientMap, formalModuleQuotientπ, cokernel.π_desc]
    have he := kernel.condition (torsionControlledGraphError J a a' θ n)
    have hq : torsionControlledGraphSnd J a a' θ n ≫
        formalModuleQuotientπ J (n + 1) F'.obj =
        torsionControlledGraphFst J a a' θ n ≫
          formalModuleQuotientπ J (n + 1) F.obj ≫ θ.hom.app (op n) := by
      simpa only [torsionControlledGraphError, Preadditive.comp_sub, sub_eq_zero,
        torsionControlledGraphSnd, torsionControlledGraphFst, Category.assoc] using he
    change (inv (torsionControlledGraphFst J a a' θ n) ≫
      torsionControlledGraphSnd J a a' θ n) ≫
        formalModuleQuotientπ J (n + 1) F'.obj =
      formalModuleQuotientπ J (n + 1) F.obj ≫ θ.hom.app (op n)
    rw [Category.assoc, hq, IsIso.inv_hom_id_assoc]

end AlgebraicGeometry
