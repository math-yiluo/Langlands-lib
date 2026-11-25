/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.CoherentMapReductionTorsion
import WeilConjectures.AlgebraicGeometry.CoherentMapCompletionTorsionKernelReflection

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in
private theorem product_zero_of_iso {X : Scheme.{u}} (K : X.IdealSheafData)
    (t : ℕ) {F G : X.Modules} (f : F ≅ G)
    (hz : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2 G)) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2 F) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  obtain ⟨k, hk⟩ := formalModuleQuotient_factor K f.hom (Nat.le_refl t)
  have hg : Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι t).2 G = 0 :=
    hz.eq_zero_of_src _
  have hf : Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι t).2 F = 0 := by
    apply (cancel_mono f.hom).mp
    simpa only [hg, comp_zero, zero_comp] using hk
  have : Mono (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι t).2 F) := by
    dsimp [Scheme.idealModuleProductι]
    infer_instance
  exact IsZero.of_mono_eq_zero _ hf

set_option backward.isDefEq.respectTransparency false in
/-- One half of the quantitative torsion reflection for a fixed compatible
algebraization. Source: Stacks Project, Tags 088A and 0888.
Proof: use the scalar reverse maps from Remark 0888 on affine sections,
transport them through the comparison square, and pass to inverse limits;
then use the closed-immersion equivalence and completion reflection.
(blueprint: lem-weil-pbc-devissage-second-adic-system-torsion-kernel) -/
theorem grothendieckDevissage_secondAdicSystem_torsion_kernel
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
    (σ : N.obj ⋙ formalCompletionFunctor I ≅
      (M.obj ⋙ formalCompletionFunctor K).flip)
    (hsquare : ∀ e n : ℕ,
        (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n))
    (t : ℕ) (ht : 1 ≤ t)
    (hα : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))) :
    ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (4 * t)).2
        (kernel (δ.hom.app (op e)))) := by
  intro e
  let F : CoherentModules X := ⟨N.obj.obj (op e), N.property.1 e⟩
  let G : CoherentModules X := ⟨((completion X K).obj H).obj.obj (op e),
    ((completion X K).obj H).property.1 e⟩
  let a : F ⟶ G := ObjectProperty.homMk (δ.hom.app (op e))
  have hred : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (kernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (cokernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))))) := by
    intro n
    let Fn : CoherentModules X := ⟨M.obj.obj (op n), M.property.1 n⟩
    let Gn : CoherentModules X := ⟨((completion X I).obj H).obj.obj (op n),
      ((completion X I).obj H).property.1 n⟩
    let an : Fn ⟶ Gn := ObjectProperty.homMk (α.hom.app (op n))
    have hbound := coherentMap_reduction_torsion K K Fn Gn an t ht
      (hα n).1 (hα n).2 e
    let p : formalModuleQuotient I (n + 1) F.obj ≅
        formalModuleQuotient K (e + 1) Fn.obj := (σ.app (op e)).app (op n)
    let q : formalModuleQuotient I (n + 1) G.obj ≅
        formalModuleQuotient K (e + 1) Gn.obj := (θ.app (op e)).app (op n)
    have hw := (hsquare e n).symm
    let hk := kernel.mapIso (f := formalModuleQuotientMap I a.hom
      (Nat.le_refl (n + 1))) (formalModuleQuotientMap K an.hom (Nat.le_refl (e + 1)))
      p q hw
    let hc := cokernel.mapIso (f := formalModuleQuotientMap I a.hom
      (Nat.le_refl (n + 1))) (formalModuleQuotientMap K an.hom (Nat.le_refl (e + 1)))
      p q hw
    exact ⟨product_zero_of_iso K (2 * t) hk hbound.1,
      product_zero_of_iso K (2 * t) hc hbound.2⟩
  have h := coherentMap_completion_torsion_kernel_reflection I K (e + 1)
    (Nat.succ_le_succ (Nat.zero_le e)) (hthick (e + 1) (by omega)) F G a
    (N.property.2.1 e) (((completion X K).obj H).property.2.1 e)
    (2 * t) (by omega) hred
  rw [show 2 * (2 * t) = 4 * t from (Nat.mul_assoc 2 2 t).symm] at h
  exact h

end AlgebraicGeometry
