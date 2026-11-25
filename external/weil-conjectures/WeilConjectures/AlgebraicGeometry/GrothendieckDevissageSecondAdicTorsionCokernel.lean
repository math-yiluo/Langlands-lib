/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.CoherentMapReductionTorsionCoker
import WeilConjectures.AlgebraicGeometry.CompletionThickeningCokernelReflection

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in
/-- One half of the quantitative torsion reflection for a fixed compatible
algebraization. Source: Stacks Project, Tags 088A and 0888.
Proof: use the scalar reverse maps from Remark 0888 on affine sections,
transport them through the comparison square, and pass to inverse limits;
then use the closed-immersion equivalence and completion reflection.
(blueprint: lem-weil-pbc-devissage-second-adic-system-torsion-cokernel) -/
theorem grothendieckDevissage_secondAdicSystem_torsion_cokernel
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
        (cokernel (δ.hom.app (op e)))) := by
  intro e
  let F : CoherentModules X := ⟨N.obj.obj (op e), N.property.1 e⟩
  let G : CoherentModules X :=
    ⟨((completion X K).obj H).obj.obj (op e), ((completion X K).obj H).property.1 e⟩
  let a : F ⟶ G := ⟨δ.hom.app (op e)⟩
  have hred : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (cokernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))))) := by
    intro n
    let Fn : CoherentModules X := ⟨M.obj.obj (op n), M.property.1 n⟩
    let Gn : CoherentModules X :=
      ⟨((completion X I).obj H).obj.obj (op n), ((completion X I).obj H).property.1 n⟩
    let an : Fn ⟶ Gn := ⟨α.hom.app (op n)⟩
    have hz := coherentMap_reduction_torsion_coker K K Fn Gn an t ht
      (hα n).1 (hα n).2 e
    let p := (σ.app (op e)).app (op n)
    let q := (θ.app (op e)).app (op n)
    let c := cokernel.mapIso
      (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1)))
      (formalModuleQuotientMap K an.hom (Nat.le_refl (e + 1))) p q
      (hsquare e n).symm
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let ι := (Scheme.idealSheafPower K.toModulesι (2 * t)).2
    let l := (MonoidalCategory.tensorLeft (Scheme.idealSheafPower K.toModulesι (2 * t)).1).mapIso c
    let C₁ := cokernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1)))
    let C₂ := cokernel (formalModuleQuotientMap K an.hom (Nat.le_refl (e + 1)))
    let a₁ := MonoidalCategoryStruct.whiskerRight ι C₁ ≫
      (MonoidalCategoryStruct.leftUnitor C₁).hom
    let a₂ := MonoidalCategoryStruct.whiskerRight ι C₂ ≫
      (MonoidalCategoryStruct.leftUnitor C₂).hom
    have w : l.hom ≫ a₂ = a₁ ≫ c.hom := by
      dsimp [l, a₁, a₂]
      rw [← Category.assoc, MonoidalCategory.whisker_exchange, Category.assoc]
      exact (congrArg (MonoidalCategoryStruct.whiskerRight ι _ ≫ ·)
        (MonoidalCategory.leftUnitor_naturality c.hom)).trans
          (Category.assoc _ _ _).symm
    let d := Arrow.isoMk (f := Arrow.mk a₁) (g := Arrow.mk a₂) l c w
    exact hz.of_iso ((im (C := X.Modules)).mapIso d)
  have h := completion_thickening_cokernel_reflection I K (e + 1) (by omega)
    (hthick (e + 1) (by omega)) F G a (N.property.2.1 e)
    (((completion X K).obj H).property.2.1 e) (2 * t) (by omega) hred
  have heq : 2 * (2 * t) = 4 * t := by omega
  rw [heq] at h
  exact h

end AlgebraicGeometry
