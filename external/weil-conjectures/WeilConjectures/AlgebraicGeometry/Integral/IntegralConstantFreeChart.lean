/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.CategoryTheory.Sites.DisjointGluing
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.ExtensionZeroPerfectModelTransport

/-!
# Inverse images of completed realizations of finite free modules

The inverse image along a morphism of schemes of the completed realization of a finite
free module is the free module sheaf of the same rank. Both corepresent the finite
families of global sections.

## References

* Bhatt--Scholze, Proposition 6.6.11
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

/-- Sections of a presheaf of types over a category with a terminal object are its values
at the terminal object. -/
def _root_.CategoryTheory.Functor.sectionsEquivOfIsTerminal {C : Type*} [Category C]
    {P : Cᵒᵖ ⥤ Type*} {T : C} (hT : IsTerminal T) : P.sections ≃ P.obj (op T) where
  toFun s := s.1 (op T)
  invFun x := Functor.sectionOfIsTerminal hT x
  left_inv s := Functor.sections_ext_of_isTerminal hT (by
    change P.map (hT.from T).op (s.1 (op T)) = s.1 (op T)
    rw [hT.hom_ext (hT.from T) (𝟙 T)]
    rw [op_id, P.map_id]; rfl)
  right_inv x := by
    change P.map (hT.from T).op x = x
    rw [hT.hom_ext (hT.from T) (𝟙 T)]
    rw [op_id, P.map_id]; rfl

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {T S : Scheme.{u}} (g : S ⟶ T)

/-- Morphisms out of the inverse image of the completed realization of `A^r` are `r`-tuples
of global sections. -/
private def integralConstantFreeHomEquiv (r : ℕ)
    (M : pbcModules S ((adicTowerInverseImage g).obj (pbcAdicCompletion T d))) :
    ((proEtaleRingModulePullback g (pbcAdicCompletion T d) _ (Iso.refl _)).obj
        ((integralConstantModule T d).obj (ModuleCat.of A (Fin r →₀ A))) ⟶ M) ≃
      (ULift.{u + 1} (Fin r) → M.sections) :=
  let W := (proEtaleBaseChange g).obj (⊤_ T.ProEt)
  let hW : IsTerminal W := terminalIsTerminal.isTerminalObj (proEtaleBaseChange g)
  ((proEtaleRingModuleAdjunction g (pbcAdicCompletion T d) _ (Iso.refl _)).homEquiv _ _).trans
    (((integralAdj T d (⊤_ T.ProEt) terminalIsTerminal).homEquiv _ _).trans
      ((ModuleCat.homEquiv.trans (Finsupp.lift _ A (Fin r)).toEquiv.symm).trans
        ((Equiv.arrowCongr Equiv.ulift.symm
          (Functor.sectionsEquivOfIsTerminal
            (P := M.val.presheaf ⋙ CategoryTheory.forget _) hW).symm))))


private theorem sectionsMap_sectionsEquivOfIsTerminal_symm
    {M M' : pbcModules S ((adicTowerInverseImage g).obj (pbcAdicCompletion T d))} (h : M ⟶ M')
    {W : S.ProEt} (hW : IsTerminal W) (x : M.val.obj (op W)) :
    SheafOfModules.sectionsMap h
        ((Functor.sectionsEquivOfIsTerminal (P := M.val.presheaf ⋙ CategoryTheory.forget _)
          hW).symm x) =
      (Functor.sectionsEquivOfIsTerminal (P := M'.val.presheaf ⋙ CategoryTheory.forget _)
          hW).symm (h.val.app (op W) x) := by
  apply (Functor.sectionsEquivOfIsTerminal
    (P := M'.val.presheaf ⋙ CategoryTheory.forget _) hW).injective
  rw [Equiv.apply_symm_apply]
  change h.val.app (op W) (((Functor.sectionsEquivOfIsTerminal
    (P := M.val.presheaf ⋙ CategoryTheory.forget _) hW).symm x).1 (op W)) = _
  congr 1
  exact (Functor.sectionsEquivOfIsTerminal
    (P := M.val.presheaf ⋙ CategoryTheory.forget _) hW).apply_symm_apply x

private theorem integralConstantFreeHomEquiv_comp (r : ℕ)
    {M M' : pbcModules S ((adicTowerInverseImage g).obj (pbcAdicCompletion T d))}
    (k : (proEtaleRingModulePullback g (pbcAdicCompletion T d) _ (Iso.refl _)).obj
        ((integralConstantModule T d).obj (ModuleCat.of A (Fin r →₀ A))) ⟶ M) (h : M ⟶ M') :
    integralConstantFreeHomEquiv d g r M' (k ≫ h) =
      fun i ↦ SheafOfModules.sectionsMap h (integralConstantFreeHomEquiv d g r M k i) := by
  funext i
  simp only [integralConstantFreeHomEquiv, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_right, Equiv.arrowCongr_apply, Function.comp_apply]
  erw [sectionsMap_sectionsEquivOfIsTerminal_symm]
  rfl
/-- The inverse image of the completed realization of `A^r` is the free module sheaf of
rank `r`. -/
private def integralConstantFreePullbackIso (r : ℕ) :
    (proEtaleRingModulePullback g (pbcAdicCompletion T d) _ (Iso.refl _)).obj
        ((integralConstantModule T d).obj (ModuleCat.of A (Fin r →₀ A))) ≅
      SheafOfModules.free (R := (adicLisseForget S).obj
        ((adicTowerInverseImage g).obj (pbcAdicCompletion T d))) (ULift.{u + 1} (Fin r)) :=
  Coyoneda.ext _ _
    (fun f ↦ (SheafOfModules.freeHomEquiv _).symm (integralConstantFreeHomEquiv d g r _ f))
    (fun f ↦ (integralConstantFreeHomEquiv d g r _).symm (SheafOfModules.freeHomEquiv _ f))
    (fun f ↦ by simp) (fun f ↦ by simp) (fun f h ↦ by
      apply (integralConstantFreeHomEquiv d g r _).injective
      rw [Equiv.apply_symm_apply, integralConstantFreeHomEquiv_comp, Equiv.apply_symm_apply]
      rfl)

/-- The inverse image of the completed realization of `A^r` is a module sheaf with a basis
of `r` sections on every object. -/
theorem exists_basis_pullback_integralConstantModule_free (r : ℕ) :
    ∃ F : pbcModules S ((adicTowerInverseImage g).obj (pbcAdicCompletion T d)),
      (∀ U : S.ProEtᵒᵖ, Nonempty (Module.Basis (Fin r)
        (((adicTowerInverseImage g).obj (pbcAdicCompletion T d)).obj.obj U) (F.val.obj U))) ∧
      Nonempty ((proEtaleRingModulePullback g (pbcAdicCompletion T d) _ (Iso.refl _)).obj
        ((integralConstantModule T d).obj (ModuleCat.of A (Fin r →₀ A))) ≅ F) :=
  ⟨_, fun U ↦ ⟨(Module.Basis.ofEquivFun
      (SheafOfModules.freeSectionsLinearEquiv (R := (adicLisseForget S).obj
        ((adicTowerInverseImage g).obj (pbcAdicCompletion T d))) (ULift.{u + 1} (Fin r))
          U)).reindex Equiv.ulift⟩,
    ⟨integralConstantFreePullbackIso d g r⟩⟩

end AlgebraicGeometry.Scheme
