/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Kummer
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison

/-!
# The normalized class map for ordinary finite coefficients

Source: the constants adjunction and the universal Ext/cohomology comparison in
WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian Opposite

namespace AlgebraicGeometry.Etale

/-- Constants adjunction followed by evaluation of an A-linear map at one. -/
private noncomputable def constantModuleHomEquiv (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ordinaryFiniteConstant A T ⟶ F) ≃
      F.obj.obj (op (Scheme.Etale.mk (𝟙 T))) := by
  let adj := constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
  refine (adj.homEquiv _ _).trans {
    toFun := fun f ↦ f.hom 1
    invFun := fun x ↦ ModuleCat.ofHom ((LinearMap.id : A →ₗ[A] A).smulRight x)
    left_inv := ?_
    right_inv := ?_
  }
  · intro f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change a • f.hom 1 = f.hom a
    simpa using (f.hom.map_smul a (1 : A)).symm
  · intro x
    simp

/-- Integral constant maps identify with sections by evaluation at one. -/
private noncomputable def constantAbelianHomEquiv (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F) ≃
        F.obj.obj (op (Scheme.Etale.mk (𝟙 T))) :=
  ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).homEquiv _ _).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv
      (F.obj.obj (op (Scheme.Etale.mk (𝟙 T))))).toEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The specified integral generator corepresents global sections of module sheaves. -/
private theorem integralGenerator_bijective (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Function.Bijective (fun f : ordinaryFiniteConstant A T ⟶ F ↦
      ordinaryFiniteIntegralGenerator A T ≫ (moduleAbelianForget A T).map f) := by
  let e := constantAbelianHomEquiv T ((moduleAbelianForget A T).obj F)
  have h : e ∘ (fun f : ordinaryFiniteConstant A T ⟶ F ↦
      ordinaryFiniteIntegralGenerator A T ≫ (moduleAbelianForget A T).map f) =
      constantModuleHomEquiv A T F := by
    funext f
    dsimp only [Function.comp_apply, e, constantAbelianHomEquiv, Equiv.trans_apply,
      AddEquiv.toEquiv_eq_coe]
    rw [Adjunction.homEquiv_naturality_right]
    simp only [ordinaryFiniteIntegralGenerator, Equiv.apply_symm_apply]
    simp only [AddEquiv.coe_toEquiv]
    erw [AddCommGrpCat.uliftZMultiplesAddEquiv_eq]
    change _ = ((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).homEquiv _ _ f).hom 1
    erw [AlgebraicGeometry.constantSheafAdj_homEquiv_eq]
    simp [AddEquiv.ulift]
    rfl
  have hcomp : Function.Bijective (e ∘ (fun f : ordinaryFiniteConstant A T ⟶ F ↦
      ordinaryFiniteIntegralGenerator A T ≫ (moduleAbelianForget A T).map f)) :=
    h ▸ (constantModuleHomEquiv A T F).bijective
  exact Function.Bijective.of_comp_left hcomp e.injective

/-- The actual class map identifies derived module morphisms with sheaf cohomology.
Source: KummerBoundaryComparison.bijective_extToSheafHOf and the constants adjunction.
(auxiliary; not a blueprint node).
Proof: A map from the constant A-module sheaf is uniquely determined by its global value
at one, by the constants/global-sections adjunction. The specified integral generator
sends the integer one to this element, so precomposition with it corepresents those
sections. On a quasi-compact quasi-separated scheme the universal delta-functor
comparison bijective_extToSheafHOf therefore applies in every degree. Its formula is
the specified forgetful Ext comparison. Finally compose with Ext.homEquiv.symm to
identify Ext classes with the displayed derived-category morphisms. -/
theorem ordinaryFiniteClass_bijective (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℕ) :
    Function.Bijective (ordinaryFiniteClass A T F n) := by
  have h := bijective_extToSheafHOf A (ordinaryFiniteIntegralGenerator A T)
    (integralGenerator_bijective A T) n F
  unfold ordinaryFiniteClass
  exact h.comp Ext.homEquiv.symm.bijective

/-- The actual Kummer boundary has a unique derived module representative.
Source: the preceding normalized class comparison and the specified Chern predicate.
(auxiliary; not a blueprint node).
Proof: surjectivity produces a representative of the fixed Kummer class. If a second
arrow satisfies the same specification, their classes agree, so injectivity equates
the arrows. Thus the construction chooses no unconstrained cohomology witness. -/
theorem existsUnique_ordinaryFiniteP1Chern (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u})
    [CompactSpace (ProjectiveLine S)] [QuasiSeparatedSpace (ProjectiveLine S)]
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤))) :
    ∃! c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
        (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧,
      ordinaryFiniteP1ChernSpec A N hA S hP c := by
  have h := ordinaryFiniteClass_bijective A (ProjectiveLine S)
    (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA) 2
  obtain ⟨c, hc⟩ := h.2 (ordinaryFiniteP1KummerClass A N hA S hP)
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  exact h.1 (hc'.trans hc.symm)

end AlgebraicGeometry.Etale
