/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass

/-!
# Kummer classes with coefficients

The Kummer boundary `δ(u) ∈ H¹(X, μₙ)` of a unit `u`, defined through the long exact sequence of
`CategoryTheory.Sheaf.H` (`AlgebraicGeometry.Scheme.kummerδ₀`), is the composition of the
morphism `ℤ ⟶ 𝔾ₘ` of `u` (`AlgebraicGeometry.Scheme.unitToGmSheaf`) with the extension class of
the Kummer sequence (`AlgebraicGeometry.Scheme.kummerδ₀_eq_comp_extClass`). This is the
bridge between the Kummer classes with `Λ`-coefficients `AlgebraicGeometry.Etale.kummerClassOf`
and the classical Kummer theory of `WeilConjectures.AlgebraicGeometry.Sites.Kummer`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

/-- The value of the adjunction `constantSheaf ⊣ Γ(T, -)` on a morphism `f`, for any terminal
object `T`: the unit of sheafification at `T` followed by `f`. -/
lemma constantSheafAdj_homEquiv_eq {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {D : Type*} [Category* D] [HasWeakSheafify J D] {T : C} (hT : IsTerminal T) {M : D}
    {F : Sheaf J D} (f : (constantSheaf J D).obj M ⟶ F) :
    (constantSheafAdj J D hT).homEquiv M F f =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) ≫ f.hom.app (op T) := by
  rw [Adjunction.homEquiv_unit]
  simp [constantSheafAdj, constantPresheafAdj]

/-- The adjunction `constantSheaf ⊣ Γ(T, -)` for two terminal objects `T`, `T'` differ by the
restriction along `T' ⟶ T`. -/
lemma constantSheafAdj_homEquiv_eq_comp {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {D : Type*} [Category* D] [HasWeakSheafify J D] {T T' : C} (hT : IsTerminal T)
    (hT' : IsTerminal T') {M : D} {F : Sheaf J D} (f : (constantSheaf J D).obj M ⟶ F) :
    (constantSheafAdj J D hT').homEquiv M F f =
      (constantSheafAdj J D hT).homEquiv M F f ≫ F.obj.map (hT.from T').op := by
  rw [constantSheafAdj_homEquiv_eq, constantSheafAdj_homEquiv_eq, Category.assoc,
    ← f.hom.naturality, ← Category.assoc]
  change _ = ((toSheafify J _).app (op T) ≫
    (sheafify J ((Functor.const Cᵒᵖ).obj M)).map (hT.from T').op) ≫ f.hom.app (op T')
  rw [← (toSheafify J _).naturality]
  simp

lemma _root_.AddCommGrpCat.uliftZMultiplesAddEquiv_eq (G : AddCommGrpCat.{u})
    (f : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ G) :
    G.uliftZMultiplesAddEquiv f = f.hom (ULift.up 1) := by
  have h := (AddEquiv.mk' (uliftZMultiplesHom G) (uliftZMultiplesHom_apply_add G)).apply_symm_apply
    (AddCommGrpCat.homAddEquiv f)
  have h2 := congrArg (fun φ : ULift.{u} ℤ →+ G ↦ φ (ULift.up 1)) h
  change uliftZMultiplesHom G (G.uliftZMultiplesAddEquiv f) (ULift.up 1) = f.hom (ULift.up 1)
    at h2
  rw [← h2]
  simp only [uliftZMultiplesHom]
  exact (one_smul ℤ _).symm

variable (X : Scheme.{u})

/-- The constant sheaf `ℤ` (on `ULift ℤ`, as in `CategoryTheory.Sheaf.H`) is the constant sheaf
`ℤ/0` of `AlgebraicGeometry.Scheme.constantSheafInt`. -/
noncomputable def Scheme.constantSheafULiftIntIso :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≅ X.constantSheafInt :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
    (AddEquiv.ulift.trans (AddEquiv.ulift (α := ZMod 0)).symm).toAddCommGrpIso

/-- Under `H⁰(X, 𝔾ₘ) = 𝔾ₘ(T)`, the morphism `ℤ ⟶ 𝔾ₘ` of a unit `u` is the section `u`. -/
lemma Scheme.equiv₀_mk₀_unitToGmSheaf {T : X.Etale} (hT : IsTerminal T) (u : Γ(X, ⊤)ˣ) :
    Sheaf.H.equiv₀ X.gmSheaf hT
      (Abelian.Ext.mk₀ ((X.constantSheafULiftIntIso).hom ≫ unitToGmSheaf u)) =
        X.gmSheaf.obj.map (terminalIsTerminal.from T).op (gmSection u) := by
  change AddCommGrpCat.uliftZMultiplesAddEquiv _ ((constantSheafAdj _ _ hT).homAddEquiv _ _
    (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ _))) = _
  rw [← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply,
    Adjunction.homAddEquiv_apply, constantSheafAdj_homEquiv_eq_comp terminalIsTerminal,
    AddCommGrpCat.uliftZMultiplesAddEquiv_eq, Scheme.constantSheafULiftIntIso, Functor.mapIso_hom,
    Adjunction.homEquiv_naturality_left, unitToGmSheaf, Equiv.apply_symm_apply]
  change (X.gmSheaf.obj.map _).hom ((zmodToGmSections 0 u (pow_zero u)).hom
    (ULift.up ((1 : ℕ) : ZMod 0))) = _
  rw [zmodToGmSections_natCast, pow_one]

lemma Scheme.gmSheaf_map_gmSection (u : Γ(X, ⊤)ˣ) :
    X.gmSheaf.obj.map (terminalIsTerminal.from
        (MorphismProperty.Over.mk ⊤ (𝟙 X) (inferInstance : Etale (𝟙 X)))).op (gmSection u) =
      AddEquiv.ulift.symm (Additive.ofMul u) := by
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  let g : (MorphismProperty.Over.mk ⊤ (𝟙 X) (inferInstance : Etale (𝟙 X)) : X.Etale) ⟶
    ⊤_ X.Etale := terminalIsTerminal.from _
  have hw : g.left ≫ (⊤_ X.Etale).hom = 𝟙 X := by simp
  refine (X.gmPresheaf_map_apply g _).trans ?_
  change g.left.appTop ((⊤_ X.Etale).hom.appTop (u : Γ(X, ⊤))) = (u : Γ(X, ⊤))
  erw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hw]
  rfl

/-- The Kummer boundary `δ(u) ∈ H¹(X, μₙ)` of a unit `u` is the composition of the morphism
`ℤ ⟶ 𝔾ₘ` of `u` with the extension class of the Kummer sequence. -/
lemma Scheme.kummerδ₀_eq_comp_extClass (n : ℕ) (hn : IsUnit (n : Γ(X, ⊤))) (u : Γ(X, ⊤)ˣ) :
    X.kummerδ₀ n hn (Additive.ofMul u) =
      (Abelian.Ext.mk₀ ((X.constantSheafULiftIntIso).hom ≫ unitToGmSheaf u)).comp
        (X.kummerSequence_shortExact n hn).extClass (zero_add 1) := by
  change Sheaf.H.δSections _ _ _ = _
  rw [Sheaf.H.δ_apply]
  congr 1
  rw [AddEquiv.symm_apply_eq]
  exact ((equiv₀_mk₀_unitToGmSheaf X _ u).trans (gmSheaf_map_gmSection X u)).symm

end AlgebraicGeometry
