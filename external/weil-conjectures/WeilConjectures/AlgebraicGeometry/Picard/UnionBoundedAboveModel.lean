/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitPresentation
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleUnionSESPresentation
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Bounded-above models for direct images from a union of two opens

## References

* Stacks Project, Tags 08BV and 0DJ9 (relative Mayer–Vietoris)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unionBounded_flatOver_of_iso
    {X S : Scheme.{u}} (f : X ⟶ S) {G H : X.Modules} (eGH : G ≅ H)
    (hflat : H.IsFlatOver f) : G.IsFlatOver f := by
  intro V U e
  let φ := (f.appLE V.1 U.1 e).hom
  let : Module Γ(S, V.1) Γ(G, U.1) := Module.compHom _ φ
  let : Module Γ(S, V.1) Γ(H, U.1) := Module.compHom _ φ
  let E := (ModuleCat.restrictScalars φ).mapIso
    ((SheafOfModules.evaluation (R := X.ringCatSheaf) (Opposite.op U.1)).mapIso eGH)
  exact (Module.Flat.equiv_iff E.toLinearEquiv).mpr (hflat V U e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unionBounded_flatOver_restrict
    {X Y S : Scheme.{u}} (a : X ⟶ Y) [IsOpenImmersion a] (f : Y ⟶ S)
    (F : Y.Modules) (hflat : F.IsFlatOver f) : (F.restrict a).IsFlatOver (a ≫ f) := by
  intro V U e
  let U' : Y.affineOpens := ⟨a ''ᵁ U.1, U.2.image_of_isOpenImmersion a⟩
  have e' : U'.1 ≤ f ⁻¹ᵁ V.1 := by
    apply (a.image_mono e).trans
    exact (a.image_preimage_le (f ⁻¹ᵁ V.1))
  have hh := hflat V U' e'
  have heq : (a ≫ f).appLE V.1 U.1 e ≫ (a.appIso U.1).inv =
      f.appLE V.1 U'.1 e' := by
    rw [Scheme.Hom.comp_appLE, Category.assoc, Scheme.Hom.appLE_appIso_inv]
    rfl
  convert hh using 1 <;> try rfl
  ext r m
  change (F.smul (((a.appIso U.1).inv.hom)
    (((a ≫ f).appLE V.1 U.1 e).hom r))).asHom.hom m =
      (F.smul ((f.appLE V.1 U'.1 e').hom r)).asHom.hom m
  exact congrArg (fun t ↦ (F.smul t).asHom.hom m) (congrArg (fun t ↦ t.hom r) heq)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unionBounded_presentation_on_subopen
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (g : A ⟶ B) (W T : Y.Opens)
    (hTW : T ≤ W) (N : W.toScheme.Modules) [N.IsQuasicoherent]
    (hN : N.IsFlatOver (W.ι ≫ p)) (hT : StandardSingleFlatCounitOnOpen p g T) :
    StandardSingleFlatCounitPresentation (T.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE hTW) N) g := by
  let a := Y.homOfLE hTW
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction a
  let e := (adj.leftAdjointUniq (Scheme.Modules.restrictAdjunction a)).app N
  have : (Scheme.Modules.tensorPullbackObj a N).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent T.toScheme.ringCatSheaf).prop_of_iso e.symm
      (inferInstance : (N.restrict a).IsQuasicoherent)
  have hn : (Scheme.Modules.tensorPullbackObj a N).IsFlatOver (T.ι ≫ p) := by
    apply unionBounded_flatOver_of_iso _ e
    simpa only [a, ← Category.assoc, Scheme.homOfLE_ι] using
      unionBounded_flatOver_restrict a (W.ι ≫ p) N hN
  exact hT _ hn

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unionBounded_mem_minus_of_presentation
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B)
    (h : StandardSingleFlatCounitPresentation p M g) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    DerivedCategory.TStructure.t.minus ((schemeDerivedDirectImage p).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  obtain ⟨K, ⟨b, hb⟩, _, e, _, _⟩ := h
  have : K.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff K b).2 hb
  have : (DerivedCategory.Q.obj K).IsLE b := inferInstance
  refine ⟨b, ?_⟩
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (((DerivedCategory.quotientCompQhIso _).app K).symm ≪≫ e.symm) b

set_option backward.isDefEq.respectTransparency false in
private theorem unionBounded_minus_biprod
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {E F : DerivedCategory C}
    (hE : DerivedCategory.TStructure.t.minus E)
    (hF : DerivedCategory.TStructure.t.minus F) :
    DerivedCategory.TStructure.t.minus (E ⊞ F) := by
  let P := (DerivedCategory.TStructure.t (C := C)).minus
  exact P.ext_of_isTriangulatedClosed₂ _
    (Pretriangulated.binaryBiproductTriangle_distinguished E F) hE hF

/-- The union direct image admits a bounded-above complex representative. -/
theorem exists_boundedAbove_union_model
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    [IsAffine B] [IsAffine A] (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) [N.IsQuasicoherent]
    (hN : N.IsFlatOver ((U ⊔ V).ι ≫ p))
    (hPU : StandardSingleFlatCounitOnOpen p g U)
    (hPV : StandardSingleFlatCounitOnOpen p g V)
    (hPUV : StandardSingleFlatCounitOnOpen p g (U ⊓ V)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    letI := HasDerivedCategory.standard A.Modules
    letI := HasDerivedCategory.standard B.Modules
    ∃ K : CochainComplex (SheafOfModules.{u} (moduleRings B.toRingedSpace)) ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)) ∧
      Nonempty (((schemeDerivedDirectImage ((U ⊔ V).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N) ≅
          DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) := by
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let := HasDerivedCategory.standard A.Modules
  let := HasDerivedCategory.standard B.Modules
  let P := (DerivedCategory.TStructure.t
    (C := SheafOfModules.{u} (moduleRings B.toRingedSpace))).minus
  have hU := unionBounded_mem_minus_of_presentation _ _ _
    (unionBounded_presentation_on_subopen p g (U ⊔ V) U le_sup_left N hN hPU)
  have hV := unionBounded_mem_minus_of_presentation _ _ _
    (unionBounded_presentation_on_subopen p g (U ⊔ V) V le_sup_right N hN hPV)
  have hUV := unionBounded_mem_minus_of_presentation _ _ _
    (unionBounded_presentation_on_subopen p g (U ⊔ V) (U ⊓ V)
      (inf_le_left.trans le_sup_left) N hN hPUV)
  obtain ⟨_, _, _, _, _, i, _⟩ := exists_derivedPullbackComposition
  let L := derivedPullback (𝟙 B)
  have hL (E : schemeDerivedCategory B) (hE : P E) : P (L.obj E) :=
    P.prop_of_iso ((i B).app E).symm hE
  obtain ⟨S, S', m, e₁, e₂, e₃, e₁', e₂', e₃', hS, _, _, _, _⟩ :=
    standardSingle_union_ses_presentation p (𝟙 B) U V N
  have h₂ : P (DerivedCategory.Q.obj S.X₂) :=
    P.prop_of_iso e₂.symm (unionBounded_minus_biprod (hL _ hU) (hL _ hV))
  have h₃ : P (DerivedCategory.Q.obj S.X₃) := P.prop_of_iso e₃.symm (hL _ hUV)
  have h₁ : P (DerivedCategory.Q.obj S.X₁) :=
    P.ext_of_isTriangulatedClosed₁ _ (DerivedCategory.triangleOfSES_distinguished hS) h₂ h₃
  have hW := P.prop_of_iso (e₁ ≪≫ (i B).app _) h₁
  obtain ⟨b, hb⟩ := hW
  have hbound : ((schemeDerivedDirectImage ((U ⊔ V).ι ≫ p)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE b := hb
  obtain ⟨K, hK, ⟨eK⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE
    ((schemeDerivedDirectImage ((U ⊔ V).ι ≫ p)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)) b
  let := hK
  exact ⟨K, ⟨b, fun j hj ↦ CochainComplex.isZero_of_isStrictlyLE K b j hj⟩,
    ⟨eK ≪≫ ((DerivedCategory.quotientCompQhIso _).app K).symm⟩⟩

end AlgebraicGeometry
