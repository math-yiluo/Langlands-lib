/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.Stability
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Kernel transforms along automorphisms

Kernel transforms are compatible with automorphisms of the kernel space, and the kernel
transform of a skyscraper-type sheaf supported along a section.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry.AffineSpace

section Automorphism

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {P V V' : Scheme.{u}} (q₁ : P ⟶ V) (q₂ : P ⟶ V') [HasCompactification q₂]
  [QuasiCompact q₂]

/-- Compact-support base change along an automorphism `σ` over `V'`. -/
private lemma kt_bc [Finite Λ] (σ : P ⟶ P) [IsIso σ] (h₂ : σ ≫ q₂ = q₂) :
    Nonempty (R(q₂)_![ModuleCat.{u + 1} Λ] ≅
      L((σ)^*[ModuleCat.{u + 1} Λ]) ⋙ R(q₂)_![ModuleCat.{u + 1} Λ]) := by
  let A := ModuleCat.{u + 1} Λ
  have sq : IsPullback σ q₂ q₂ (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨h₂.trans (Category.comp_id _).symm⟩
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  let idIso : L((𝟙 V')^*[A]) ≅ 𝟭 _ :=
    Functor.leftDerivedFunctorNatIso _ (Etale.upperStarId A _) ≪≫
      (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _
  exact ⟨(Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ idIso.symm ≪≫
      asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)⟩

/-- `D(q₁^*) ⋙ Lσ^* ≅ D(τ^*) ⋙ D(q₁^*)` for `σ ≫ q₁ = q₁ ≫ τ`. -/
private lemma kt_pc (σ : P ⟶ P) (τ : V ⟶ V) (h₁ : σ ≫ q₁ = q₁ ≫ τ) :
    Nonempty (D((q₁)^*[ModuleCat.{u + 1} Λ]) ⋙ L((σ)^*[ModuleCat.{u + 1} Λ]) ≅
      D((τ)^*[ModuleCat.{u + 1} Λ]) ⋙ D((q₁)^*[ModuleCat.{u + 1} Λ])) := by
  let A := ModuleCat.{u + 1} Λ
  let ι {X Y : Scheme.{u}} (f : X ⟶ Y) := leftDerivedUpperStarIsoMapDerivedCategory A f
  exact ⟨Functor.isoWhiskerRight (ι q₁).symm _ ≪≫
      (leftDerivedUpperStarComp A σ q₁ (q₁ ≫ τ) h₁.symm).symm ≪≫
      leftDerivedUpperStarComp A q₁ τ ≪≫
      Functor.isoWhiskerRight (ι _) _ ≪≫ Functor.isoWhiskerLeft _ (ι _)⟩

/-- `Lσ^*` commutes with tensoring by `𝒦`. -/
private lemma kt_tens (σ : P ⟶ P)
    (𝒦 : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (derivedTensorRight (ModuleCat.{u + 1} Λ) P 𝒦 ⋙ L((σ)^*[ModuleCat.{u + 1} Λ]) ≅
      L((σ)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedTensorRight (ModuleCat.{u + 1} Λ) P
        (L((σ)^*[ModuleCat.{u + 1} Λ]).obj 𝒦)) :=
  ⟨derivedTensorRightCompLeftDerivedUpperStarIso _ σ 𝒦⟩

/-- A kernel transform `K ↦ Rq₂,!(q₁^* K ⊗ᴸ 𝒦)[a]` is unchanged by an automorphism `σ` of
`P` over `V'`: if `σ` lies over the endomorphism `τ` of `V` and `Lσ^* 𝒦 ≅ 𝒦'`, then
`Rq₂,!(q₁^* K ⊗ᴸ 𝒦)[a] ≅ Rq₂,!(q₁^* τ^* K ⊗ᴸ 𝒦')[a]`, naturally in `K`. This is
compact-support base change along the cartesian square with sides `σ`, `q₂`, `q₂` and `𝟙`,
together with the monoidality of `Lσ^*`. -/
theorem nonempty_iso_kernelTransform_of_isIso [Finite Λ] (σ : P ⟶ P) [IsIso σ] (τ : V ⟶ V)
    (h₁ : σ ≫ q₁ = q₁ ≫ τ) (h₂ : σ ≫ q₂ = q₂)
    (𝒦 𝒦' : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : L((σ)^*[ModuleCat.{u + 1} Λ]).obj 𝒦 ≅ 𝒦') (a : ℤ) :
    Nonempty (D((q₁)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedTensorRight _ P 𝒦 ⋙
        R(q₂)_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ a ≅
      D((τ)^*[ModuleCat.{u + 1} Λ]) ⋙ D((q₁)^*[ModuleCat.{u + 1} Λ]) ⋙
        derivedTensorRight _ P 𝒦' ⋙ R(q₂)_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ a) := by
  obtain ⟨bc⟩ := kt_bc Λ q₂ σ h₂
  obtain ⟨pc⟩ := kt_pc Λ q₁ σ τ h₁
  obtain ⟨tens⟩ := kt_tens Λ σ 𝒦
  let X := R(q₂)_![ModuleCat.{u + 1} Λ] ⋙
    shiftFunctor (DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) a
  -- every reassociation is explicit, the kernel being slow to unfold derived functors
  exact ⟨Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight bc (shiftFunctor _ a) ≪≫ Functor.associator _ _ _)) ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight tens X ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight pc _ ≪≫
      Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight ((derivedTensor _ P).flip.mapIso e) X))⟩

/-- If `R ⋙ T ≅ (- ⊗ N) ⋙ R` and `N ≅ U` with `U ⊗ U ≅ U`, then `T (R U) ≅ R U`. This is stated
for abstract functors so that the kernel never unfolds the concrete derived functors it is
applied to. -/
private lemma nonempty_iso_of_iso_comp_flip {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) (T : D ⥤ D) (B : C ⥤ C ⥤ C) {N U : C} (pf : R ⋙ T ≅ B.flip.obj N ⋙ R)
    (e : N ≅ U) (l : (B.obj U).obj U ≅ U) : Nonempty (T.obj (R.obj U) ≅ R.obj U) :=
  ⟨pf.app U ≪≫ R.mapIso ((B.obj U).mapIso e ≪≫ l)⟩

/-- `(F ⋙ G ⋙ H ⋙ K).obj X = K.obj (H.obj (G.obj (F.obj X)))`, stated for abstract functors so
that the kernel never unfolds the concrete derived functors it is applied to. -/
private lemma _root_.CategoryTheory.Functor.comp_obj_comp_obj_comp_obj_eq
    {C₁ C₂ C₃ C₄ C₅ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Category C₅] (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₃ ⥤ C₄) (K : C₄ ⥤ C₅) (X : C₁) :
    (F ⋙ G ⋙ H ⋙ K).obj X = K.obj (H.obj (G.obj (F.obj X))) :=
  rfl

/-- `q₁^* Rz_* Λ ≅ Rz'_! Λ`, for `z'` the base change of the proper `z` along `q₁`. -/
private lemma kt_sky₁ [Finite Λ] {T : Scheme.{u}} (z : T ⟶ V) [IsProper z] (z' : V' ⟶ P)
    (g : V' ⟶ T) [HasCompactification z'] [QuasiCompact z'] (sq : IsPullback g z' z q₁) :
    Nonempty ((D((q₁)^*[ModuleCat.{u + 1} Λ])).obj
        ((R((z)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)) ≅
      (R(z')_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) := by
  let A := ModuleCat.{u + 1} Λ
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  obtain ⟨pz⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar A z
  exact ⟨(leftDerivedUpperStarIsoMapDerivedCategory A q₁).symm.app _ ≪≫
      (L((q₁)^*[A])).mapIso (pz.symm.app _) ≪≫
      (asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)).app _ ≪≫
      (R(z')_![A]).mapIso (leftDerivedUpperStarUnitIso A g)⟩

/-- `Rz'_! Λ ⊗ᴸ 𝒦 ≅ Rz'_!(Λ ⊗ᴸ z'^* 𝒦) ≅ Rz'_! Λ` when `z'^* 𝒦 ≅ Λ`. -/
private lemma kt_sky₂ [Finite Λ] (z' : V' ⟶ P) [HasCompactification z']
    (𝒦 : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : L((z')^*[ModuleCat.{u + 1} Λ]).obj 𝒦 ≅ 𝟙_ _) :
    Nonempty ((derivedTensorRight _ P 𝒦).obj ((R(z')_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) ≅
      (R(z')_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) := by
  let A := ModuleCat.{u + 1} Λ
  obtain ⟨pf⟩ := nonempty_iso_rightDerivedLowerShriek_comp_derivedTensorRight A z' 𝒦
    (fun K ↦ hasProjectionFormula_of_finite Λ _ K 𝒦)
  exact nonempty_iso_of_iso_comp_flip _ _ (derivedTensor A V') pf e (derivedTensorLeftUnitor A V' _)

omit [QuasiCompact q₂] in
/-- `Rq₂,! Rz'_! Λ ≅ Λ` for a section `z'` of `q₂`. -/
private lemma kt_sky₃ [Finite Λ] (z' : V' ⟶ P) [HasCompactification z'] (hz : z' ≫ q₂ = 𝟙 V') :
    Nonempty ((R(q₂)_![ModuleCat.{u + 1} Λ]).obj ((R(z')_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) ≅
      𝟙_ _) := by
  let A := ModuleCat.{u + 1} Λ
  have : HasCompactification (z' ≫ q₂) := .of_eq hz.symm
  have : QuasiCompact (z' ≫ q₂) := by rw [hz]; infer_instance
  obtain ⟨pid⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar A (𝟙 V')
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ z' q₂
  have hcongr {X Y : Scheme.{u}} {f f' : X ⟶ Y} [HasCompactification f]
      [HasCompactification f'] (h : f = f') : Nonempty (R(f)_![A] ≅ R(f')_![A]) := by
    subst h
    exact ⟨Iso.refl _⟩
  obtain ⟨cc⟩ := hcongr hz
  exact ⟨(c.app _).symm ≪≫ cc.app _ ≪≫ pid.app _ ≪≫ (rightDerivedLowerStarIdIso Λ V').app _⟩

omit [QuasiCompact q₂] in
/-- The kernel transform `Rq₂,!(q₁^*(-) ⊗ᴸ 𝒦)` of a skyscraper `Rz_* Λ` along a proper
`z : T ⟶ V`: if the base change `z'` of `z` along `q₁` is a section of `q₂` and the kernel is
trivial along `z'`, then the transform of `Rz_* Λ` is `Λ`. This is `Rz_* = Rz_!`,
compact-support base change along `q₁`, the projection formula for `z'` and the composition
law `R(z' ≫ q₂)_! = R(𝟙)_!`. -/
theorem nonempty_iso_kernelTransform_obj_rightDerivedLowerStar [Finite Λ] {T : Scheme.{u}}
    (z : T ⟶ V) [IsProper z] (z' : V' ⟶ P) (g : V' ⟶ T) [HasCompactification z']
    [QuasiCompact z'] (sq : IsPullback g z' z q₁) (hz : z' ≫ q₂ = 𝟙 V')
    (𝒦 : DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : L((z')^*[ModuleCat.{u + 1} Λ]).obj 𝒦 ≅ 𝟙_ _) (a : ℤ) :
    Nonempty ((D((q₁)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedTensorRight _ P 𝒦 ⋙
        R(q₂)_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ a).obj
          ((R((z)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _)) ≅ (shiftFunctor _ a).obj (𝟙_ _)) := by
  obtain ⟨s₁⟩ := kt_sky₁ Λ q₁ z z' g sq
  obtain ⟨s₂⟩ := kt_sky₂ Λ z' 𝒦 e
  obtain ⟨s₃⟩ := kt_sky₃ Λ q₂ z' hz
  exact ⟨eqToIso (Functor.comp_obj_comp_obj_comp_obj_eq _ _ _ _ _) ≪≫ (shiftFunctor _ a).mapIso
    ((R(q₂)_![ModuleCat.{u + 1} Λ]).mapIso ((derivedTensorRight _ P 𝒦).mapIso s₁ ≪≫ s₂) ≪≫ s₃)⟩

/-- The derived pullback of a sheaf placed in degree zero is the pullback of the sheaf, placed
in degree zero. -/
lemma nonempty_iso_leftDerivedUpperStar_singleFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (e : (f)^*[ModuleCat.{u + 1} Λ].obj F ≅ G) :
    Nonempty (L((f)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.singleFunctor _ 0).obj G) :=
  ⟨(leftDerivedUpperStarIsoMapDerivedCategory _ f).app _ ≪≫
    (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e⟩

end Automorphism

end AlgebraicGeometry.Etale
