/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension

/-!
# Uniform vanishing for torsion abelian higher direct images

Source: Stacks Project, Tag 0F10, and the separable-closure descent proof in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension`.
(blueprint: lem-kun-torsion-abelian-direct-image-dimension-bound).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

private theorem torsion_forget_upperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (hF : ((sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj F).IsTorsion) :
    ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f).obj F)).IsTorsion := by
  exact Sheaf.IsTorsion.of_iso
    (asIso ((Etale.upperStarForget₂ (ULift.{u + 1} ℤ) f).app F))
    (Etale.isTorsion_upperStar f hF)

private theorem module_vanishing
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) (n : ℕ)
    (hn : ∀ (L : Type u) [Field L] (s : Spec (.of L) ⟶ Spec (.of K)) {P : Scheme.{u}}
      (p₁ : P ⟶ X) (p₂ : P ⟶ Spec (.of L)), IsPullback p₁ p₂ aX s →
        topologicalKrullDim P ≤ (n : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (hF : ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj F).IsTorsion)
    (q : ℤ) (hq : (2 * n : ℤ) < q) :
    IsZero (Etale.higherDirectImage (ULift.{u + 1} ℤ) f q F) := by
  let Λ := ULift.{u + 1} ℤ
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := ⟨⟩
  -- the cofiltered system of the `X_L`, for the finite subextensions `L` of `K^sep / K`
  let Ks := SeparableClosure K
  let I := IntermediateField.FiniteSubext K Ks
  let D : Iᵒᵖ ⥤ Scheme.{u} := (IntermediateField.subextDiagram K Ks).op ⋙ Scheme.Spec
  let c : Cone D := subextSpecCone K Ks
  have hc : IsLimit c := isLimitSubextSpecCone K Ks
  have hD {i j : Iᵒᵖ} (g : i ⟶ j) : IsAffineHom (D.map g) :=
    inferInstanceAs (IsAffineHom (Spec.map _))
  let i₀ : Iᵒᵖ := Opposite.op ⟨⊥, inferInstance⟩
  let ρ : CommRingCat.of (⊥ : IntermediateField K Ks) ≅ CommRingCat.of K :=
    (IntermediateField.botEquiv K Ks).toRingEquiv.toCommRingCatIso
  let p : X ⟶ D.obj i₀ := aX ≫ Spec.map ρ.hom
  let pY : Y ⟶ D.obj i₀ := aY ≫ Spec.map ρ.hom
  let D' := baseChangeDiagram D p
  let c' := baseChangeCone D c p
  have hc' : IsLimit c' := isLimitBaseChangeCone D c p hc
  let D'' : Over i₀ ⥤ Over X :=
    { obj j := Over.mk (pullback.fst p (D.map j.hom))
      map g := Over.homMk (D'.map g) (baseChangeDiagram_map_fst D p g)
      map_id j := by ext1; exact D'.map_id j
      map_comp g h := by ext1; exact D'.map_comp g h }
  let c'' : Cone D'' :=
    { pt := Over.mk (pullback.fst p (c.π.app i₀))
      π := { app j := Over.homMk (c'.π.app j) (baseChangeCone_π_app_fst D c p j)
             naturality j j' g := by ext1; exact c'.π.naturality g } }
  have hc'' : IsLimit ((Over.forget X).mapCone c'') := hc'
  have : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) := hD
  have (j j' : Over i₀) (g : j ⟶ j') : IsAffineHom (D''.map g).left :=
    inferInstanceAs (IsAffineHom (D'.map g))
  have (j : Over i₀) : QuasiCompact ((D''.obj j).hom ≫ f) :=
    inferInstanceAs (QuasiCompact (pullback.fst p (D.map j.hom) ≫ f))
  have (j : Over i₀) : QuasiSeparated ((D''.obj j).hom ≫ f) := by
    have : IsAffine (D.obj j.left) := inferInstanceAs (IsAffine (Spec _))
    have : QuasiSeparatedSpace (D''.obj j).left :=
      (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd p (D.map j.hom))).mp inferInstance
    exact inferInstanceAs (QuasiSeparated (pullback.fst p (D.map j.hom) ≫ f))
  have : IsAffine c.pt := inferInstanceAs (IsAffine (Spec _))
  have : IsAffineHom (c.π.app i₀) := inferInstanceAs (IsAffineHom (Spec.map _))
  have : QuasiCompact (c''.pt.hom ≫ f) :=
    inferInstanceAs (QuasiCompact (pullback.fst p (c.π.app i₀) ≫ f))
  have : QuasiSeparated (c''.pt.hom ≫ f) := by
    have : QuasiSeparatedSpace c''.pt.left :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (c.π.app i₀))
    exact inferInstanceAs (QuasiSeparated (pullback.fst p (c.π.app i₀) ≫ f))
  -- the higher direct image vanishes over the limit `X_{K^sep}`
  have hT : IsZero (Etale.higherDirectImage Λ (c''.pt.hom ≫ f) q
      ((c''.pt.hom)^*[ModuleCat.{u + 1} Λ].obj F)) := by
    let aT : pullback p (c.π.app i₀) ⟶ Spec (.of Ks) := pullback.snd p (c.π.app i₀)
    have hρ : (Scheme.Spec.mapIso ρ.symm.op).hom = Spec.map ρ.inv := rfl
    have hρρ : Spec.map ρ.hom ≫ Spec.map ρ.inv = 𝟙 _ := by
      rw [← Spec.map_comp, ρ.inv_hom_id, Spec.map_id]
    have hpb : IsPullback (pullback.fst p (c.π.app i₀)) aT aX
        (c.π.app i₀ ≫ Spec.map ρ.inv) :=
      (IsPullback.of_hasPullback p (c.π.app i₀)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (Scheme.Spec.mapIso ρ.symm.op) (by simp)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        (by
          erw [hρ]
          exact (Category.assoc _ _ _).trans ((congrArg (aX ≫ ·) hρρ).trans
            (Category.comp_id _)))
        (by
          erw [hρ]
          exact (Category.id_comp _).symm)
    have : LocallyOfFiniteType aT :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
    exact Etale.isZero_higherDirectImage_of_two_mul_lt_of_acyclic_of_quasiCompact
      (k := Ks) (c''.pt.hom ≫ f) aT n (hn Ks _ _ _ hpb)
      (fun V I _ m ↦ Etale.subsingleton_H_forget₂_uliftInt_of_injective I m) _
      (fun V ↦ torsion_forget_upperStar V.hom _
        (torsion_forget_upperStar c''.pt.hom F hF)) q hq
  -- the transition maps from `X` to the stages `X_L` are monomorphisms
  let X₀ : Over X := Over.mk (𝟙 X)
  have hmono (j : Over i₀) (ψ : D''.obj j ⟶ X₀) :
      Mono (Etale.higherDirectImageOverMap Λ f F q ψ) := by
    let L : IntermediateField K Ks := j.left.unop.1
    have : FiniteDimensional K L := j.left.unop.2
    have hr : (IntermediateField.subextDiagram K Ks).map j.hom.unop =
        ρ.hom ≫ CommRingCat.ofHom (algebraMap K L) := by
      ext x
      exact IntermediateField.inclusion_bot_apply _ _ x
    have hDj : D.map j.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ Spec.map ρ.hom := by
      rw [← Spec.map_comp, ← hr]
      rfl
    have : IsIso (Spec.map ρ.hom) := inferInstanceAs (IsIso (Scheme.Spec.mapIso ρ.op).hom)
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
      have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
      have : Algebra.FinitePresentation K L :=
        Algebra.FinitePresentation.of_finiteType.mp inferInstance
      exact HasRingHomProperty.Spec_iff.mpr
        (RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩)
    have hE : Etale (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ Spec.map ρ.hom) :=
      inferInstance
    have hS : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ Spec.map ρ.hom) :=
      inferInstance
    have : Etale (D.map j.hom) := by
      rw [hDj]
      exact hE
    have : Surjective (D.map j.hom) := by
      rw [hDj]
      exact hS
    have hψ : ψ.left = pullback.fst p (D.map j.hom) := by simpa [X₀, D''] using Over.w ψ
    have h₂ := pullback.condition (f := pY) (g := D.map j.hom)
    refine Etale.mono_higherDirectImageOverMap Λ f F q ψ (pullback.fst pY (D.map j.hom))
      (Surjective.surj (f := pullback.fst pY (D.map j.hom)))
      (IsPullback.of_hasPullback (X₀.hom ≫ f) (pullback.fst pY (D.map j.hom)))
      (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd pY (D.map j.hom)) ?_) ?_
    · have h₃ : (X₀.hom ≫ f) ≫ pY = p := by simp [X₀, p, pY, ← hf]
      rw [← h₃]
      exact (pullback.condition_assoc pY).trans ((congrArg (_ ≫ ·) h₂).trans
        (Category.assoc _ _ _).symm)
    · rw [hψ, pullback.lift_fst]
  -- hence the higher direct image vanishes, by the limit theorem
  let R₀ := Etale.higherDirectImage Λ (X₀.hom ≫ f) q ((X₀.hom)^*[ModuleCat.{u + 1} Λ].obj F)
  have hR₀ : IsZero R₀ := Etale.isZero_higherDirectImage_of_isLimit_of_mono Λ f F D'' c'' hc'' q
    (i₀ := Over.mk (𝟙 i₀)) (Over.homMk (D''.obj (Over.mk (𝟙 i₀))).hom (by simp [X₀])) hmono hT
  have e : R₀ = Etale.higherDirectImage Λ f q ((𝟙 X)^*[ModuleCat.{u + 1} Λ].obj F) := by
    simp [R₀, X₀]
  rw [e] at hR₀
  exact hR₀.of_iso ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (R+((f)_*[ModuleCat.{u + 1} Λ]).mapIso ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((Etale.upperStarId (ModuleCat.{u + 1} Λ) X).app F).symm)))

/-- A uniform dimension bound after extension of the ground field bounds higher direct
images of every torsion abelian sheaf. Source: Stacks Project, Tag 0F10; separable-closure
descent as in the source library's Kunneth/CohomologicalDimension module.
(blueprint: lem-kun-torsion-abelian-direct-image-dimension-bound)

Proof: Regard abelian sheaves as sheaves of modules over ULift Z. Over a separably closed
field, apply the finite-type cohomology bound on affine etale objects of the target.
Injective ULift Z-module sheaves have injective underlying abelian sheaves, so the Ext
comparison computes this as higher direct image. Torsion is preserved by inverse image
and by the comparison with underlying abelian sheaves. For an arbitrary ground field,
write its separable closure as the filtered union of finite separable subextensions.
Base change the source to this system. Its higher direct image at the limit vanishes
by the separably closed case and the uniform dimension bound. Transition maps from the
original higher direct image are monic: after the etale surjective extension of the
target they factor the base change isomorphism. Continuity then forces the original
higher direct image to vanish. Finally, the exact equivalence with abelian sheaves
commutes with single-degree complexes, derived direct image, and homology. -/
theorem isZero_torsion_higherDirectImage_of_forall_field_dimension_le
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) (n : ℕ)
    (hn : ∀ (L : Type u) [Field L] (s : Spec (.of L) ⟶ Spec (.of K)) {P : Scheme.{u}}
      (p₁ : P ⟶ X) (p₂ : P ⟶ Spec (.of L)), IsPullback p₁ p₂ aX s →
        topologicalKrullDim P ≤ (n : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (q : ℤ) (hq : (2 * n : ℤ) < q) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  let ΦX := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let ΦY := sheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let M := ΦX.asEquivalence.inverse.obj F
  let e : ΦX.obj M ≅ F := ΦX.asEquivalence.counitIso.app F
  have hM : (ΦX.obj M).IsTorsion := Sheaf.IsTorsion.of_iso e.symm hF
  have hz := ΦY.map_isZero (module_vanishing aX aY f hf n hn M hM q hq)
  let eH := (ΦY.mapDerivedCategoryPlusHomologyFunctorIso q).app
    ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj M))
  let eR := (DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (asIso ((rightDerivedLowerStarForget₂ f).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj M)))
  let eS := (DerivedCategory.Plus.homologyFunctor _ q).mapIso
    ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).mapIso
      ((ΦX.mapDerivedCategoryPlusSingleFunctor 0).app M ≪≫
        (DerivedCategory.Plus.singleFunctor _ 0).mapIso e))
  exact hz.of_iso (eH ≪≫ eR ≪≫ eS).symm

end AlgebraicGeometry.Etale
