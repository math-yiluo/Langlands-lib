/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedSections
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnboundedDerivedBoundary
import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
import WeilConjectures.CategoryTheory.Sites.SectionsWithSupport
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Canonically normalized support localization

This extends the existence interface with the injective-complex normalization
of the boundary. The ordinary arrows are uniquely fixed by the support kernel inclusions.

## References

* Tag 09XP, restriction construction
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

private lemma supportι_mono (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (W : T.Opens) : Mono (supportedEtaleSectionsι A T W) := by
  dsimp [supportedEtaleSectionsι]
  infer_instance

attribute [local instance] supportι_mono

private lemma supportι_app_mono (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (W : T.Opens)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Mono ((supportedEtaleSectionsι A T W).app M) := by infer_instance

attribute [local instance] supportι_app_mono

private theorem globalSectionsComparison_eq (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).hom.app M = M.ΓRes (Opposite.op (⊤_ X.Etale)) := by
  let adj := constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let adj' := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
    (terminalIsTerminal (C := X.Etale))
  have hc := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app adj adj' M
  apply (adj'.homEquiv _ M).symm.injective
  change (adj'.homEquiv _ M).symm ((adj.rightAdjointUniq adj').hom.app M) = _
  rw [hc]
  apply (adj'.homEquiv _ M).injective
  rw [Equiv.apply_symm_apply]
  change (CategoryTheory.constantPresheafAdj (ModuleCat.{u + 1} A)
      (terminalIsTerminal (C := X.Etale))).homEquiv _ _
    ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _
      (adj.counit.app M)) = _
  rw [Adjunction.homEquiv_unit]
  change (𝟙 _) ≫ ((sheafificationAdjunction X.smallEtaleTopology
      (ModuleCat.{u + 1} A)).homEquiv _ _ (adj.counit.app M)).app
        (Opposite.op (⊤_ X.Etale)) =
    ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _
      ((adj.homEquiv _ M).symm (𝟙 _))).app (Opposite.op (⊤_ X.Etale))
  rw [Category.id_comp, adj.homEquiv_symm_id]
  rfl

private theorem globalSectionsUpperStarMap_comp_ΓRes
    (A : Type (u + 1)) [CommRing A] {T S : Scheme.{u}} (h : S ⟶ T)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (V : T.Etale) (W : S.Etale) (φ : W.left ⟶ V.left)
    (hφ : φ ≫ V.hom = W.hom ≫ h) :
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h M ≫
        ((upperStar (ModuleCat.{u + 1} A) h).obj M).ΓRes (Opposite.op W) =
      M.ΓRes (Opposite.op V) ≫
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
          (Opposite.op V) ≫
        ((upperStar (ModuleCat.{u + 1} A) h).obj M).obj.map
          (homToPullback h φ hφ).op := by
  let N := (upperStar (ModuleCat.{u + 1} A) h).obj M
  let e := Sheaf.ΓNatIsoSheafSections S.smallEtaleTopology
    (ModuleCat.{u + 1} A) terminalIsTerminal
  have he : e.inv.app N ≫ N.ΓRes (Opposite.op W) =
      N.obj.map (terminal.from W).op := by
    apply (cancel_epi (e.hom.app N)).1
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    change N.ΓRes (Opposite.op W) = e.hom.app N ≫ _
    rw [globalSectionsComparison_eq]
    exact (Sheaf.ΓRes_map N (terminal.from W).op).symm
  have hm : terminal.from W ≫ (PreservesTerminal.iso h.Etale).inv =
      homToPullback h φ hφ ≫ h.Etale.map (terminal.from V) :=
    (isLimitOfPreserves h.Etale (limit.isLimit (Functor.empty T.Etale))).hom_ext
      (fun j ↦ isEmptyElim j)
  simp only [globalSectionsUpperStarMap, Category.assoc]
  change _ ≫ _ ≫ N.obj.map _ ≫ e.inv.app N ≫ N.ΓRes (Opposite.op W) = _
  rw [he, ← N.obj.map_comp, ← op_comp, hm, op_comp, N.obj.map_comp]
  have hu := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.naturality
    (terminal.from V).op
  change M.obj.map (terminal.from V).op ≫
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
        (Opposite.op V) =
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
        (Opposite.op (⊤_ T.Etale)) ≫ N.obj.map (h.Etale.map (terminal.from V)).op at hu
  change (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).hom.app M ≫
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
        (Opposite.op (⊤_ T.Etale)) ≫ _ ≫ _ = _
  rw [← reassoc_of% hu, globalSectionsComparison_eq, Sheaf.ΓRes_map_assoc]

private theorem sectionsUpperStarMap_localization
    (A : Type (u + 1)) [CommRing A] {T S : Scheme.{u}} (h : S ⟶ T) [Etale h]
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (V : T.Etale) (W : S.Etale) (φ : W.left ⟶ V.left)
    (hφ : φ ≫ V.hom = W.hom ≫ h) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
        (Opposite.op V) ≫
      ((upperStar (ModuleCat.{u + 1} A) h).obj M).obj.map (homToPullback h φ hφ).op ≫
      ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) h inferInstance).hom.app
        M).hom.app (Opposite.op W) =
      M.obj.map (MorphismProperty.Over.homMk φ hφ :
        (MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W ⟶ V).op := by
  let e := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) h inferInstance
  have h₁ := Adjunction.unit_leftAdjointUniq_hom_app
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)
    (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) h inferInstance) M
  have h₂ := congrArg (fun α ↦ α.hom.app (Opposite.op V)) h₁
  have h₃ :
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
        (Opposite.op V) ≫ (e.hom.app M).hom.app
        (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj V)) =
      M.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ h
        inferInstance trivial).counit.app V).op := h₂
  rw [((e.hom.app M).hom.naturality (homToPullback h φ hφ).op)]
  rw [← Category.assoc, h₃]
  change M.obj.map _ ≫ M.obj.map _ = _
  rw [← M.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp [homToPullback]

private theorem sectionsUpperStarMap_isIso
    (A : Type (u + 1)) [CommRing A] {T S : Scheme.{u}} (h : S ⟶ T) [Etale h]
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (V : T.Etale) (W : S.Etale) (φ : W.left ⟶ V.left) [IsIso φ]
    (hφ : φ ≫ V.hom = W.hom ≫ h) :
    IsIso (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
        (Opposite.op V) ≫
      ((upperStar (ModuleCat.{u + 1} A) h).obj M).obj.map (homToPullback h φ hφ).op) := by
  let ψ : (MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W ⟶ V :=
    MorphismProperty.Over.homMk φ hφ
  have : IsIso ψ := ⟨MorphismProperty.Over.homMk (inv φ)
    (by rw [IsIso.inv_comp_eq, hφ]; rfl),
    MorphismProperty.Over.Hom.ext (by simp [ψ]),
    MorphismProperty.Over.Hom.ext (by simp [ψ])⟩
  have he : IsIso (((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) h
      inferInstance).hom.app M).hom.app (Opposite.op W)) :=
    inferInstanceAs (IsIso (((sheafSections _ _).obj (Opposite.op W)).map
      ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) h
        inferInstance).hom.app M)))
  have hi : IsIso (((((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app
      M).hom.app (Opposite.op V)) ≫
      ((upperStar (ModuleCat.{u + 1} A) h).obj M).obj.map (homToPullback h φ hφ).op) ≫
    (((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) h
      inferInstance).hom.app M).hom.app (Opposite.op W))) := by
    rw [Category.assoc, sectionsUpperStarMap_localization]
    exact inferInstanceAs (IsIso (M.obj.map ψ.op))
  exact IsIso.of_isIso_comp_right _
    (((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) h
      inferInstance).hom.app M).hom.app (Opposite.op W))

private theorem globalSectionsUpperStarMap_naturality (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (m : X ⟶ Y)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)} (k : F ⟶ F') :
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)).map k ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F' =
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F ≫
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStar (ModuleCat.{u + 1} A) m).map k) := by
  let eL := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal
  let eK := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) m
  have hu := congrArg (fun φ ↦ φ.hom.app (Opposite.op (⊤_ Y.Etale))) (adj.unit.naturality k)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  simp only [globalSectionsUpperStarMap, Category.assoc]
  rw [eL.hom.naturality_assoc k]
  change eL.hom.app F ≫ k.hom.app (Opposite.op (⊤_ Y.Etale)) ≫
      (adj.unit.app F').hom.app (Opposite.op (⊤_ Y.Etale)) ≫
      ((upperStar (ModuleCat.{u + 1} A) m).obj F').obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
      eK.inv.app _ =
    eL.hom.app F ≫ (adj.unit.app F).hom.app (Opposite.op (⊤_ Y.Etale)) ≫
      ((upperStar (ModuleCat.{u + 1} A) m).obj F).obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
      eK.inv.app _ ≫ (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStar (ModuleCat.{u + 1} A) m).map k)
  rw [reassoc_of% hu]
  have hn := ((upperStar (ModuleCat.{u + 1} A) m).map k).hom.naturality
    (PreservesTerminal.iso m.Etale).inv.op
  change ((upperStar (ModuleCat.{u + 1} A) m).obj F).obj.map
      (PreservesTerminal.iso m.Etale).inv.op ≫
      ((upperStar (ModuleCat.{u + 1} A) m).map k).hom.app (Opposite.op (⊤_ X.Etale)) =
    ((lowerStar (ModuleCat.{u + 1} A) m).map ((upperStar (ModuleCat.{u + 1} A) m).map k)).hom.app
      (Opposite.op (⊤_ Y.Etale)) ≫
      ((upperStar (ModuleCat.{u + 1} A) m).obj F').obj.map
        (PreservesTerminal.iso m.Etale).inv.op at hn
  rw [← reassoc_of% hn]
  have hk := eK.inv.naturality ((upperStar (ModuleCat.{u + 1} A) m).map k)
  change ((upperStar (ModuleCat.{u + 1} A) m).map k).hom.app
    (Opposite.op (⊤_ X.Etale)) ≫ eK.inv.app _ =
    eK.inv.app _ ≫ (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStar (ModuleCat.{u + 1} A) m).map k) at hk
  rw [hk]

private theorem supportι_comp_ΓRes_of_le (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (O U : T.Opens) (hU : U ≤ O)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (supportedEtaleSectionsι A T O).app M ≫
      M.ΓRes (Opposite.op (Scheme.Etale.mk U.ι)) = 0 := by
  let f : Scheme.Etale.mk U.ι ⟶ Scheme.Etale.mk O.ι :=
    MorphismProperty.Over.homMk (T.homOfLE hU) (T.homOfLE_ι hU)
  rw [← Sheaf.ΓRes_map M f.op, ← Category.assoc]
  have hk := NatTrans.congr_app (kernel.condition (Sheaf.natTransΓRes
    T.smallEtaleTopology (ModuleCat.{u + 1} A) (Opposite.op (Scheme.Etale.mk O.ι)))) M
  change (supportedEtaleSectionsι A T O).app M ≫
    M.ΓRes (Opposite.op (Scheme.Etale.mk O.ι)) = 0 at hk
  rw [hk, zero_comp]

private theorem ΓRes_mkId_isIso (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso (M.ΓRes (Opposite.op (Scheme.Etale.mk (𝟙 T)))) :=
  (Sheaf.isLimitConeΓ M).isIso_π_app_of_isInitial _
    (MorphismProperty.Over.mkIdTerminal @Etale T).op

private theorem isIso_of_kernel_square {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasKernels C] {K₁ K₂ X₁ X₂ Y₁ Y₂ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (ι₁ : K₁ ⟶ X₁) (ι₂ : K₂ ⟶ X₂)
    (h₁ : ι₁ ≫ f₁ = 0) (h₂ : ι₂ ≫ f₂ = 0)
    (κ₁ : IsLimit (KernelFork.ofι ι₁ h₁)) (κ₂ : IsLimit (KernelFork.ofι ι₂ h₂))
    (r : K₁ ⟶ K₂) (p : X₁ ⟶ X₂) (q : Y₁ ⟶ Y₂) [IsIso p] [Mono q]
    (h : f₁ ≫ q = p ≫ f₂) (hr : r ≫ ι₂ = ι₁ ≫ p) : IsIso r := by
  let e₁ := κ₁.conePointUniqueUpToIso (kernelIsKernel f₁)
  let e₂ := κ₂.conePointUniqueUpToIso (kernelIsKernel f₂)
  have he₁ : e₁.hom ≫ kernel.ι f₁ = ι₁ :=
    κ₁.conePointUniqueUpToIso_hom_comp (kernelIsKernel f₁) WalkingParallelPair.zero
  have he₂ : e₂.inv ≫ ι₂ = kernel.ι f₂ :=
    κ₂.conePointUniqueUpToIso_inv_comp (kernelIsKernel f₂) WalkingParallelPair.zero
  have : Mono ι₂ := Fork.IsLimit.mono κ₂
  have hr' : r = e₁.hom ≫ kernel.map f₁ f₂ p q h ≫ e₂.inv := by
    apply (cancel_mono ι₂).1
    rw [hr, Category.assoc, Category.assoc, he₂, kernel.lift_ι,
      ← Category.assoc, he₁]
  rw [hr']
  infer_instance

private noncomputable def openSquare {T : Scheme.{u}} (U W : T.Opens) : Square T.Etale where
  X₁ := Scheme.Etale.mk (U ⊓ W).ι
  X₂ := Scheme.Etale.mk U.ι
  X₃ := Scheme.Etale.mk W.ι
  X₄ := Scheme.Etale.mk (U ⊔ W).ι
  f₁₂ := MorphismProperty.Over.homMk (T.homOfLE inf_le_left) (T.homOfLE_ι _)
  f₁₃ := MorphismProperty.Over.homMk (T.homOfLE inf_le_right) (T.homOfLE_ι _)
  f₂₄ := MorphismProperty.Over.homMk (T.homOfLE le_sup_left) (T.homOfLE_ι _)
  f₃₄ := MorphismProperty.Over.homMk (T.homOfLE le_sup_right) (T.homOfLE_ι _)
  fac := by
    apply MorphismProperty.Over.Hom.ext
    change T.homOfLE inf_le_left ≫ T.homOfLE le_sup_left =
      T.homOfLE inf_le_right ≫ T.homOfLE le_sup_right
    rw [← cancel_mono (U ⊔ W).ι]
    simp only [Category.assoc, Scheme.homOfLE_ι]

private theorem openSquare_sections (A : Type (u + 1)) [CommRing A]
    {T : Scheme.{u}} (U W : T.Opens)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ((openSquare U W).op.map (M.obj ⋙ forget (ModuleCat.{u + 1} A))).IsPullback := by
  have hp : (openSquare U W).IsPullback := by
    apply IsPullback.of_map (Scheme.Etale.forget T ⋙ Over.forget T)
    · exact (openSquare U W).fac
    · exact isPullback_opens_inf_le (le_sup_left : U ≤ U ⊔ W) le_sup_right
  have h₂ : Mono (openSquare U W).f₂₄ :=
    (Scheme.Etale.forget T ⋙ Over.forget T).mono_of_mono_map (by
      change Mono (T.homOfLE (le_sup_left : U ≤ U ⊔ W)); infer_instance)
  have h₃ : Mono (openSquare U W).f₃₄ :=
    (Scheme.Etale.forget T ⋙ Over.forget T).mono_of_mono_map (by
      change Mono (T.homOfLE (le_sup_right : W ≤ U ⊔ W)); infer_instance)
  have hc : Sieve.ofTwoArrows (openSquare U W).f₂₄ (openSquare U W).f₃₄ ∈
      T.smallEtaleTopology (openSquare U W).X₄ := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    rcases x.property with hx | hx
    · refine ⟨WalkingPair.left, ⟨x.val, hx⟩, ?_⟩
      change T.homOfLE le_sup_left ⟨x.val, hx⟩ = x
      apply Subtype.ext
      exact Scheme.homOfLE_apply _ _
    · refine ⟨WalkingPair.right, ⟨x.val, hx⟩, ?_⟩
      change T.homOfLE le_sup_right ⟨x.val, hx⟩ = x
      apply Subtype.ext
      exact Scheme.homOfLE_apply _ _
  let P := M.obj ⋙ forget (ModuleCat.{u + 1} A)
  have hP : Presheaf.IsSheaf T.smallEtaleTopology P :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ M.property
  let sq := openSquare U W
  apply Square.IsPullback.mk
  refine PullbackCone.IsLimit.mk _
    (fun t ↦ hP.amalgamateOfArrows _ hc
      (fun j ↦ WalkingPair.casesOn j t.fst t.snd)
      (fun V ↦ by
        rintro (_ | _) (_ | _) a b fac
        · obtain rfl : a = b := (cancel_mono sq.f₂₄).1 fac
          rfl
        · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hp.isLimit _ _ fac
          have ht : t.fst ≫ P.map sq.f₁₂.op = t.snd ≫ P.map sq.f₁₃.op := t.condition
          simpa only [Functor.map_comp, op_comp, Category.assoc, sq, Square.pullbackCone,
            PullbackCone.mk_fst, PullbackCone.mk_snd] using ht =≫ P.map φ.op
        · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hp.isLimit _ _ fac.symm
          have ht : t.fst ≫ P.map sq.f₁₂.op = t.snd ≫ P.map sq.f₁₃.op := t.condition
          simpa only [Functor.map_comp, op_comp, Category.assoc, sq, Square.pullbackCone,
            PullbackCone.mk_fst, PullbackCone.mk_snd] using ht.symm =≫ P.map φ.op
        · obtain rfl : a = b := (cancel_mono sq.f₃₄).1 fac
          rfl)) (fun _ ↦ ?_) (fun _ ↦ ?_) (fun t m hm₁ hm₂ ↦ ?_)
  · exact hP.amalgamateOfArrows_map _ _ _ _ WalkingPair.left
  · exact hP.amalgamateOfArrows_map _ _ _ _ WalkingPair.right
  · apply hP.hom_ext_ofArrows _ hc
    rintro (_ | _)
    · rw [hP.amalgamateOfArrows_map _ _ _ _ WalkingPair.left]
      exact hm₁
    · rw [hP.amalgamateOfArrows_map _ _ _ _ WalkingPair.right]
      exact hm₂

private lemma openHom_subsingleton {T : Scheme.{u}} (U : T.Opens) (V : T.Etale) :
    Subsingleton (V ⟶ Scheme.Etale.mk U.ι) :=
  ⟨fun f g ↦ MorphismProperty.Over.Hom.ext ((cancel_mono U.ι).1
    ((MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm))⟩

attribute [local instance] openHom_subsingleton

private theorem injective_restriction_surjective (A : Type (u + 1)) [CommRing A]
    {T : Scheme.{u}} (U : T.Opens)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) [Injective M] :
    Function.Surjective (M.ΓRes (Opposite.op (Scheme.Etale.mk U.ι))) := by
  have := Sheaf.isSplitEpi_ΓRes_of_injective (Scheme.Etale.mk U.ι) M
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

private theorem supportedSection_exists (A : Type (u + 1)) [CommRing A]
    {T : Scheme.{u}} (W : T.Opens)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (x : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)
    (hx : M.ΓRes (Opposite.op (Scheme.Etale.mk W.ι)) x = 0) :
    ∃ y, (supportedEtaleSectionsι A T W).app M y = x := by
  let f := Sheaf.natTransΓRes T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (Opposite.op (Scheme.Etale.mk W.ι))
  let S := ShortComplex.mk ((supportedEtaleSectionsι A T W).app M) (f.app M)
    (NatTrans.congr_app (kernel.condition f) M)
  have he : S.Exact := ShortComplex.exact_of_f_is_kernel S
    (KernelFork.mapIsLimit _ (kernelIsKernel f)
      ((evaluation _ (ModuleCat.{u + 1} A)).obj M))
  exact S.moduleCat_exact_iff.1 he x hx

/-- Intersection of the two closed supports, as a closed immersion. -/
noncomputable def supportIntersection {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T) :
    pullback b c ⟶ T := pullback.fst b c ≫ b

/-- Closedness of the intersection follows by base change and composition. -/
@[instance]
theorem supportIntersection_closed {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    IsClosedImmersion (supportIntersection b c) := by
  dsimp [supportIntersection]
  infer_instance

/-- The support restricted to an actual open ambient scheme. -/
noncomputable def supportOnOpen {T B : Scheme.{u}} (b : B ⟶ T) (U : T.Opens) :
    pullback b U.ι ⟶ U := pullback.snd b U.ι

/-- Closed immersions remain closed after open base change. -/
@[instance]
theorem supportOnOpen_closed {T B : Scheme.{u}} (b : B ⟶ T) (U : T.Opens)
    [IsClosedImmersion b] : IsClosedImmersion (supportOnOpen b U) := by
  dsimp [supportOnOpen]
  infer_instance

private theorem supportIntersection_complement {T B C : Scheme.{u}}
    (b : B ⟶ T) (c : C ⟶ T) [IsClosedImmersion b] [IsClosedImmersion c] :
    (supportIntersection b c).openComplement = b.openComplement ⊔ c.openComplement := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_openComplement, supportIntersection,
    Scheme.Pullback.range_fst_comp, TopologicalSpace.Opens.coe_sup, Set.compl_inter]

/-- The complement of a support after open base change. -/
theorem supportOnOpen_complement {T B : Scheme.{u}} (b : B ⟶ T)
    [IsClosedImmersion b] (U : T.Opens) :
    (supportOnOpen b U).openComplement = U.ι ⁻¹ᵁ b.openComplement := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_openComplement, supportOnOpen,
    Scheme.Pullback.range_snd, Scheme.Hom.coe_preimage, Set.preimage_compl]

/-- Uniquely normalized inclusion of the intersection support kernel. -/
theorem exists_unique_supportInclusion (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    ∃! a : supportedEtaleSections A T (supportIntersection b c).openComplement ⟶
        supportedEtaleSections A T b.openComplement,
      a ≫ supportedEtaleSectionsι A T b.openComplement =
        supportedEtaleSectionsι A T (supportIntersection b c).openComplement := by
  rw [supportIntersection_complement]
  let f := Sheaf.natTransΓRes T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (Opposite.op (Scheme.Etale.mk b.openComplement.ι))
  have hz : supportedEtaleSectionsι A T (b.openComplement ⊔ c.openComplement) ≫ f = 0 := by
    apply NatTrans.ext
    funext M
    exact supportι_comp_ΓRes_of_le A T _ _ le_sup_left M
  refine ⟨kernel.lift f (supportedEtaleSectionsι A T
    (b.openComplement ⊔ c.openComplement)) hz, kernel.lift_ι _ _ _, ?_⟩
  intro a' ha'
  apply (cancel_mono (supportedEtaleSectionsι A T b.openComplement)).1
  rw [ha']
  exact (kernel.lift_ι _ _ _).symm

/-- Canonical support inclusion, selected by its unique kernel characterization. -/
noncomputable def supportInclusion (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    supportedEtaleSections A T (supportIntersection b c).openComplement ⟶
      supportedEtaleSections A T b.openComplement :=
  (exists_unique_supportInclusion A b c).choose

/-- Supported pullback along an open immersion, normalized on ordinary sections. -/
theorem exists_unique_supportTransport (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (_hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :
    ∃! r : supportedEtaleSections A T b.openComplement ⟶
        upperStar (ModuleCat.{u + 1} A) h ⋙ supportedEtaleSections A S d.openComplement,
      ∀ M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
        r.app M ≫ (supportedEtaleSectionsι A S d.openComplement).app
            ((upperStar (ModuleCat.{u + 1} A) h).obj M) =
          (supportedEtaleSectionsι A T b.openComplement).app M ≫
            globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h M := by
  let F := upperStar (ModuleCat.{u + 1} A) h
  let ι := supportedEtaleSectionsι A S d.openComplement
  let φ := h.resLE b.openComplement d.openComplement _hd.le
  have hφ : φ ≫ b.openComplement.ι = d.openComplement.ι ≫ h :=
    Scheme.Hom.resLE_comp_ι h _hd.le
  have hz (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      ((supportedEtaleSectionsι A T b.openComplement).app M ≫
        globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h M) ≫
        (F.obj M).ΓRes (Opposite.op (Scheme.Etale.mk d.openComplement.ι)) = 0 := by
    rw [Category.assoc, globalSectionsUpperStarMap_comp_ΓRes A h M
      (Scheme.Etale.mk b.openComplement.ι) (Scheme.Etale.mk d.openComplement.ι) φ hφ,
      ← Category.assoc, ← Category.assoc]
    have hk := NatTrans.congr_app (kernel.condition
      (Sheaf.natTransΓRes T.smallEtaleTopology (ModuleCat.{u + 1} A)
        (Opposite.op (Scheme.Etale.mk b.openComplement.ι)))) M
    change (supportedEtaleSectionsι A T b.openComplement).app M ≫
      M.ΓRes (Opposite.op (Scheme.Etale.mk b.openComplement.ι)) = 0 at hk
    rw [hk, zero_comp, zero_comp]
  let η : Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      F ⋙ Sheaf.Γ S.smallEtaleTopology (ModuleCat.{u + 1} A) := {
    app M := globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h M
    naturality M N f := globalSectionsUpperStarMap_naturality A h f }
  let f₂ := Sheaf.natTransΓRes S.smallEtaleTopology (ModuleCat.{u + 1} A)
    (Opposite.op (Scheme.Etale.mk d.openComplement.ι))
  let P := (Functor.whiskeringLeft
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) (ModuleCat.{u + 1} A)).obj F
  let k := supportedEtaleSectionsι A T b.openComplement ≫ η
  have hk : k ≫ P.map f₂ = 0 := NatTrans.ext (funext hz)
  let κ := KernelFork.mapIsLimit _ (kernelIsKernel f₂) P
  let r := κ.lift (KernelFork.ofι k hk)
  have hr : r ≫ Functor.whiskerLeft F ι = k := κ.fac _ WalkingParallelPair.zero
  refine ⟨r, fun M ↦ NatTrans.congr_app hr M, ?_⟩
  intro r' hr'
  apply NatTrans.ext
  funext M
  apply (cancel_mono (ι.app (F.obj M))).1
  exact (hr' M).trans (NatTrans.congr_app hr M).symm

/-- Canonical restriction on supported sections is uniquely fixed by restriction on
ordinary sections. -/
theorem exists_unique_supportOpenRestriction (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :
    ∃! r : supportedEtaleSections A T b.openComplement ⟶
        upperStar (ModuleCat.{u + 1} A) U.ι ⋙
          supportedEtaleSections A U (supportOnOpen b U).openComplement,
      ∀ M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
        r.app M ≫ (supportedEtaleSectionsι A U (supportOnOpen b U).openComplement).app
            ((upperStar (ModuleCat.{u + 1} A) U.ι).obj M) =
          (supportedEtaleSectionsι A T b.openComplement).app M ≫
            globalSectionsUpperStarMap (ModuleCat.{u + 1} A) U.ι M := by
  exact exists_unique_supportTransport A U.ι b (supportOnOpen b U)
    (supportOnOpen_complement b U)

/-- Restriction with support to an open ambient scheme. -/
noncomputable def supportOpenRestriction (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :
    supportedEtaleSections A T b.openComplement ⟶
      upperStar (ModuleCat.{u + 1} A) U.ι ⋙
        supportedEtaleSections A U (supportOnOpen b U).openComplement :=
  (exists_unique_supportOpenRestriction A b U).choose

/-- The composite of intersection inclusion and restriction to T minus C is zero. -/
theorem supportInclusion_restriction_zero (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    supportInclusion A b c ≫ supportOpenRestriction A b c.openComplement = 0 := by
  apply NatTrans.ext
  funext M
  let U := c.openComplement
  let N := (upperStar (ModuleCat.{u + 1} A) U.ι).obj M
  have : IsIso (N.ΓRes (Opposite.op (Scheme.Etale.mk (𝟙 (U : Scheme))) )) :=
    ΓRes_mkId_isIso A U N
  apply (cancel_mono ((supportedEtaleSectionsι A U (supportOnOpen b U).openComplement).app
    N)).1
  apply (cancel_mono (N.ΓRes (Opposite.op (Scheme.Etale.mk (𝟙 (U : Scheme)))))).1
  have hr := (exists_unique_supportOpenRestriction A b U).choose_spec.1 M
  change (supportOpenRestriction A b U).app M ≫
    (supportedEtaleSectionsι A U (supportOnOpen b U).openComplement).app N = _ at hr
  have ha := NatTrans.congr_app (exists_unique_supportInclusion A b c).choose_spec.1 M
  change (supportInclusion A b c).app M ≫
    (supportedEtaleSectionsι A T b.openComplement).app M = _ at ha
  simp only [NatTrans.comp_app, NatTrans.app_zero, zero_comp]
  rw [Category.assoc ((supportInclusion A b c).app M)
    ((supportOpenRestriction A b U).app M)
    ((supportedEtaleSectionsι A U (supportOnOpen b U).openComplement).app N), hr,
    ← Category.assoc ((supportInclusion A b c).app M), ha]
  rw [Category.assoc, globalSectionsUpperStarMap_comp_ΓRes A U.ι M
    (Scheme.Etale.mk U.ι) (Scheme.Etale.mk (𝟙 (U : Scheme))) (𝟙 (U : Scheme)) (by simp),
    ← Category.assoc, ← Category.assoc]
  have hk := supportι_comp_ΓRes_of_le A T (supportIntersection b c).openComplement U
    (by rw [supportIntersection_complement]; exact le_sup_right) M
  rw [hk]
  simp only [zero_comp]

/-- The ordinary support localization short complex of functors. -/
noncomputable def supportLocalizationSequence (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :=
  ShortComplex.mk (supportInclusion A b c) (supportOpenRestriction A b c.openComplement)
    (supportInclusion_restriction_zero A b c)

/-- Termwise localization of a complex of sheaves. -/
noncomputable def supportLocalizationComplex (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c]
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u + 1} A) ℤ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex (supportInclusion A b c) (.up ℤ)).app I)
    ((NatTrans.mapHomologicalComplex (supportOpenRestriction A b c.openComplement)
      (.up ℤ)).app I)
    (by
      ext n : 1
      exact NatTrans.congr_app (supportInclusion_restriction_zero A b c) (I.X n))

section

attribute [local irreducible] supportedEtaleSections supportedEtaleSectionsι upperStar

set_option backward.isDefEq.respectTransparency true in
private theorem supportLocalizationSequence_shortExact (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c]
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) [Injective M] :
    ((supportLocalizationSequence A b c).map
      ((evaluation _ (ModuleCat.{u + 1} A)).obj M)).ShortExact := by
  classical
  let U := c.openComplement
  let W := b.openComplement
  let K := (supportOnOpen b U).openComplement
  let N := (upperStar (ModuleCat.{u + 1} A) U.ι).obj M
  let VU := Scheme.Etale.mk U.ι
  let VI := Scheme.Etale.mk (U ⊓ W).ι
  let VK := Scheme.Etale.mk K.ι
  let V₀ := Scheme.Etale.mk (𝟙 (U : Scheme))
  let eI : K.toScheme ≅ (U ⊓ W).toScheme :=
    (U : Scheme).isoOfEq (supportOnOpen_complement b U) ≪≫
      U.ι.isoImage (U.ι ⁻¹ᵁ W) ≪≫ T.isoOfEq (by
        simp only [Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι])
  have heI : eI.hom ≫ (U ⊓ W).ι = K.ι ≫ U.ι := by
    simp only [eI, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
      Scheme.Hom.isoImage_hom_ι]
    rw [← Category.assoc, Scheme.isoOfEq_hom_ι]
  let qU : M.obj.obj (Opposite.op VU) ⟶ N.obj.obj (Opposite.op V₀) :=
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) U.ι).unit.app M).hom.app
      (Opposite.op VU) ≫ N.obj.map
        (homToPullback U.ι (V := V₀) (U := VU) (𝟙 (U : Scheme)) (by
          change (𝟙 (U : Scheme)) ≫ U.ι = (𝟙 (U : Scheme)) ≫ U.ι
          rfl)).op
  let qI : M.obj.obj (Opposite.op VI) ⟶ N.obj.obj (Opposite.op VK) :=
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) U.ι).unit.app M).hom.app
      (Opposite.op VI) ≫ N.obj.map
        (homToPullback U.ι (V := VK) (U := VI) eI.hom heI).op
  let : IsIso (𝟙 (U : Scheme)) := ⟨𝟙 _, Category.id_comp _, Category.comp_id _⟩
  have : IsIso qU := by
    set_option backward.isDefEq.respectTransparency false in
      exact sectionsUpperStarMap_isIso A U.ι M VU V₀ (𝟙 (U : Scheme)) (by
        change (𝟙 (U : Scheme)) ≫ U.ι = (𝟙 (U : Scheme)) ≫ U.ι
        rfl)
  have : IsIso qI := by
    set_option backward.isDefEq.respectTransparency false in
      exact sectionsUpperStarMap_isIso A U.ι M VI VK eI.hom heI
  have : IsIso (N.ΓRes (Opposite.op V₀)) := ΓRes_mkId_isIso A U N
  let m : VK ⟶ V₀ := MorphismProperty.Over.homMk K.ι (by
    change K.ι ≫ (𝟙 (U : Scheme)) = K.ι
    exact Category.comp_id _)
  let f : VI ⟶ VU := (openSquare U W).f₁₂
  have hcU : globalSectionsUpperStarMap (ModuleCat.{u + 1} A) U.ι M ≫
      N.ΓRes (Opposite.op V₀) = M.ΓRes (Opposite.op VU) ≫ qU :=
    globalSectionsUpperStarMap_comp_ΓRes A U.ι M VU V₀ (𝟙 (U : Scheme)) (by
      change (𝟙 (U : Scheme)) ≫ U.ι = (𝟙 (U : Scheme)) ≫ U.ι
      rfl)
  have hcI : globalSectionsUpperStarMap (ModuleCat.{u + 1} A) U.ι M ≫
      N.ΓRes (Opposite.op VK) = M.ΓRes (Opposite.op VI) ≫ qI :=
    globalSectionsUpperStarMap_comp_ΓRes A U.ι M VI VK eI.hom heI
  have : Epi (M.ΓRes (Opposite.op VU)) :=
    (ModuleCat.epi_iff_surjective _).2 (injective_restriction_surjective A U M)
  have hrel : M.obj.map f.op ≫ qI = qU ≫ N.obj.map m.op := by
    apply (cancel_epi (M.ΓRes (Opposite.op VU))).1
    rw [← Category.assoc, Sheaf.ΓRes_map]
    rw [← hcI, ← Category.assoc, ← hcU, Category.assoc, Sheaf.ΓRes_map]
  let j : (supportedEtaleSections A U K).obj N ⟶ M.obj.obj (Opposite.op VU) :=
    (supportedEtaleSectionsι A U K).app N ≫
    N.ΓRes (Opposite.op V₀) ≫ inv qU
  have : Mono j := inferInstance
  have hj : (supportOpenRestriction A b U).app M ≫ j =
      (supportedEtaleSectionsι A T W).app M ≫ M.ΓRes (Opposite.op VU) := by
    have hr := (exists_unique_supportOpenRestriction A b U).choose_spec.1 M
    change (supportOpenRestriction A b U).app M ≫
      (supportedEtaleSectionsι A U K).app N = _ at hr
    calc
      _ = ((supportOpenRestriction A b U).app M ≫
          (supportedEtaleSectionsι A U K).app N) ≫
            (N.ΓRes (Opposite.op V₀) ≫ inv qU) := (Category.assoc _ _ _).symm
      _ = ((supportedEtaleSectionsι A T W).app M ≫
          globalSectionsUpperStarMap (ModuleCat.{u + 1} A) U.ι M) ≫
            (N.ΓRes (Opposite.op V₀) ≫ inv qU) := congrArg (fun z ↦ z ≫ _) hr
      _ = (supportedEtaleSectionsι A T W).app M ≫
          ((globalSectionsUpperStarMap (ModuleCat.{u + 1} A) U.ι M ≫
            N.ΓRes (Opposite.op V₀)) ≫ inv qU) := by simp only [Category.assoc]
      _ = (supportedEtaleSectionsι A T W).app M ≫
          ((M.ΓRes (Opposite.op VU) ≫ qU) ≫ inv qU) := congrArg (fun z ↦
        (supportedEtaleSectionsι A T W).app M ≫ (z ≫ inv qU)) hcU
      _ = _ := by simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hj0 : j ≫ M.obj.map f.op = 0 := by
    apply (cancel_mono qI).1
    change ((supportedEtaleSectionsι A U K).app N ≫
      N.ΓRes (Opposite.op V₀) ≫ inv qU) ≫ M.obj.map f.op ≫ qI = _
    rw [Category.assoc, Category.assoc, hrel, ← Category.assoc (inv qU),
      IsIso.inv_hom_id, Category.id_comp, Sheaf.ΓRes_map]
    rw [zero_comp]
    exact supportι_comp_ΓRes_of_le A U K K le_rfl N
  let S := (supportLocalizationSequence A b c).map
    ((evaluation _ (ModuleCat.{u + 1} A)).obj M)
  have ha : (supportInclusion A b c).app M ≫
      (supportedEtaleSectionsι A T W).app M =
      (supportedEtaleSectionsι A T (supportIntersection b c).openComplement).app M :=
    NatTrans.congr_app (exists_unique_supportInclusion A b c).choose_spec.1 M
  have : Mono S.f := by
    change Mono ((supportInclusion A b c).app M)
    have : Mono ((supportInclusion A b c).app M ≫
        (supportedEtaleSectionsι A T W).app M) := by rw [ha]; infer_instance
    exact mono_of_mono _ ((supportedEtaleSectionsι A T W).app M)
  have hp := openSquare_sections A U W M
  have hW (x : (supportedEtaleSections A T W).obj M) :
      M.ΓRes (Opposite.op (Scheme.Etale.mk W.ι))
        ((supportedEtaleSectionsι A T W).app M x) = 0 := by
    simpa using ConcreteCategory.congr_hom
      (supportι_comp_ΓRes_of_le A T W W le_rfl M) x
  have he : S.Exact := by
    apply S.moduleCat_exact_iff.2
    intro x hx
    let t := (supportedEtaleSectionsι A T W).app M x
    have hU : M.ΓRes (Opposite.op VU) t = 0 := by
      change (supportOpenRestriction A b U).app M x =
        (0 : (supportedEtaleSections A U K).obj N) at hx
      have h := ConcreteCategory.congr_hom hj x
      change j ((supportOpenRestriction A b U).app M x) =
        M.ΓRes (Opposite.op VU) t at h
      rw [hx, map_zero] at h
      exact h.symm
    have hO : M.ΓRes (Opposite.op (Scheme.Etale.mk (U ⊔ W).ι)) t = 0 := by
      apply (PullbackCone.IsLimit.equivPullbackObj hp.isLimit).injective
      apply Subtype.ext
      apply Prod.ext
      · change M.obj.map (openSquare U W).f₂₄.op
          (M.ΓRes (Opposite.op (Scheme.Etale.mk (U ⊔ W).ι)) t) =
            M.obj.map (openSquare U W).f₂₄.op 0
        calc
          _ = M.ΓRes (Opposite.op VU) t :=
            ConcreteCategory.congr_hom (Sheaf.ΓRes_map M (openSquare U W).f₂₄.op) t
          _ = _ := by
            rw [hU, map_zero]
            rfl
      · change M.obj.map (openSquare U W).f₃₄.op
          (M.ΓRes (Opposite.op (Scheme.Etale.mk (U ⊔ W).ι)) t) =
            M.obj.map (openSquare U W).f₃₄.op 0
        calc
          _ = M.ΓRes (Opposite.op (Scheme.Etale.mk W.ι)) t :=
            ConcreteCategory.congr_hom (Sheaf.ΓRes_map M (openSquare U W).f₃₄.op) t
          _ = _ := by
            rw [hW x, map_zero]
            rfl
    have hBC : M.ΓRes (Opposite.op
        (Scheme.Etale.mk (supportIntersection b c).openComplement.ι)) t = 0 := by
      rw [supportIntersection_complement]
      rw [sup_comm U W] at hO
      exact hO
    obtain ⟨y, hy⟩ := supportedSection_exists A (supportIntersection b c).openComplement M t hBC
    refine ⟨y, ?_⟩
    apply (ModuleCat.mono_iff_injective ((supportedEtaleSectionsι A T W).app M)).1
      inferInstance
    exact (ConcreteCategory.congr_hom ha y).trans hy
  refine ShortComplex.ShortExact.mk' he inferInstance ?_
  apply (ModuleCat.epi_iff_surjective S.g).2
  intro y
  have hy0 : M.obj.map f.op (j y) = 0 := by
    exact ConcreteCategory.congr_hom hj0 y
  let z : M.obj.obj (Opposite.op (Scheme.Etale.mk (U ⊔ W).ι)) :=
    (PullbackCone.IsLimit.equivPullbackObj hp.isLimit).symm
      ⟨⟨j y, (0 : M.obj.obj (Opposite.op (Scheme.Etale.mk W.ι)))⟩,
        by
          change M.obj.map f.op (j y) = M.obj.map (openSquare U W).f₁₃.op 0
          rw [map_zero]
          exact hy0⟩
  have hzU : M.obj.map (openSquare U W).f₂₄.op z = j y :=
    PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst hp.isLimit _
  have hzW : M.obj.map (openSquare U W).f₃₄.op z = 0 :=
    PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd hp.isLimit _
  obtain ⟨t, ht⟩ := injective_restriction_surjective A (U ⊔ W) M z
  have htW : M.ΓRes (Opposite.op (Scheme.Etale.mk W.ι)) t = 0 := by
    calc
      _ = M.obj.map (openSquare U W).f₃₄.op
          (M.ΓRes (Opposite.op (Scheme.Etale.mk (U ⊔ W).ι)) t) :=
        (ConcreteCategory.congr_hom (Sheaf.ΓRes_map M (openSquare U W).f₃₄.op) t).symm
      _ = 0 := by rw [ht, hzW]
  obtain ⟨x, hx⟩ := supportedSection_exists A W M t htW
  refine ⟨x, ?_⟩
  apply (ModuleCat.mono_iff_injective j).1 inferInstance
  calc
    j (S.g x) = M.ΓRes (Opposite.op VU)
        ((supportedEtaleSectionsι A T W).app M x) := ConcreteCategory.congr_hom hj x
    _ = j y := by
      rw [hx]
      exact (ConcreteCategory.congr_hom
        (Sheaf.ΓRes_map M (openSquare U W).f₂₄.op) t).symm.trans
          ((congrArg (M.obj.map (openSquare U W).f₂₄.op) ht).trans hzU)

end

/-- Injective sheaves give a short exact sequence of supported section complexes. -/
theorem supportLocalizationComplex_shortExact (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c]
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [∀ n : ℤ, Injective (I.X n)] : (supportLocalizationComplex A b c I).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact supportLocalizationSequence_shortExact A b c (I.X n)

/-- The derived functor of the third ordinary support functor before the canonical
open-restriction comparison. -/
noncomputable abbrev supportOpenComposite (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :=
  upperStar (ModuleCat.{u + 1} A) U.ι ⋙
    supportedEtaleSections A U (supportOnOpen b U).openComplement

/-- The canonical boundary, normalized on every termwise injective K-injective complex. -/
theorem exists_unique_supportLocalizationBoundary (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    ∃! δ : (supportOpenComposite A b c.openComplement).rightDerivedFunctor ⟶
        (supportedEtaleSections A T (supportIntersection b c).openComplement).rightDerivedFunctor
          ⋙ shiftFunctor (DerivedCategory (ModuleCat.{u + 1} A)) (1 : ℤ),
      ∀ (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)],
        δ.app (DerivedCategory.Q.obj I) ≫
            ((supportedEtaleSections A T (supportIntersection b
              c).openComplement).rightDerivedFunctorObjQIso I).hom⟦1⟧' =
          ((supportOpenComposite A b c.openComplement).rightDerivedFunctorObjQIso I).hom ≫
            DerivedCategory.triangleOfSESδ (supportLocalizationComplex_shortExact A b c I) := by
  let S := supportLocalizationSequence A b c
  have hS : S.ShortExactOnInjectives := by
    intro J _
    let I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ := {
      X _ := J
      d _ _ := 0 }
    let : ∀ n : ℤ, Injective (I.X n) := fun _ ↦ inferInstance
    exact (supportLocalizationComplex_shortExact A b c I).map_of_exact
      (HomologicalComplex.eval _ (.up ℤ) 0)
  let : S.X₁.Additive := inferInstanceAs
    (supportedEtaleSections A T (supportIntersection b c).openComplement).Additive
  let : S.X₂.Additive := inferInstanceAs
    (supportedEtaleSections A T b.openComplement).Additive
  let : S.X₃.Additive := inferInstanceAs (supportOpenComposite A b c.openComplement).Additive
  exact ShortComplex.exists_unique_unboundedDerivedBoundary S hS

/-- The normalized connecting map, with no arbitrary triangle completion. -/
noncomputable def supportLocalizationBoundary (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    (supportOpenComposite A b c.openComplement).rightDerivedFunctor ⟶
      (supportedEtaleSections A T (supportIntersection b c).openComplement).rightDerivedFunctor ⋙
        shiftFunctor (DerivedCategory (ModuleCat.{u + 1} A)) (1 : ℤ) :=
  (exists_unique_supportLocalizationBoundary A b c).choose

/-- Canonical derived-composite comparison for an open immersion. -/
theorem exists_unique_supportTransportComparison (A : Type (u + 1)) [CommRing A]
    {T S D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (d : D ⟶ S) [IsClosedImmersion d] :
    ∃! e : (upperStar (ModuleCat.{u + 1} A) h ⋙
        supportedEtaleSections A S d.openComplement).rightDerivedFunctor ≅
        (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory ⋙ supportedSectionsDerived A d,
      (upperStar (ModuleCat.{u + 1} A) h ⋙
          supportedEtaleSections A S d.openComplement).rightDerivedFunctorUnit ≫
          Functor.whiskerLeft DerivedCategory.Qh e.hom =
        Functor.rightDerivedFunctorCompUnit (upperStar (ModuleCat.{u + 1} A) h)
            (supportedEtaleSections A S d.openComplement) ≫
          Functor.whiskerLeft DerivedCategory.Qh (Functor.whiskerRight
            (upperStar (ModuleCat.{u + 1} A) h).rightDerivedFunctorIsoMapDerivedCategory.hom
            (supportedSectionsDerived A d)) := by
  let F := upperStar (ModuleCat.{u + 1} A) h
  let G := supportedEtaleSections A S d.openComplement
  let : F.PreservesKInjectiveComplexes :=
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) h
      inferInstance).preservesKInjectiveComplexes
  let e := Functor.rightDerivedFunctorCompIso F G ≪≫
    Functor.isoWhiskerRight F.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor
  have hc : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorCompIso F G).hom =
        Functor.rightDerivedFunctorCompUnit F G := by
    simp [Functor.rightDerivedFunctorCompIso]
  have he : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh e.hom =
        Functor.rightDerivedFunctorCompUnit F G ≫ Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerRight F.rightDerivedFunctorIsoMapDerivedCategory.hom
            G.rightDerivedFunctor) := by
    change (F ⋙ G).rightDerivedFunctorUnit ≫
      (Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorCompIso F G).hom ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerRight F.rightDerivedFunctorIsoMapDerivedCategory.hom
            G.rightDerivedFunctor)) = _
    rw [← Category.assoc, hc]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Functor.rightDerived_ext (F ⋙ G).rightDerivedFunctor
    (F ⋙ G).rightDerivedFunctorUnit (HomotopyCategory.quasiIso _ (.up ℤ))
  exact he'.trans he.symm

/-- Canonical comparison for restriction to an open before taking supported sections. -/
theorem exists_unique_supportOpenDerivedComparison (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :
    ∃! e : (supportOpenComposite A b U).rightDerivedFunctor ≅
        (upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategory ⋙
          supportedSectionsDerived A (supportOnOpen b U),
      (supportOpenComposite A b U).rightDerivedFunctorUnit ≫
          Functor.whiskerLeft DerivedCategory.Qh e.hom =
        Functor.rightDerivedFunctorCompUnit (upperStar (ModuleCat.{u + 1} A) U.ι)
            (supportedEtaleSections A U (supportOnOpen b U).openComplement) ≫
          Functor.whiskerLeft DerivedCategory.Qh
            (Functor.whiskerRight
              ((upperStar (ModuleCat.{u + 1} A) U.ι).rightDerivedFunctorIsoMapDerivedCategory).hom
              (supportedSectionsDerived A (supportOnOpen b U))) := by
  exact exists_unique_supportTransportComparison A U.ι (supportOnOpen b U)

/-- The uniquely normalized derived open comparison. -/
noncomputable def supportOpenDerivedComparison (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :
    (supportOpenComposite A b U).rightDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategory ⋙
        supportedSectionsDerived A (supportOnOpen b U) :=
  (exists_unique_supportOpenDerivedComparison A b U).choose

/-- The derived restriction arrow, with the third term on the open ambient scheme. -/
noncomputable def derivedSupportOpenRestriction (A : Type (u + 1)) [CommRing A]
    {T B : Scheme.{u}} (b : B ⟶ T) [IsClosedImmersion b] (U : T.Opens) :=
  Functor.rightDerivedFunctorNatTrans (supportOpenRestriction A b U) ≫
    (supportOpenDerivedComparison A b U).hom

/-- Localization triangle with the actual support inclusion, restriction, and boundary. -/
noncomputable def normalizedSupportTriangle (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c]
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    Triangle (DerivedCategory (ModuleCat.{u + 1} A)) :=
  Triangle.mk ((Functor.rightDerivedFunctorNatTrans (supportInclusion A b c)).app K)
    ((derivedSupportOpenRestriction A b c.openComplement).app K)
    ((supportOpenDerivedComparison A b c.openComplement).inv.app K ≫
      (supportLocalizationBoundary A b c).app K)

/-- The uniquely normalized ordinary supported transport. -/
noncomputable def supportTransport (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :
    supportedEtaleSections A T b.openComplement ⟶
      upperStar (ModuleCat.{u + 1} A) h ⋙ supportedEtaleSections A S d.openComplement :=
  (exists_unique_supportTransport A h b d hd).choose

/-- The normalized derived-composite comparison for an open immersion. -/
noncomputable def supportTransportComparison (A : Type (u + 1)) [CommRing A]
    {T S D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (d : D ⟶ S) [IsClosedImmersion d] :
    (upperStar (ModuleCat.{u + 1} A) h ⋙
      supportedEtaleSections A S d.openComplement).rightDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory ⋙ supportedSectionsDerived A d :=
  (exists_unique_supportTransportComparison A h d).choose

/-- The actual derived restriction with closed support, to an arbitrary open immersion. -/
noncomputable def derivedSupportTransport (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :=
  Functor.rightDerivedFunctorNatTrans (supportTransport A h b d hd) ≫
    (supportTransportComparison A h d).hom

/-- Change of ambient scheme by an isomorphism is an isomorphism on derived supports. -/
@[instance]
theorem derivedSupportTransport_isIso (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsIso h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :
    IsIso (derivedSupportTransport A h b d hd) := by
  have hM (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      IsIso ((supportTransport A h b d hd).app M) := by
    let N := (upperStar (ModuleCat.{u + 1} A) h).obj M
    let φ := h.resLE b.openComplement d.openComplement hd.le
    have hφ : φ ≫ b.openComplement.ι = d.openComplement.ι ≫ h :=
      Scheme.Hom.resLE_comp_ι h hd.le
    have hp : IsPullback φ d.openComplement.ι b.openComplement.ι h :=
      IsOpenImmersion.isPullback _ _ _ _ hφ.symm (by simpa using hd.symm)
    have : IsIso φ := hp.isIso_fst_of_isIso
    let q := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
        (Opposite.op (Scheme.Etale.mk b.openComplement.ι)) ≫
      N.obj.map (homToPullback h
        (V := Scheme.Etale.mk d.openComplement.ι)
        (U := Scheme.Etale.mk b.openComplement.ι) φ hφ).op
    have : IsIso q := sectionsUpperStarMap_isIso A h M
      (Scheme.Etale.mk b.openComplement.ι) (Scheme.Etale.mk d.openComplement.ι) φ hφ
    let f₁ := Sheaf.natTransΓRes T.smallEtaleTopology (ModuleCat.{u + 1} A)
      (Opposite.op (Scheme.Etale.mk b.openComplement.ι))
    let f₂ := Sheaf.natTransΓRes S.smallEtaleTopology (ModuleCat.{u + 1} A)
      (Opposite.op (Scheme.Etale.mk d.openComplement.ι))
    exact isIso_of_kernel_square (f₁.app M) (f₂.app N)
      ((supportedEtaleSectionsι A T b.openComplement).app M)
      ((supportedEtaleSectionsι A S d.openComplement).app N)
      (NatTrans.congr_app (kernel.condition f₁) M)
      (NatTrans.congr_app (kernel.condition f₂) N)
      (KernelFork.mapIsLimit _ (kernelIsKernel f₁)
        ((evaluation _ (ModuleCat.{u + 1} A)).obj M))
      (KernelFork.mapIsLimit _ (kernelIsKernel f₂)
        ((evaluation _ (ModuleCat.{u + 1} A)).obj N))
      ((supportTransport A h b d hd).app M)
      (globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h M) q
      (globalSectionsUpperStarMap_comp_ΓRes A h M
        (Scheme.Etale.mk b.openComplement.ι)
        (Scheme.Etale.mk d.openComplement.ι) φ hφ).symm
      ((exists_unique_supportTransport A h b d hd).choose_spec.1 M)
  have : IsIso (supportTransport A h b d hd) := NatIso.isIso_of_isIso_app _
  change IsIso (Functor.rightDerivedFunctorNatTrans (supportTransport A h b d hd) ≫
    (supportTransportComparison A h d).hom)
  infer_instance

end AlgebraicGeometry.Etale
