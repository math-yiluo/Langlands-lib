/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundary
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Reduction of the supported integral constant

The integral generator is the actual quotient projection, including its value on one.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private def quotientCast (n : ℕ) :
    AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶
      AddCommGrpCat.of (ULift.{u + 1} (ZMod n)) :=
  AddCommGrpCat.ofHom
    ((AddEquiv.ulift : ULift.{u + 1} (ZMod n) ≃+ ZMod n).symm.toAddMonoidHom.comp
      ((Int.castAddHom (ZMod n)).comp
        (AddEquiv.ulift : ULift.{u + 1} ℤ ≃+ ℤ).toAddMonoidHom))

private theorem quotientCast_condition (n : ℕ) :
    (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ quotientCast n = 0 := by
  ext x
  simp [quotientCast, AddEquiv.ulift]

private theorem quotientCast_shortExact (n : ℕ) (hn : 0 < n) :
    (ShortComplex.mk (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      (quotientCast n) (quotientCast_condition n)).ShortExact := by
  have hf : Function.Injective (fun x : ULift.{u + 1} ℤ ↦ n • x) := by
    intro x y h
    apply ULift.ext
    have h' : (n : ℤ) * x.down = (n : ℤ) * y.down := by
      simpa [map_nsmul, Int.nsmul_eq_mul, AddEquiv.ulift] using
        congrArg (AddEquiv.ulift : ULift.{u + 1} ℤ ≃+ ℤ) h
    exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn)) h'
  have hg : Function.Surjective (quotientCast.{u} n) := by
    intro x
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective x.down
    exact ⟨ULift.up z, by simpa [quotientCast, AddEquiv.ulift] using congrArg ULift.up hz⟩
  refine { mono_f := (AddCommGrpCat.mono_iff_injective _).2 hf
           epi_g := (AddCommGrpCat.epi_iff_surjective _).2 hg
           exact := ?_ }
  rw [ShortComplex.ab_exact_iff_function_exact]
  intro x
  constructor
  · intro hx
    have hx' : (x.down : ZMod n) = 0 := by
      simpa [quotientCast, AddEquiv.ulift] using congrArg ULift.down hx
    obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x.down n).1 hx'
    refine ⟨ULift.up z, ?_⟩
    apply ULift.ext
    simpa [Int.nsmul_eq_mul] using hz.symm
  · rintro ⟨y, rfl⟩
    simp [quotientCast, AddEquiv.ulift]
    rfl

private def constantResidueForgetIso (T : Scheme.{u}) (n : ℕ) :
    (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ≅
      (moduleAbelianForget (ULift.{u + 1} (ZMod n)) T).obj
        (ordinaryFiniteConstant (ULift.{u + 1} (ZMod n)) T) := by
  let R := ULift.{u + 1} (ZMod n)
  let U := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let f := Int.castRingHom R
  have : (ModuleCat.restrictScalars.{u + 1} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} f).isLeftAdjoint
  have : U.IsLeftAdjoint := inferInstanceAs
    (ModuleCat.restrictScalars.{u + 1} f ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  let P := (Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of R R)
  let e := sheafifyComposeIso T.smallEtaleTopology U P
  exact { hom := ⟨e.hom⟩
          inv := ⟨e.inv⟩
          hom_inv_id := by ext : 1; exact e.hom_inv_id
          inv_hom_id := by ext : 1; exact e.inv_hom_id }

private theorem ordinaryFiniteIntegralGenerator_residue (T : Scheme.{u}) (n : ℕ) :
    ordinaryFiniteIntegralGenerator (ULift.{u + 1} (ZMod n)) T =
      (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).map (quotientCast n) ≫
        (constantResidueForgetIso T n).hom := by
  apply ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).homEquiv _ _).injective
  rw [ordinaryFiniteIntegralGenerator]
  erw [Equiv.apply_symm_apply]
  rw [constantSheafAdj_homEquiv_apply]
  let R := ULift.{u + 1} (ZMod n)
  let J := T.smallEtaleTopology
  let U := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let P := (Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of R R)
  let t := op (Scheme.Etale.mk (𝟙 T))
  let f := Int.castRingHom R
  have : (ModuleCat.restrictScalars.{u + 1} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} f).isLeftAdjoint
  have : U.IsLeftAdjoint := inferInstanceAs
    (ModuleCat.restrictScalars.{u + 1} f ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  have hz : (toSheafify J ((Functor.const T.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app t ≫
      ((constantSheaf J AddCommGrpCat.{u + 1}).map (quotientCast n)).hom.app t =
        quotientCast n ≫ (toSheafify J ((Functor.const T.Etaleᵒᵖ).obj
          (AddCommGrpCat.of R))).app t := by
    exact (congr_app (toSheafify_naturality J
      ((Functor.const T.Etaleᵒᵖ).map (quotientCast n))) t).symm
  have hc : (toSheafify J ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of R))).app t ≫
      (constantResidueForgetIso T n).hom.hom.app t = U.map ((toSheafify J P).app t) := by
    change (toSheafify J (P ⋙ U)).app t ≫
      (sheafifyComposeIso J U P).hom.app t = _
    exact congr_app (sheafComposeIso_hom_fac J U P) t
  change _ = (toSheafify J ((Functor.const T.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app t ≫
    (((constantSheaf J AddCommGrpCat.{u + 1}).map (quotientCast n)).hom.app t ≫
      (constantResidueForgetIso T n).hom.hom.app t)
  rw [← Category.assoc, hz, Category.assoc, hc]
  have hcast : quotientCast n = AddCommGrpCat.ofHom
      ((Int.castAddHom R).comp
        (AddEquiv.ulift : ULift.{u + 1} ℤ ≃+ ℤ).toAddMonoidHom) := by
    ext x
    simp [quotientCast, AddEquiv.ulift]
    rfl
  rw [hcast]
  rfl

private theorem ordinaryIntegralResidueSequence (T : Scheme.{u}) (n : ℕ) (hn : 0 < n) :
    ∃ w : (n • 𝟙 ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≫
      ordinaryFiniteIntegralGenerator (ULift.{u + 1} (ZMod n)) T = 0,
      (ShortComplex.mk _ _ w).ShortExact := by
  let F := constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}
  let γ := ordinaryFiniteIntegralGenerator (ULift.{u + 1} (ZMod n)) T
  have hw : (n • 𝟙 (F.obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≫ γ = 0 := by
    dsimp only [γ]
    rw [ordinaryFiniteIntegralGenerator_residue]
    rw [← F.map_id, ← F.map_nsmul, ← Category.assoc, ← F.map_comp,
      quotientCast_condition, F.map_zero, zero_comp]
  refine ⟨hw, ?_⟩
  let e : (ShortComplex.mk _ _ (quotientCast_condition n)).map F ≅
      ShortComplex.mk _ γ hw := by
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (constantResidueForgetIso T n) ?_ ?_
    · change (𝟙 _) ≫ (n • 𝟙 _) = F.map (n • 𝟙 _) ≫ (𝟙 _)
      simp only [F.map_nsmul, F.map_id, Category.id_comp, Category.comp_id]
    · change (𝟙 _) ≫ γ = F.map (quotientCast n) ≫ (constantResidueForgetIso T n).hom
      simpa only [Category.id_comp] using ordinaryFiniteIntegralGenerator_residue T n
  exact ShortComplex.shortExact_of_iso e ((quotientCast_shortExact n hn).map_of_exact F)

/-- For a closed immersion i:D→T of schemes and n>0, the maps n:i_*Z_D→i_*Z_D and the normalized
integral generator i_*Z_D→forget(i_*(ULift(Z/n))_D) form a short exact sequence of abelian etale
sheaves [def-weil-pbc-direct-image, def-asd-ordinary-finite-p1-kummer-class].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (auxiliary; not a blueprint node).
Proof: The constant integer-to-residue sequence is exact: sheafification is exact and the elementary
integer sequence has kernel nZ. A closed immersion is finite, so its etale direct image is exact.
Apply this direct image to the constant sequence. The constant-sections adjunction identifies its
quotient map with the published integral generator. Positivity ensures multiplication by n is monic,
including n=1. -/
theorem supported_integral_residue_sequence {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (n : ℕ) (hn : 0 < n) :
    ∃ w : (n • 𝟙 ((lowerStar AddCommGrpCat.{u + 1} i).obj
        (supportedIntegralConstant D))) ≫
      supportedIntegralGenerator (ULift.{u + 1} (ZMod n)) i = 0,
      (ShortComplex.mk _ _ w).ShortExact := by
  obtain ⟨w, hw⟩ := ordinaryIntegralResidueSequence D n hn
  let F := lowerStar AddCommGrpCat.{u + 1} i
  have hmap : F.map (n • 𝟙 (supportedIntegralConstant D)) =
      n • 𝟙 (F.obj (supportedIntegralConstant D)) := by
    rw [F.map_nsmul, F.map_id]
  have wt : (n • 𝟙 (F.obj (supportedIntegralConstant D))) ≫
      supportedIntegralGenerator (ULift.{u + 1} (ZMod n)) i = 0 := by
    rw [supportedIntegralGenerator, ← hmap, ← F.map_comp, w, F.map_zero]
  refine ⟨wt, ?_⟩
  let e : (ShortComplex.mk _ _ w).map F ≅ ShortComplex.mk _ _ wt := by
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · change (𝟙 _) ≫ _ = F.map _ ≫ (𝟙 _)
      simpa only [Category.id_comp, Category.comp_id] using hmap.symm
    · change (𝟙 _) ≫ _ = F.map _ ≫ (𝟙 _)
      rfl
  exact ShortComplex.shortExact_of_iso e (hw.map_of_exact F)

end AlgebraicGeometry.Etale
