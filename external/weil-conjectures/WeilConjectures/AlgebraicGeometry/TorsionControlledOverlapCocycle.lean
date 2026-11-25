/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.TorsionCommonOpenComparisonMap
import WeilConjectures.AlgebraicGeometry.TorsionLocalSectionSeparation
import WeilConjectures.AlgebraicGeometry.CoherentMapTorsionCompletionExt
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.TorsionControlledCompletionHomLiftExists
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Torsion-controlled local descent data

Source: Stacks Project, Tag 0889(1), Zariski locality by uniqueness;
Sheaves, Tags 00AL and 00AM.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The fixed local sources and normalized quotient maps admit compatible overlap isomorphisms.
All local objects and maps are supplied; only pairwise comparisons and their cocycle are built.

Source: Stacks Project, Tag 0889(1), uniqueness verification omitted at the end of the proof;
Sheaves, Tags 00AL and 00AM.
(blueprint: new-stage3-torsion-controlled-overlap-cocycle).

Proof: On every common open obtain a map respecting the supplied b and q maps.
No isomorphism or cocycle is assumed at this step. The Artin--Rees separation
argument shows that b and all q maps jointly separate local sections. Evaluate a
forward map followed by the reverse map on any contained open: its b and q images
agree with the identity by the two compatibility equations. Section separation
and sheaf morphism extensionality identify the composite with the identity.
Package the two maps on Ui intersect Uj into theta_ij. On every common open of
three charts, the direct map and the two-map composite have identical b and q
images, again by compatibility. Section separation on chart k proves equality,
and ModuleCat extensionality gives the cocycle. The b and q clauses are exactly
the original common-open map equations. Intersections need not be affine. The
unit ideal is handled by the map to H, the zero ideal by the quotient maps,
and the empty index type or empty scheme causes no additional condition.
-/
theorem torsionControlled_overlap_cocycle
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (ι : Type u) (U : ι → X.Opens)
    (Hlocal : ∀ i, CoherentModules (U i).toScheme)
    (hHlocal : ∀ i, (Hlocal i).obj = (Scheme.Modules.restrictFunctor (U i).ι).obj H.obj)
    (Fi : ∀ i, CoherentModules (U i).toScheme)
    (ai : ∀ i, Fi i ⟶ Hlocal i)
    (βi : ∀ i, N.obj ⋙ Scheme.Modules.restrictFunctor (U i).ι ≅
      formalCompletionSystem (J.comap (U i).ι) (Fi i).obj)
    (hbound : ∀ i, ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (kernel (ai i).hom)) ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (cokernel (ai i).hom)))
    (Li : ∀ i, SheafOfModules ((moduleRings X.toRingedSpace).over (U i)))
    (li : ∀ i, (Scheme.Modules.overEquiv (U i)).functor.obj (Li i) ≅ (Fi i).obj)
    (bi : ∀ i, Li i ⟶ H.obj.over (U i))
    (qi : ∀ (i : ι) (n : ℕᵒᵖ), Li i ⟶ (N.obj.obj n).over (U i))
    (hbi : (∀ i, (Scheme.Modules.overEquiv (U i)).functor.map (bi i) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app H.obj ≫
          eqToHom (hHlocal i).symm = (li i).hom ≫ (ai i).hom))
    (hqi : (∀ (i : ι) (n : ℕᵒᵖ), (Scheme.Modules.overEquiv (U i)).functor.map (qi i n) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app (N.obj.obj n) =
          (li i).hom ≫ formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Fi i).obj ≫
            (βi i).inv.app n))
    (hδ : (∀ (i : ι) (n : ℕᵒᵖ), qi i n ≫ (δ.hom.app n).over (U i) =
        bi i ≫ (formalModuleQuotientπ J (n.unop + 1) H.obj).over (U i)))
 :
    ∃ (θ : ∀ i j,
      (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Li i) ≅
      (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Li j)),
      (∀ (i j k : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
        (θ i k).hom.val.app (op (Over.mk (homOfLE (le_inf hi hk)))) =
          (θ i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
            (θ j k).hom.val.app (op (Over.mk (homOfLE (le_inf hj hk))))) ∧
      (∀ (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
        (θ i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
          (bi j).val.app (op (Over.mk (homOfLE hj))) =
            (bi i).val.app (op (Over.mk (homOfLE hi)))) ∧
      (∀ (n : ℕᵒᵖ) (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
        (θ i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
          (qi j n).val.app (op (Over.mk (homOfLE hj))) =
            (qi i n).val.app (op (Over.mk (homOfLE hi)))) := by
  classical
  have sep := torsion_local_section_separation J H N ι U Hlocal hHlocal Fi ai βi
    hbound Li li bi qi hbi hqi
  have maps := torsion_common_open_comparison_map J H N δ ι U Hlocal hHlocal Fi ai
    βi hbound Li li bi qi hbi hqi hδ
  choose f hb hq using maps
  have inverse (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
      f i j W hi hj ≫ f j i W hj hi = 𝟙 _ := by
    apply SheafOfModules.hom_ext
    ext V x
    rcases V with ⟨⟨V, ⟨⟨⟩⟩, a⟩⟩
    let hV : V ≤ W := leOfHom a
    apply sep i V (hV.trans hi)
    · have h₁ := congrArg (fun g => g x) (hb i j W hi hj V hV)
      have h₂ := congrArg (fun g => g ((f i j W hi hj).val.app
        (op (Over.mk (homOfLE hV))) x)) (hb j i W hj hi V hV)
      exact h₂.trans h₁
    · intro n
      have h₁ := congrArg (fun g => g x) (hq i j W hi hj n V hV)
      have h₂ := congrArg (fun g => g ((f i j W hi hj).val.app
        (op (Over.mk (homOfLE hV))) x)) (hq j i W hj hi n V hV)
      exact h₂.trans h₁
  let θ (i j : ι) :=
    (⟨f i j (U i ⊓ U j) inf_le_left inf_le_right,
      f j i (U i ⊓ U j) inf_le_right inf_le_left,
      inverse i j _ _ _, inverse j i _ _ _⟩ :
      (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Li i) ≅
      (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Li j))
  refine ⟨θ, ?_, ?_, ?_⟩
  · intro i j k W hi hj hk
    ext x
    apply sep k W hk
    · have h₁ := congrArg (fun g => g x)
        (hb i k (U i ⊓ U k) inf_le_left inf_le_right W (le_inf hi hk))
      have h₂ := congrArg (fun g => g x)
        (hb i j (U i ⊓ U j) inf_le_left inf_le_right W (le_inf hi hj))
      have h₃ := congrArg (fun g => g ((θ i j).hom.val.app
        (op (Over.mk (homOfLE (le_inf hi hj)))) x))
        (hb j k (U j ⊓ U k) inf_le_left inf_le_right W (le_inf hj hk))
      exact h₁.trans (h₃.trans h₂).symm
    · intro n
      have h₁ := congrArg (fun g => g x)
        (hq i k (U i ⊓ U k) inf_le_left inf_le_right n W (le_inf hi hk))
      have h₂ := congrArg (fun g => g x)
        (hq i j (U i ⊓ U j) inf_le_left inf_le_right n W (le_inf hi hj))
      have h₃ := congrArg (fun g => g ((θ i j).hom.val.app
        (op (Over.mk (homOfLE (le_inf hi hj)))) x))
        (hq j k (U j ⊓ U k) inf_le_left inf_le_right n W (le_inf hj hk))
      exact h₁.trans (h₃.trans h₂).symm
  · intro i j W hi hj
    exact hb i j (U i ⊓ U j) inf_le_left inf_le_right W (le_inf hi hj)
  · intro n i j W hi hj
    exact hq i j (U i ⊓ U j) inf_le_left inf_le_right n W (le_inf hi hj)

end AlgebraicGeometry
