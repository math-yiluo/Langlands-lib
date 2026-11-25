/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.GeneratingSectionsStalkSpan
import WeilConjectures.AlgebraicGeometry.InvertibleStalkLinearEquiv
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus

/-!
# Morphisms into projective space from generating sections

The integral projective space used by the functor-of-points declaration is the base change
of the raw integral Proj to `Spec ℤ`. Its second projection identifies it with that Proj.
Thus the second component of the defining pairing below is `ψ ≫ toProjInt`.

## References

* Stacks Project, Constructions, Lemma 01NE, Definition 01NF and its following paragraph
* Stacks Project, Constructions, Lemma 01NE
* Stacks Project, Constructions, Definition 01NF, paragraph following it
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

variable (I : Type u) [Finite I] {Y S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The integral morphism attached to an invertible module and generating sections exists
uniquely, including for an arbitrary finite coordinate set. -/
theorem generatingSections_integralHom_exists (L : Y.Modules) [L.IsInvertible]
    (s : I → L.sections) (hs : Epi (L.freeHomEquiv.symm s)) :
    ∃! ψ : Y ⟶ ℙ(I; Spec (CommRingCat.of (ULift.{u} ℤ))),
      ∃ e : (Scheme.Modules.tensorPullback ψ).obj
          (twist I (Spec (CommRingCat.of (ULift.{u} ℤ))) 1) ≅ L,
        ∀ i : I, e.hom.app ⊤ (((Classical.choose
          (Scheme.Modules.exists_tensorPullbackAdjunction ψ)).unit.app
            (twist I (Spec (CommRingCat.of (ULift.{u} ℤ))) 1)).val.app (Opposite.op ⊤)
              (twistOneSection I (Spec (CommRingCat.of (ULift.{u} ℤ))) i)) =
          (s i).val (Opposite.op ⊤) := by
  -- The native chart construction works for arbitrary coordinate types, including the empty type.
  classical
  let a : I → Γ(L, ⊤) := fun i ↦ (s i).val (Opposite.op ⊤)
  have hnonvan : ∀ y : Y, ∃ i, y ∈ nonvanishingLocus L (a i) := by
    intro y
    obtain ⟨e⟩ := invertible_stalk_linearEquiv Y L y
    have hspan := (generating_sections_iff_stalk_span Y L s).mp hs y
    by_contra! hn
    let P : Submodule (Y.presheaf.stalk y) ↑(TopCat.Presheaf.stalk L.val.presheaf y) :=
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) • ⊤
    have hle : Submodule.span (Y.presheaf.stalk y)
        (Set.range fun i ↦ TopCat.Presheaf.germ L.val.presheaf ⊤ y trivial (a i)) ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact not_not.mp (hn i)
    have hm : P.map e.toLinearMap = IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
      simp only [P, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range,
        Ideal.smul_eq_mul, Ideal.mul_top]
    have h1 : (1 : Y.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
      rw [← hm]
      exact ⟨e.symm 1, hle (hspan ▸ Submodule.mem_top), e.apply_symm_apply 1⟩
    exact (IsLocalRing.maximalIdeal.isMaximal (Y.presheaf.stalk y)).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    IsInvertible.sheafOfModules_isInvertible L
  let U : I → Y.Opens := fun i ↦
    (Hom.zeroLocus (homOfGlobalSection L (a i))).support.compl
  have hU : ⨆ i, U i = ⊤ := by
    apply eq_top_iff.mpr
    intro y _
    obtain ⟨i, hi⟩ := hnonvan y
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    rwa [nonvanishingLocus_eq_compl_support_zeroLocus] at hi
  have hgen (i : I) : IsFreeGenerator
      (L.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (a i)) := by
    have h := isFreeGenerator_app_one_of_le (homOfGlobalSection L (a i)) (U := U i) le_rfl
    change IsFreeGenerator ((homOfGlobalSection L (a i)).app (U i)
      (show Γ(Y, U i) from 1)) at h
    rwa [homOfGlobalSection_app_one] at h
  let Z := Spec (CommRingCat.of (ULift.{u} ℤ))
  let φ := homOfIsFreeGenerator a U hgen (specULiftZIsTerminal.from Y) hU
  let ε : (Scheme.Modules.pullback φ).obj (twist I Z 1) ≅ L :=
    asIso (twistRestrictHom a U hgen (specULiftZIsTerminal.from Y) hU)
  have hε (i : I) : ε.hom.app ⊤ (pullbackSection φ (twistOneSection I Z i)) = a i := by
    have h := twistRestrictHom_app_pullbackSection a U hgen
      (specULiftZIsTerminal.from Y) hU i
    simpa only [φ, ε, asIso_hom, Scheme.Hom.preimage_top, presheaf_map_id_apply] using h
  have transfer (ψ : Y ⟶ ℙ(I; Z)) :
      (∃ e : (Scheme.Modules.pullback ψ).obj (twist I Z 1) ≅ L,
        ∀ i, e.hom.app ⊤ (pullbackSection ψ (twistOneSection I Z i)) = a i) ↔
      (∃ e : (tensorPullback ψ).obj (twist I Z 1) ≅ L,
        ∀ i, e.hom.app ⊤ (((Classical.choose
          (exists_tensorPullbackAdjunction ψ)).unit.app (twist I Z 1)).val.app
            (Opposite.op ⊤) (twistOneSection I Z i)) = a i) := by
    let adj := Classical.choose (exists_tensorPullbackAdjunction ψ)
    let c := (adj.leftAdjointUniq (pullbackPushforwardAdjunction ψ)).app (twist I Z 1)
    have hc (i : I) : c.hom.app ⊤ ((adj.unit.app (twist I Z 1)).val.app
        (Opposite.op ⊤) (twistOneSection I Z i)) =
        pullbackSection ψ (twistOneSection I Z i) := by
      exact congrArg (fun t ↦ t.val.app (Opposite.op ⊤) (twistOneSection I Z i))
        (adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction ψ) (twist I Z 1))
    constructor
    · rintro ⟨e, he⟩
      refine ⟨c ≪≫ e, ?_⟩
      intro i
      simpa only [Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply,
        Functor.leftUnitor_inv_app, Hom.id_app, AddCommGrpCat.id_apply] using
          (congrArg (e.hom.app ⊤) (hc i)).trans (he i)
    · rintro ⟨e, he⟩
      refine ⟨c.symm ≪≫ e, ?_⟩
      intro i
      simp only [Iso.trans_hom, Iso.symm_hom, Hom.comp_app, ConcreteCategory.comp_apply]
      rw [← hc]
      have hci : c.inv.app ⊤ (c.hom.app ⊤ ((adj.unit.app (twist I Z 1)).val.app
          (Opposite.op ⊤) (twistOneSection I Z i))) =
          (adj.unit.app (twist I Z 1)).val.app (Opposite.op ⊤) (twistOneSection I Z i) := by
        rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app]
        rfl
      rw [hci]
      exact he i
  refine ⟨φ, (transfer φ).mp ⟨ε, hε⟩, ?_⟩
  intro ψ hψ
  obtain ⟨eψ, heψ⟩ := (transfer ψ).mpr hψ
  have hε' (i : I) : ε.hom.app _ (pullbackSection φ (twistOneSection I Z i)) =
      L.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ ⊤ ≤ ⊤)).op (a i) := by
    simpa only [Scheme.Hom.preimage_top, presheaf_map_id_apply] using hε i
  have heψ' (i : I) : eψ.hom.app _ (pullbackSection ψ (twistOneSection I Z i)) =
      L.presheaf.map (homOfLE (le_top : ψ ⁻¹ᵁ ⊤ ≤ ⊤)).op (a i) := by
    simpa only [Scheme.Hom.preimage_top, presheaf_map_id_apply] using heψ i
  let W : I → Y.Opens := fun i ↦ φ ⁻¹ᵁ standardOpen I Z i
  have hW : ⨆ i, W i = ⊤ := Scheme.Hom.iSup_preimage_eq_top φ (iSup_standardOpen I Z)
  have hWψ (i : I) : W i ≤ ψ ⁻¹ᵁ standardOpen I Z i := by
    dsimp only [W]
    rw [← generatingLocus_eq_preimage_standardOpen ε.hom hε' i,
      generatingLocus_eq_preimage_standardOpen eψ.hom heψ' i]
  apply Scheme.Opens.hom_ext_of_iSup_eq_top W hW
  intro i
  have hcoeff (j : I) : φ.appLE (standardOpen I Z i) (W i) le_rfl (coordRatio I Z i j) =
      ψ.appLE (standardOpen I Z i) (W i) (hWψ i) (coordRatio I Z i j) := by
    apply (isFreeGenerator_of_twistRestrict_iso ε.hom hε' i).smul_left_injective
    rw [Scheme.Hom.appLE]
    simp only [CommRingCat.comp_apply]
    rw [Scheme.presheaf_map_id_apply,
      ← map_eq_coordRatio_smul_of_twistRestrict_iso ε.hom hε' i j]
    have h := congrArg (L.presheaf.map (homOfLE (hWψ i)).op)
      (map_eq_coordRatio_smul_of_twistRestrict_iso eψ.hom heψ' i j)
    rw [Scheme.Modules.map_smul, presheaf_map_homOfLE_map_homOfLE,
      presheaf_map_homOfLE_map_homOfLE] at h
    exact h
  have h₁ : ((W i).ι ≫ ψ) ⁻¹ᵁ standardOpen I Z i = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ hWψ i x.2
  have h₂ : ((W i).ι ≫ φ) ⁻¹ᵁ standardOpen I Z i = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ x.2
  apply hom_ext_of_preimage_standardOpen_eq_top i h₁ h₂
  · exact specULiftZIsTerminal.hom_ext _ _
  · intro j
    have e₁ (h) : ((W i).ι ≫ ψ).appLE (standardOpen I Z i) ⊤ h
        (coordRatio I Z i j) = (W i).ι.appLE (W i) ⊤ (fun x _ ↦ x.2)
          (ψ.appLE (standardOpen I Z i) (W i) (hWψ i) (coordRatio I Z i j)) := by
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    have e₂ (h) : ((W i).ι ≫ φ).appLE (standardOpen I Z i) ⊤ h
        (coordRatio I Z i j) = (W i).ι.appLE (W i) ⊤ (fun x _ ↦ x.2)
          (φ.appLE (standardOpen I Z i) (W i) le_rfl (coordRatio I Z i j)) := by
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    rw [e₁, e₂, hcoeff]

/-- The morphism `ψ` into integral projective space classified by the given pair. -/
noncomputable def integralHomOfGeneratingSections (L : Y.Modules) [L.IsInvertible]
    (s : I → L.sections) (hs : Epi (L.freeHomEquiv.symm s)) :
    Y ⟶ ℙ(I; Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  Classical.choose (generatingSections_integralHom_exists I L s hs)

/-- Pair `g` with the integral morphism classified by `(L,s)` using the universal property
of the fibre product. No trivialization of `L` is an additional input. -/
noncomputable def homOfGeneratingSections (g : Y ⟶ S) (L : Y.Modules) [L.IsInvertible]
    (s : I → L.sections) (hs : Epi (L.freeHomEquiv.symm s)) : Y ⟶ ℙ(I; S) :=
  pullback.lift g
    (integralHomOfGeneratingSections I L s hs ≫
      toProjInt I (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (terminal.hom_ext _ _)

end AlgebraicGeometry.ProjectiveSpace
