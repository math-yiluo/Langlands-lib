/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusElement
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction

/-!
# Weil groups along an open immersion

Let `j : U ⟶ C` be a morphism of schemes over a finite field `k₀`, with `j ≫ p = pU`. The
constant covers of `C` pull back to those of `U`: on geometric fibres at `s` and `s ≫ j`, the map
`y ↦ y ≫ (j ×_{k₀} 1)` from the fibre of `U ×_{k₀} Spec A` to that of `C ×_{k₀} Spec A` is a
bijection compatible with the actions of the fundamental groups and with the Frobenius
(`AlgebraicGeometry.Scheme.FiniteEtale.constantCoverFiberMap`). Hence the induced map
`ρ : π₁(U, s) → π₁(C, t)` preserves the Weil groups and their degrees:
`(g, n) ∈ W(U) ↔ (ρ g, n) ∈ W(C)`
(`AlgebraicGeometry.Scheme.FiniteEtale.mem_weilGroup_fundamentalGroupMap_iff`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {K : Type u} [Field K] {U C : Scheme.{u}} {pU : U ⟶ Spec (.of K)}
  {p : C ⟶ Spec (.of K)} (j : U ⟶ C) (hj : j ≫ p = pU)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U)

include hj

/-- The morphism `U ×_{k₀} Spec A ⟶ C ×_{k₀} Spec A` of constant covers induced by `j`. -/
noncomputable def constantCoverLeftMap (A : FiniteEtaleAlgebra K) :
    (constantCover pU A).obj.left ⟶ (constantCover p A).obj.left :=
  Limits.pullback.map pU A.specHom p A.specHom j (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hj])
    (by simp)

@[reassoc (attr := simp)]
lemma constantCoverLeftMap_fst (A : FiniteEtaleAlgebra K) :
    constantCoverLeftMap j hj A ≫ Limits.pullback.fst p A.specHom =
      Limits.pullback.fst pU A.specHom ≫ j := by
  simp [constantCoverLeftMap]

@[reassoc (attr := simp)]
lemma constantCoverLeftMap_snd (A : FiniteEtaleAlgebra K) :
    constantCoverLeftMap j hj A ≫ Limits.pullback.snd p A.specHom =
      Limits.pullback.snd pU A.specHom := by
  simp [constantCoverLeftMap]

/-- The map `y ↦ y ≫ (j ×_{k₀} 1)` between geometric fibres of constant covers. -/
noncomputable def constantCoverFiberMap (A : FiniteEtaleAlgebra K)
    (y : (fiber s).obj (constantCover pU A)) : (fiber (s ≫ j)).obj (constantCover p A) :=
  fiberMk (s ≫ j) (constantCover p A) (y.left ≫ constantCoverLeftMap j hj A) (by
    change (y.left ≫ constantCoverLeftMap j hj A) ≫ Limits.pullback.fst p A.specHom = s ≫ j
    rw [Category.assoc, constantCoverLeftMap_fst, ← Category.assoc]
    exact congrArg (· ≫ j) (fiber_left_comp s y))

omit [IsSepClosed Ω] in
lemma baseRingHom_comp : baseRingHom p (s ≫ j) = baseRingHom pU s := by
  rw [baseRingHom, baseRingHom, Category.assoc, hj]

lemma fiberConstantCoverEquiv_constantCoverFiberMap (A : FiniteEtaleAlgebra K)
    (y : (fiber s).obj (constantCover pU A)) :
    (fiberConstantCoverEquiv p (s ≫ j) A (constantCoverFiberMap j hj s A y)).1 =
      (fiberConstantCoverEquiv pU s A y).1 := by
  rw [fiberConstantCoverEquiv_apply, fiberConstantCoverEquiv_apply]
  change (Spec.preimage ((y.left ≫ constantCoverLeftMap j hj A) ≫
    Limits.pullback.snd p A.specHom)).hom = _
  rw [Category.assoc, constantCoverLeftMap_snd]

lemma constantCoverFiberMap_bijective (A : FiniteEtaleAlgebra K) :
    Function.Bijective (constantCoverFiberMap j hj s A) := by
  refine ⟨fun y y' h ↦ (fiberConstantCoverEquiv pU s A).injective (Subtype.ext ?_), fun z ↦ ?_⟩
  · rw [← fiberConstantCoverEquiv_constantCoverFiberMap j hj s A y, h,
      fiberConstantCoverEquiv_constantCoverFiberMap]
  · let φ := fiberConstantCoverEquiv p (s ≫ j) A z
    refine ⟨(fiberConstantCoverEquiv pU s A).symm ⟨φ.1, by
      rw [φ.2, baseRingHom_comp j hj s]⟩, ?_⟩
    apply (fiberConstantCoverEquiv p (s ≫ j) A).injective
    apply Subtype.ext
    rw [fiberConstantCoverEquiv_constantCoverFiberMap, Equiv.apply_symm_apply]

lemma constantCoverFiberMap_fiber_map_arithmeticFrobenius [Finite K] (A : FiniteEtaleAlgebra K)
    (y : (fiber s).obj (constantCover pU A)) :
    constantCoverFiberMap j hj s A ((fiber s).map (arithmeticFrobenius pU A).hom y) =
      (fiber (s ≫ j)).map (arithmeticFrobenius p A).hom (constantCoverFiberMap j hj s A y) := by
  apply fiber_ext
  change (y.left ≫ (arithmeticFrobenius pU A).hom.hom.left) ≫ constantCoverLeftMap j hj A =
    (y.left ≫ constantCoverLeftMap j hj A) ≫ (arithmeticFrobenius p A).hom.hom.left
  simp only [Category.assoc]
  congr 1
  apply Limits.pullback.hom_ext <;>
    simp [arithmeticFrobenius, constantCoverIso, constantCoverMap_hom_left]

lemma constantCoverFiberMap_geometricFrobenius_zpow [Finite K] (A : FiniteEtaleAlgebra K) (n : ℤ)
    (y : (fiber s).obj (constantCover pU A)) :
    constantCoverFiberMap j hj s A ((geometricFrobenius pU s A ^ n) y) =
      (geometricFrobenius p (s ≫ j) A ^ n) (constantCoverFiberMap j hj s A y) := by
  have h (y : (fiber s).obj (constantCover pU A)) :
      constantCoverFiberMap j hj s A ((geometricFrobenius pU s A)⁻¹ y) =
        (geometricFrobenius p (s ≫ j) A)⁻¹ (constantCoverFiberMap j hj s A y) :=
    constantCoverFiberMap_fiber_map_arithmeticFrobenius j hj s A y
  have := Equiv.Perm.zpow_apply_eq_of_comm _ _ _ h (-n) y
  simpa using this

/-- The point `y ≫ (j ×_{k₀} 1)` of the fibre of `C ×_{k₀} Spec A` at `s ≫ j` is the image under
the canonical isomorphism `F_s ∘ j^* ≅ F_{s ≫ j}` of the image of `y` under the morphism
`U ×_{k₀} Spec A ⟶ j^* (C ×_{k₀} Spec A)`. -/
noncomputable def constantCoverToPullback (A : FiniteEtaleAlgebra K) :
    constantCover pU A ⟶ (pullback j).obj (constantCover p A) :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk
    (Limits.pullback.lift (constantCoverLeftMap j hj A) (Limits.pullback.fst pU A.specHom)
      (constantCoverLeftMap_fst j hj A))
    (Limits.pullback.lift_snd _ _ _))

lemma pullbackFiberIso_constantCoverToPullback (A : FiniteEtaleAlgebra K)
    (y : (fiber s).obj (constantCover pU A)) :
    (pullbackFiberIso j s).hom.app _ ((fiber s).map (constantCoverToPullback j hj A) y) =
      constantCoverFiberMap j hj s A y := by
  apply fiber_ext
  change (y.left ≫ Limits.pullback.lift _ _ _) ≫ Limits.pullback.fst _ j = _
  simp [constantCoverFiberMap]

variable [Finite K] {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] {t : Spec (.of Ω') ⟶ C}
  (τ : fiber (s ≫ j) ≅ fiber t)
  (GU : Type u) [Group GU] [∀ P, MulAction GU ((fiber s).obj P)] [IsNaturalSMul (fiber s) GU]
  [ConnectedSpace C] (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC]
  [CompactSpace GC] [∀ P, MulAction GC ((fiber t).obj P)] [IsFundamentalGroup (fiber t) GC]

omit [Finite K] in
lemma fundamentalGroupMap_smul_constantCoverFiberMap (g : GU) (A : FiniteEtaleAlgebra K)
    (y : (fiber s).obj (constantCover pU A)) :
    fundamentalGroupMap (pullbackFiberIso j s ≪≫ τ) GU GC g •
        τ.hom.app _ (constantCoverFiberMap j hj s A y) =
      τ.hom.app _ (constantCoverFiberMap j hj s A (g • y)) := by
  have h := fundamentalGroupMap_smul (pullbackFiberIso j s ≪≫ τ) GU GC g (constantCover p A)
    ((fiber s).map (constantCoverToPullback j hj A) y)
  simp only [Iso.trans_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    pullbackFiberIso_constantCoverToPullback] at h
  rw [h, ← IsNaturalSMul.naturality, pullbackFiberIso_constantCoverToPullback]

/-- The map of fundamental groups induced by `j` preserves the Weil groups and the degrees. -/
theorem mem_weilGroup_fundamentalGroupMap_iff [GeometricallyConnected p]
    [GeometricallyConnected pU] (g : GU) (n : Multiplicative ℤ) :
    (g, n) ∈ weilGroup pU s GU ↔
      (fundamentalGroupMap (pullbackFiberIso j s ≪≫ τ) GU GC g, n) ∈ weilGroup p t GC := by
  rw [mem_weilGroup_iff, mem_weilGroup_iff]
  refine forall_congr' fun A ↦ ⟨fun h z ↦ ?_, fun h y ↦ ?_⟩
  · obtain ⟨w, rfl⟩ : ∃ w, τ.hom.app _ w = z :=
      ⟨τ.inv.app _ z, ConcreteCategory.congr_hom (τ.inv_hom_id_app _) z⟩
    obtain ⟨y, rfl⟩ := (constantCoverFiberMap_bijective j hj s A).2 w
    rw [fundamentalGroupMap_smul_constantCoverFiberMap, h,
      constantCoverFiberMap_geometricFrobenius_zpow, app_geometricFrobenius_zpow]
  · apply (constantCoverFiberMap_bijective j hj s A).1
    have hinj : Function.Injective (τ.hom.app (constantCover p A)) :=
      ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
    apply hinj
    rw [← fundamentalGroupMap_smul_constantCoverFiberMap j hj s τ GU GC g A y, h,
      constantCoverFiberMap_geometricFrobenius_zpow, app_geometricFrobenius_zpow]

end AlgebraicGeometry.Scheme.FiniteEtale
