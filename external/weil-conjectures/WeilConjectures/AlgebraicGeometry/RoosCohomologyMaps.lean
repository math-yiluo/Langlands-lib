/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.AlgebraicGeometry.MilnorTower
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-!
# Explicit maps and exactness for the strict Roos cohomology sequence
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

section Helpers

variable {A : Type a} [Category.{b} A] [Abelian A]

theorem extract_shortExact {P Q H U V : A}
    (f : P ⟶ Q) (g : Q ⟶ H) (i : H ⟶ U) (j : U ⟶ V)
    (hfg : f ≫ g = 0) (hgi : g ≫ i = 0) (hij : i ≫ j = 0)
    (h₁ : (ShortComplex.mk f g hfg).Exact)
    (h₂ : (ShortComplex.mk g i hgi).Exact)
    (h₃ : (ShortComplex.mk i j hij).Exact) :
    ∃ h : cokernel.desc f g hfg ≫ kernel.lift j i hij = 0,
      (ShortComplex.mk (cokernel.desc f g hfg) (kernel.lift j i hij) h).ShortExact := by
  have hz : cokernel.desc f g hfg ≫ kernel.lift j i hij = 0 := by
    apply (cancel_epi (cokernel.π f)).1
    apply (cancel_mono (kernel.ι j)).1
    simp [Category.assoc, hgi]
  refine ⟨hz, ?_⟩
  have : Mono (cokernel.desc f g hfg) := h₁.mono_cokernelDesc
  have : Epi (kernel.lift j i hij) := h₃.epi_kernelLift
  refine ⟨?_⟩
  let S := ShortComplex.mk g i hgi
  let T := ShortComplex.mk (cokernel.desc f g hfg) (kernel.lift j i hij) hz
  let S' := ShortComplex.mk (cokernel.desc f g hfg) i (by
    apply (cancel_epi (cokernel.π f)).1
    simp [hgi])
  let φ : S ⟶ S' :=
    { τ₁ := cokernel.π f
      τ₂ := 𝟙 H
      τ₃ := 𝟙 U
      comm₁₂ := by simp [S, S']
      comm₂₃ := by simp [S, S'] }
  have h' : S'.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 h₂
  let ψ : T ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 H
      τ₃ := kernel.ι j
      comm₁₂ := by simp [T, S']
      comm₂₃ := by simp [T, S'] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 h'

variable [HasCountableLimits A]

def towerKernelIso (M : ℕᵒᵖ ⥤ A) :
    kernel (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
      (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op)) ≅ limit M :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel _)
    (Fan.IsLimit.isLimitKernelForkOneSub (productIsProduct _)
      (towerProductShift (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op))
      (fun n ↦ by simp [towerProductShift]) (limit.isLimit M))

def productHomologyIso [HasExactLimitsOfShape (Discrete ℕ) A]
    (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (p : ℤ) :
    (∏ᶜ fun n : ℕ ↦ K.obj (op n)).homology p ≅
      ∏ᶜ fun n : ℕ ↦ (K.obj (op n)).homology p :=
  asIso (piComparison (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) p)
    (fun n : ℕ ↦ K.obj (op n)))

set_option backward.isDefEq.respectTransparency false in
theorem productHomologyIso_transition [HasExactLimitsOfShape (Discrete ℕ) A]
    (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (p : ℤ) :
    HomologicalComplex.homologyMap
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ K.obj (op n))
          (WeilConjectures.integralOperationsTowerStep K)) p ≫
        (productHomologyIso K p).hom =
      (productHomologyIso K p).hom ≫
        towerTransitionEndomorphism (K := fun n : ℕ ↦ (K.obj (op n)).homology p)
          (fun n ↦ HomologicalComplex.homologyMap
            (K.map (homOfLE (Nat.le_succ n)).op) p) := by
  apply Pi.hom_ext
  intro n
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) p
  change (H.map _ ≫ piComparison H (fun n : ℕ ↦ K.obj (op n))) ≫
      Pi.π (fun n : ℕ ↦ H.obj (K.obj (op n))) n =
    (piComparison H (fun n : ℕ ↦ K.obj (op n)) ≫
      towerTransitionEndomorphism (fun n ↦ H.map (K.map (homOfLE (Nat.le_succ n)).op))) ≫
        Pi.π (fun n : ℕ ↦ H.obj (K.obj (op n))) n
  rw [Category.assoc, piComparison_comp_π, ← H.map_comp]
  simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
    Category.id_comp, Pi.lift_comp_π, H.map_sub, H.map_comp,
    Category.assoc, Preadditive.comp_sub, piComparison_comp_π]
  rw [← Category.assoc, piComparison_comp_π]
  rfl

abbrev roosTransition (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  towerTransitionEndomorphism (K := fun n : ℕ ↦ K.obj (op n))
    (WeilConjectures.integralOperationsTowerStep K)

def roosBoundary (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) :
    (∏ᶜ fun n : ℕ ↦ K.obj (op n)).homology (q - 1) ⟶
      (WeilConjectures.integralOperationsRoos K).homology q := by
  letI := HasDerivedCategory.standard A
  exact CochainComplex.homologyδOfTriangle
    (CochainComplex.mappingCocone.triangle (roosTransition K)) (q - 1) q (by omega)

abbrev roosProjection (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) :=
  HomologicalComplex.homologyMap (CochainComplex.mappingCocone.fst (roosTransition K)) q

theorem roosBoundary_exact (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) :
    ∃ (h₁ : HomologicalComplex.homologyMap (roosTransition K) (q - 1) ≫
        roosBoundary K q = 0)
      (h₂ : roosBoundary K q ≫ roosProjection K q = 0)
      (h₃ : roosProjection K q ≫ HomologicalComplex.homologyMap (roosTransition K) q = 0),
      (ShortComplex.mk _ _ h₁).Exact ∧ (ShortComplex.mk _ _ h₂).Exact ∧
        (ShortComplex.mk _ _ h₃).Exact := by
  let _ := HasDerivedCategory.standard A
  let T := CochainComplex.mappingCocone.triangle (roosTransition K)
  have hT := DerivedCategory.mappingCocone_triangle_distinguished (roosTransition K)
  exact ⟨_, _, _, CochainComplex.homologyMap_exact₃_of_distTriang T hT (q - 1) q (by omega),
    CochainComplex.homologyMap_exact₁_of_distTriang T hT (q - 1) q (by omega),
    CochainComplex.homologyMap_exact₂_of_distTriang T hT q⟩

def roosCokernelIso [HasExactLimitsOfShape (Discrete ℕ) A]
    (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (p : ℤ) :
    cokernel (HomologicalComplex.homologyMap (roosTransition K) p) ≅
      milnorTowerCokernel (milnorCohomologyTower K p) :=
  cokernel.mapIso _ _ (productHomologyIso K p) (productHomologyIso K p)
    (productHomologyIso_transition K p)

def roosKernelIso [HasExactLimitsOfShape (Discrete ℕ) A]
    (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (p : ℤ) :
    kernel (HomologicalComplex.homologyMap (roosTransition K) p) ≅
      limit (milnorCohomologyTower K p) :=
  kernel.mapIso _ _ (productHomologyIso K p) (productHomologyIso K p)
    (productHomologyIso_transition K p) ≪≫ towerKernelIso (milnorCohomologyTower K p)

def milnorInclusion [HasExactLimitsOfShape (Discrete ℕ) A]
    (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) :
    milnorTowerCokernel (milnorCohomologyTower K (q - 1)) ⟶
      (WeilConjectures.integralOperationsRoos K).homology q :=
  (roosCokernelIso K (q - 1)).inv ≫
    cokernel.desc _ (roosBoundary K q) (roosBoundary_exact K q).choose

def milnorProjection [HasExactLimitsOfShape (Discrete ℕ) A]
    (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) :
    (WeilConjectures.integralOperationsRoos K).homology q ⟶
      limit (milnorCohomologyTower K q) :=
  kernel.lift _ (roosProjection K q)
      (roosBoundary_exact K q).choose_spec.choose_spec.choose ≫ (roosKernelIso K q).hom

set_option backward.isDefEq.respectTransparency false in
/-- The explicit Roos boundary and projection form a short exact sequence.

proof.md, first paragraph
(auxiliary; not a blueprint node).

Proof: The mapping-cocone triangle gives three adjacent exact pairs. Factoring
its boundary through the preceding cokernel gives a monomorphism; factoring its
projection through the following kernel gives an epimorphism. The middle pair
remains exact by cancellation of the cokernel epimorphism and kernel monomorphism.
Exact products identify product homology with the product of homologies, and the
projection formulas identify the induced transition with one minus shift. Finally,
the kernel of one minus shift represents compatible families and hence the tower
limit. Transporting the factored sequence along these endpoint isomorphisms gives
the stated explicit short exact sequence. -/
theorem milnor_shortExact [HasExactLimitsOfShape (Discrete ℕ) A]
    (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) :
    ∃ h : milnorInclusion K q ≫ milnorProjection K q = 0,
      (ShortComplex.mk (milnorInclusion K q) (milnorProjection K q) h).ShortExact := by
  obtain ⟨h₁, h₂, h₃, he₁, he₂, he₃⟩ := roosBoundary_exact K q
  obtain ⟨hz, he⟩ := extract_shortExact _ _ _ _ h₁ h₂ h₃ he₁ he₂ he₃
  have hw : milnorInclusion K q ≫ milnorProjection K q = 0 := by
    dsimp only [milnorInclusion, milnorProjection]
    calc
      _ = (roosCokernelIso K (q - 1)).inv ≫
          (cokernel.desc _ (roosBoundary K q) h₁ ≫
            kernel.lift _ (roosProjection K q) h₃) ≫ (roosKernelIso K q).hom := by
              simp only [Category.assoc]
      _ = 0 := by rw [hz, zero_comp, comp_zero]
  refine ⟨hw, ShortComplex.shortExact_of_iso ?_ he⟩
  exact ShortComplex.isoMk (roosCokernelIso K (q - 1)) (Iso.refl _) (roosKernelIso K q)
    (by simp [milnorInclusion]) (by simp [milnorProjection])

end Helpers

end AlgebraicGeometry.Scheme.ProEt
