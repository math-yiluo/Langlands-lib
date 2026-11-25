/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import WeilConjectures.AlgebraicGeometry.AdicFiniteTransitionTensorSequence
import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # The endpoint Roos epimorphism for finite reductions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

private theorem map_roos
    {C : Type*} [Category C] [Preadditive C]
    {D : Type*} [Category D] [Preadditive D]
    (E : C ⥤ D) [E.Additive] (F : ℕ → C)
    [HasProduct F] [HasProduct (fun n ↦ E.obj (F n))]
    (t : ∀ n, F (n + 1) ⟶ F n) :
    E.map (towerTransitionEndomorphism t) ≫ piComparison E F =
      piComparison E F ≫ towerTransitionEndomorphism (fun n ↦ E.map (t n)) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, piComparison_comp_π, ← E.map_comp]
  simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
    Category.id_comp, Pi.lift_comp_π, E.map_sub, E.map_comp, Preadditive.comp_sub,
    Category.assoc, piComparison_comp_π, piComparison_comp_π_assoc]

private theorem model_exact_products (X : Scheme.{u})
    (R : Sheaf (coefficientProEtaleModelTopology.{u, v} X)
      RingCat.{max v (u + 1)}) :
    HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{max v (u + 1)} R) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let e := (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt))
  let : e.functor.IsContinuous (ProEt.topology X) T :=
    coefficientProEtaleModelUp_isContinuous X
  let : e.inverse.IsContinuous T (ProEt.topology X) := by
    change AsSmall.down.IsContinuous T (ProEt.topology X)
    infer_instance
  let F : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X := AsSmall.up
  let S := (F.sheafPushforwardContinuous RingCat.{max v (u + 1)} (ProEt.topology X) T).obj R
  let E : SheafOfModules.{max v (u + 1)} R ≌ SheafOfModules.{max v (u + 1)} S :=
    SheafOfModules.pushforwardPushforwardEquivalence (S := S) (R := R) e (𝟙 S) (𝟙 R)
      (by ext U; dsimp [e, AsSmall.equiv]; erw [R.obj.map_id]; rfl)
      (by ext U; dsimp [e, AsSmall.equiv]; erw [S.obj.map_id]; rfl)
  have : HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{max v (u + 1)} S) :=
    ProEt.products_exact.{u, v, 0} X S ℕ
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) E.symm

private theorem model_tower_epi (X : Scheme.{u})
    (R : Sheaf (coefficientProEtaleModelTopology.{u, v} X)
      RingCat.{max v (u + 1)})
    (K : ℕ → SheafOfModules.{max v (u + 1)} R)
    (t : ∀ n, K (n + 1) ⟶ K n) (ht : ∀ n, Epi (t n)) :
    Epi (towerTransitionEndomorphism t) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let e := (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt))
  let : e.functor.IsContinuous (ProEt.topology X) T :=
    coefficientProEtaleModelUp_isContinuous X
  let : e.inverse.IsContinuous T (ProEt.topology X) := by
    change AsSmall.down.IsContinuous T (ProEt.topology X)
    infer_instance
  let F : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X := AsSmall.up
  let S := (F.sheafPushforwardContinuous RingCat.{max v (u + 1)} (ProEt.topology X) T).obj R
  let E : SheafOfModules.{max v (u + 1)} R ≌ SheafOfModules.{max v (u + 1)} S :=
    SheafOfModules.pushforwardPushforwardEquivalence (S := S) (R := R) e (𝟙 S) (𝟙 R)
      (by ext U; dsimp [e, AsSmall.equiv]; erw [R.obj.map_id]; rfl)
      (by ext U; dsimp [e, AsSmall.equiv]; erw [S.obj.map_id]; rfl)
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products E.functor
  let := HasDerivedCategory.standard (SheafOfModules.{max v (u + 1)} S)
  let M := Functor.ofOpSequence (X := fun n ↦ E.functor.obj (K n))
    (fun n ↦ E.functor.map (t n))
  have hM (n : ℕ) : Epi (M.map (homOfLE (Nat.le_succ n)).op) := by
    have := ht n
    dsimp only [M]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    infer_instance
  have he : Epi (towerTransitionEndomorphism (K := fun n ↦ E.functor.obj (K n))
      (fun n ↦ E.functor.map (t n))) := by
    simpa only [M, Functor.ofOpSequence_obj, Functor.ofOpSequence_map_homOfLE_succ]
      using (AlgebraicGeometry.ProEtale.milnor_epimorphic X S M hM).1
  have : Epi (E.functor.map (towerTransitionEndomorphism t) ≫ piComparison E.functor K) := by
    rw [map_roos]
    infer_instance
  have : Epi (E.functor.map (towerTransitionEndomorphism t)) :=
    (epi_comp_iff_of_isIso _ (piComparison E.functor K)).1 inferInstance
  exact E.functor.epi_of_epi_map inferInstance

private theorem top_transition_epi
    (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A) (a b : ℤ)
    (hTor : HasCoefficientProEtaleTorAmplitude.{u, v} X (adicFiniteCoeff J 0)
      (adicFiniteReduction.{u, v} X J N 0) a b) (n : ℕ) :
    Epi ((coefficientModelCohomology
      (constant (coefficientProEtaleModelTopology.{u, v} X) A) b).map
        (adicFiniteTransition.{u, v} X J N n)) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := constant T A
  let B := Mod R
  let := HasDerivedCategory.standard B
  let H := coefficientModelCohomology R b
  obtain ⟨P, hp, eP, M, S, hS, e₂, e₃, hs, hk⟩ :=
    adicFiniteTransition_tensor_sequence X A J N n
  have hz := hTor.2 P hp eP M (b + 1) (Or.inr (by omega))
  have hz' : IsZero (S.X₁.homology (b + 1)) :=
    ((res (quotient T A J 0)).map_isZero hz).of_iso (Classical.choice (hk (b + 1)))
  have : Epi (HomologicalComplex.homologyMap S.g b) :=
    (hS.homology_exact₃ b (b + 1) rfl).epi_f (hz'.eq_zero_of_tgt _)
  have : Epi (H.map ((Q R).map S.g) ≫
      (DerivedCategory.homologyFunctorFactors B b).hom.app S.X₃) := by
    rw [DerivedCategory.homologyFunctorFactors_hom_naturality]
    infer_instance
  have : Epi (H.map ((Q R).map S.g)) :=
    (epi_comp_iff_of_isIso _
      ((DerivedCategory.homologyFunctorFactors B b).hom.app S.X₃)).mp inferInstance
  have : Epi (H.map e₂.hom ≫ H.map (adicFiniteTransition X J N n)) := by
    rw [← H.map_comp, ← hs, H.map_comp]
    infer_instance
  exact epi_of_epi (H.map e₂.hom) (H.map (adicFiniteTransition X J N n))

/-- The degree-b Roos endomorphism of the normalized reduction product is epic.
Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1),
and sites-cohomology.tex, Tag 0947.
(auxiliary; not a blueprint node).

Proof: Resolve N by one K-flat complex P with flat terms. Its quotient scalar
extensions compute all reductions. Tensor the exact sequence
0 -> J^(n+1)/J^(n+2) -> A/J^(n+2) -> A/J^(n+1) -> 0 with P.
Flatness makes this a short exact sequence of complexes. The first term is,
by scalar balancing, the tensor of the residue reduction with the displayed
A/J-module sheaf. The residue Tor test makes its cohomology in degree b+1
zero. The long exact sequence therefore makes each transition on H^b epic.
The scalar-unit normalization identifies these maps with H^b(adicFiniteTransition).
For the epimorphic module tower, one minus its shift on the product is epic:
evaluate at affine weakly contractible objects, lift recursively, and detect
epimorphy on this conservative family. Transport to the coefficient-sized site.
Exact countable products imply that derived cohomology preserves this product.
Its projection comparison conjugates H^b of the stated Roos endomorphism to
one minus shift of the cohomology tower, proving the assertion. This uses no
completeness of N. The argument also applies to J=0, J=A and empty schemes. -/
theorem adicFiniteTop_roos_epi
    (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A)
    [HasProduct (adicFiniteUnderlying.{u, v} X J N)]
    (a b : ℤ)
    (hTor : HasCoefficientProEtaleTorAmplitude.{u, v} X (adicFiniteCoeff J 0)
      (adicFiniteReduction.{u, v} X J N 0) a b) :
    Epi ((coefficientModelCohomology
      (constant (coefficientProEtaleModelTopology.{u, v} X) A) b).map
        (towerTransitionEndomorphism (adicFiniteTransition.{u, v} X J N))) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := constant T A
  let B := Mod R
  let := HasDerivedCategory.standard B
  let H := coefficientModelCohomology R b
  let U := adicFiniteUnderlying.{u, v} X J N
  let t := adicFiniteTransition.{u, v} X J N
  have : HasExactLimitsOfShape (Discrete ℕ) B :=
    model_exact_products X (siteModuleRings R)
  have : CountableAB4Star B := CountableAB4Star.of_hasExactLimitsOfShape_nat B
  have : PreservesLimitsOfShape (Discrete ℕ) H :=
    (derivedCategory_countableProducts_core B).choose_spec.2 ℕ b
  have ht (n : ℕ) : Epi (H.map (t n)) := top_transition_epi X A J N a b hTor n
  have : Epi (towerTransitionEndomorphism (K := fun n ↦ H.obj (U n))
      (fun n ↦ H.map (t n))) := model_tower_epi X (siteModuleRings R) _ _ ht
  have : Epi (H.map (towerTransitionEndomorphism t) ≫ piComparison H U) := by
    rw [map_roos]
    infer_instance
  exact (epi_comp_iff_of_isIso _ (piComparison H U)).mp inferInstance

end AlgebraicGeometry.Scheme
