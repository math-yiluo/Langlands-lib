/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import Mathlib.Algebra.Homology.BifunctorHomotopy
import all WeilConjectures.AlgebraicGeometry.FlatLocalizationKoszulHomotopy
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections

/-! # Scalar contraction for the ordered ringed Koszul complex

Source: Stacks Project, More on Algebra, Tag 0913.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory
open SheafOfModules.LocalizationCech

private theorem double_scalar_nullhomotopy
    {A : Type*} [Category A] [Abelian A] (z : 𝟭 A ⟶ 𝟭 A) (P : A) :
    Nonempty (Homotopy ((z.mapHomologicalComplex (.up ℤ)).app
      (HomologicalComplex.double (z.app P) (by decide : (ComplexShape.up ℤ).Rel 0 1))) 0) := by
  let K := HomologicalComplex.double (z.app P) (by decide : (ComplexShape.up ℤ).Rel 0 1)
  let h (i j : ℤ) : K.X i ⟶ K.X j :=
    if hi : i = 1 then if hj : j = 0 then
      eqToHom (congrArg K.X hi) ≫ (HomologicalComplex.doubleXIso₁ _ _ (by decide)).hom ≫
        (HomologicalComplex.doubleXIso₀ _ _).inv ≫ eqToHom (congrArg K.X hj.symm)
      else 0 else 0
  refine ⟨⟨h, ?_, ?_⟩⟩
  · intro i j hij
    dsimp [h]
    split_ifs with hi hj
    · subst i; subst j; exact False.elim (hij (by decide))
    · rfl
    · rfl
  · intro i
    by_cases h0 : i = 0
    · subst i
      simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.zero_f]
      apply (cancel_mono (HomologicalComplex.doubleXIso₀ (z.app P)
        (by decide : (ComplexShape.up ℤ).Rel 0 1)).hom).1
      simpa [dNext, prevD, h, K, HomologicalComplex.double_d, Category.assoc] using
        (z.naturality (HomologicalComplex.doubleXIso₀ (z.app P)
          (by decide : (ComplexShape.up ℤ).Rel 0 1)).hom).symm
    · by_cases h1 : i = 1
      · subst i
        simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.zero_f]
        apply (cancel_mono (HomologicalComplex.doubleXIso₁ (z.app P)
          (by decide : (ComplexShape.up ℤ).Rel 0 1) (by decide)).hom).1
        simpa [dNext, prevD, h, K, HomologicalComplex.double_d, Category.assoc] using
          (z.naturality (HomologicalComplex.doubleXIso₁ (z.app P)
            (by decide : (ComplexShape.up ℤ).Rel 0 1) (by decide)).hom).symm
      · exact (HomologicalComplex.isZero_double_X (z.app P)
          (by decide : (ComplexShape.up ℤ).Rel 0 1) i h0 h1).eq_of_src _ _

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

private theorem sectionScalarNat_tensor_left
    (R : Sheaf J CommRingCat.{u}) (s : (SheafOfModules.unit (rings R)).sections)
    (e : ℕ) (M N : SheafOfModules.{u} (rings R)) :
    letI := SheafOfModules.monoidalCategory R
    (sectionScalarNat R s e).app M ▷ N = (sectionScalarNat R s e).app (M ⊗ N) := by
  let := SheafOfModules.monoidalCategory R
  apply SheafOfModules.RingedTensor.pure_hom_ext R M N
  intro X m n
  have h := SheafOfModules.RingedTensor.pure_map R
    ((sectionScalarNat R s e).app M) (𝟙 N) X m n
  simp only [tensorHom_def, whiskerLeft_id, Category.comp_id] at h
  erw [h]
  change SheafOfModules.RingedTensor.pure R M N X
    (((show R.obj.obj X from s.val X) ^ e) • m) n =
    ((show R.obj.obj X from s.val X) ^ e) • SheafOfModules.RingedTensor.pure R M N X m n
  change ((SheafOfModules.RingedTensor.pureMap R M N).app X)
      ((((show R.obj.obj X from s.val X) ^ e) • m) ⊗ₜ[R.obj.obj X] n) = _
  rw [← TensorProduct.smul_tmul']
  exact ((SheafOfModules.RingedTensor.pureMap R M N).app X).hom.map_smul _ _

private theorem sectionScalarNat_tensor_right
    (R : Sheaf J CommRingCat.{u}) (s : (SheafOfModules.unit (rings R)).sections)
    (e : ℕ) (M N : SheafOfModules.{u} (rings R)) :
    letI := SheafOfModules.monoidalCategory R
    M ◁ (sectionScalarNat R s e).app N = (sectionScalarNat R s e).app (M ⊗ N) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  apply (cancel_mono (β_ M N).hom).mp
  erw [BraidedCategory.braiding_naturality_right,
    sectionScalarNat_tensor_left]
  exact (sectionScalarNat R s e).naturality (β_ M N).hom

private theorem sectionScalarNat_tensorComplex_left
    (R : Sheaf J CommRingCat.{u}) (s : (SheafOfModules.unit (rings R)).sections)
    (e : ℕ) (K L : ringedSiteComplex R) :
    letI := SheafOfModules.monoidalCategory R
    HomologicalComplex.mapBifunctorMap
        (((sectionScalarNat R s e).mapHomologicalComplex (.up ℤ)).app K) (𝟙 L)
        (curriedTensor _) (.up ℤ) =
      ((sectionScalarNat R s e).mapHomologicalComplex (.up ℤ)).app
        (HomologicalComplex.mapBifunctor K L (curriedTensor _) (.up ℤ)) := by
  let := SheafOfModules.monoidalCategory R
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.id_f,
    Functor.map_id]
  change ((sectionScalarNat R s e).app (K.X p) ▷ L.X q) ≫ _ = _
  rw [sectionScalarNat_tensor_left]
  exact ((sectionScalarNat R s e).naturality
    (HomologicalComplex.ιMapBifunctor K L (curriedTensor _) (.up ℤ) p q n hpq)).symm

private theorem sectionScalarNat_tensorComplex_right
    (R : Sheaf J CommRingCat.{u}) (s : (SheafOfModules.unit (rings R)).sections)
    (e : ℕ) (K L : ringedSiteComplex R) :
    letI := SheafOfModules.monoidalCategory R
    HomologicalComplex.mapBifunctorMap (𝟙 K)
        (((sectionScalarNat R s e).mapHomologicalComplex (.up ℤ)).app L)
        (curriedTensor _) (.up ℤ) =
      ((sectionScalarNat R s e).mapHomologicalComplex (.up ℤ)).app
        (HomologicalComplex.mapBifunctor K L (curriedTensor _) (.up ℤ)) := by
  let := SheafOfModules.monoidalCategory R
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.id_f,
    Functor.map_id, NatTrans.id_app, Category.id_comp]
  change (K.X p ◁ (sectionScalarNat R s e).app (L.X q)) ≫ _ = _
  rw [sectionScalarNat_tensor_right]
  exact ((sectionScalarNat R s e).naturality
    (HomologicalComplex.ιMapBifunctor K L (curriedTensor _) (.up ℤ) p q n hpq)).symm

private theorem factor_scalar_nullhomotopy
    (R : Sheaf J CommRingCat.{u})
    (b : (R.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    Nonempty (Homotopy
      (((sectionScalarNat R ⟨b.val, b.property⟩ (n + 1)).mapHomologicalComplex
        (.up ℤ)).app (ringedKoszulFactor R b n)) 0) := by
  have he : (sectionScalarNat R ⟨b.val, b.property⟩ (n + 1)).app
      (SheafOfModules.unit (rings R)) = (ringedKoszulScalar R b ^ (n + 1)).asHom :=
    sectionScalarNat_unit R ⟨b.val, b.property⟩ (n + 1)
  unfold ringedKoszulFactor
  rw [← he]
  exact double_scalar_nullhomotopy _ _

private theorem tensor_map_zero_left
    (R : Sheaf J CommRingCat.{u}) (K L : ringedSiteComplex R) :
    letI := SheafOfModules.monoidalCategory R
    HomologicalComplex.mapBifunctorMap (0 : K ⟶ K) (𝟙 L)
      (curriedTensor _) (.up ℤ) = 0 := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.tensorClosed R).1.some
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.zero_f]

private theorem tensor_map_zero_right
    (R : Sheaf J CommRingCat.{u}) (K L : ringedSiteComplex R) :
    letI := SheafOfModules.monoidalCategory R
    HomologicalComplex.mapBifunctorMap (𝟙 K) (0 : L ⟶ L)
      (curriedTensor _) (.up ℤ) = 0 := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.tensorClosed R).1.some
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.zero_f]

private theorem ordered_scalar_nullhomotopy
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (R.obj ⋙ forget CommRingCat).sections) (n : ℕ) (j : Fin r) :
    Nonempty (Homotopy
      (((sectionScalarNat R ⟨(b j).val, (b j).property⟩ (n + 1)).mapHomologicalComplex
        (.up ℤ)).app ((ringedKoszulDiagram R r b).obj n)) 0) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.tensorClosed R).1.some
  induction r with
  | zero => exact Fin.elim0 j
  | succ r ih =>
    let K := ringedKoszulFactor R (b 0) n
    let L := (ringedKoszulDiagram R r (fun i ↦ b i.succ)).obj n
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · obtain ⟨h⟩ := factor_scalar_nullhomotopy R (b 0) n
      have ht := HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 L)
        (curriedTensor _) (.up ℤ)
      rw [sectionScalarNat_tensorComplex_left, tensor_map_zero_left] at ht
      exact ⟨ht⟩
    · obtain ⟨h⟩ := ih (fun i ↦ b i.succ) k
      have ht := HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K) h
        (curriedTensor _) (.up ℤ)
      rw [sectionScalarNat_tensorComplex_right, tensor_map_zero_right] at ht
      exact ⟨ht⟩

/-- A uniform positive ideal power annihilates the homology of an ordered Koszul stage.
Source: Stacks Project, More on Algebra, Tags 0626 and 0913.
(auxiliary; not a blueprint node).

Proof: multiplication by a generator to exponent n+1 contracts its two-term factor.
Tensor that homotopy with the other factors, with the total-complex signs. Naturality
of scalar multiplication on cycles and homology makes the induced scalar map zero.
An ideal generated by r elements whose (n+1)-st powers kill a module has its
(r*(n+1)+1)-st power contained in the annihilator, by induction on the generators.
The empty generating family gives the zero ideal to the first power. -/
theorem ordered_koszul_ideal_power_annihilates_homology
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (R.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    ∀ (q : ℤ) (X : Cᵒᵖ) (a : R.obj.obj X),
      a ∈ (Ideal.span (Set.range (fun j : Fin r ↦ (b j).val X))) ^
        (r * (n + 1) + 1) →
      ∀ x : (((ringedKoszulDiagram R r b).obj n).homology q).val.obj X,
        a • x = 0 := by
  intro q X a ha x
  let K := (ringedKoszulDiagram R r b).obj n
  let A := Module.annihilator (R.obj.obj X) ((K.homology q).val.obj X)
  have hgen : ∀ j ∈ (Finset.univ : Finset (Fin r)), (b j).val X ^ (n + 1) ∈ A := by
    intro j _
    apply Module.mem_annihilator.mpr
    intro y
    obtain ⟨h⟩ := ordered_scalar_nullhomotopy R r b n j
    have he := scalarNat_homology
      (sectionScalarNat R ⟨(b j).val, (b j).property⟩ (n + 1)) K
      (End.of (((sectionScalarNat R ⟨(b j).val, (b j).property⟩ (n + 1)).mapHomologicalComplex
        (.up ℤ)).app K)) (fun _ ↦ rfl) q
    have hz := he.symm.trans (h.homologyMap_eq q)
    rw [HomologicalComplex.homologyMap_zero] at hz
    exact congrArg (fun t : K.homology q ⟶ K.homology q ↦ t.val.app X y) hz
  have hh : (Ideal.span (Set.range (fun j ↦ (b j).val X))) ^ (r * (n + 1) + 1) ≤ A := by
    simpa using span_pow_le_of_generator_powers Finset.univ
      (fun j ↦ (b j).val X) (n + 1) A hgen
  exact Module.mem_annihilator.mp (hh ha) x

end CategoryTheory
