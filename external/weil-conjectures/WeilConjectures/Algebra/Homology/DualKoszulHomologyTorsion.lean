/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.AlgebraicGeometry.OrderedKoszulHomologyTorsion
import all WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality

/-! # Boundedness and torsion of dual Koszul homology

Source: Stacks Project, Tags 0913 and 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open SheafOfModules.LocalizationCech
namespace CategoryTheory

private theorem negative_double_scalar_nullhomotopy
    {A : Type*} [Category A] [Abelian A] (z : 𝟭 A ⟶ 𝟭 A) (P : A) :
    Nonempty (Homotopy ((z.mapHomologicalComplex (.up ℤ)).app
      (HomologicalComplex.double (z.app P) (by decide : (ComplexShape.up ℤ).Rel (-1) 0))) 0) := by
  let K := HomologicalComplex.double (z.app P) (by decide : (ComplexShape.up ℤ).Rel (-1) 0)
  let h (i j : ℤ) : K.X i ⟶ K.X j :=
    if hi : i = 0 then if hj : j = -1 then
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
    by_cases h0 : i = -1
    · subst i
      simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.zero_f]
      apply (cancel_mono (HomologicalComplex.doubleXIso₀ (z.app P)
        (by decide : (ComplexShape.up ℤ).Rel (-1) 0)).hom).1
      simpa [dNext, prevD, h, K, HomologicalComplex.double_d, Category.assoc] using
        (z.naturality (HomologicalComplex.doubleXIso₀ (z.app P)
          (by decide : (ComplexShape.up ℤ).Rel (-1) 0)).hom).symm
    · by_cases h1 : i = 0
      · subst i
        simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.zero_f]
        apply (cancel_mono (HomologicalComplex.doubleXIso₁ (z.app P)
          (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).hom).1
        simpa [dNext, prevD, h, K, HomologicalComplex.double_d, Category.assoc] using
          (z.naturality (HomologicalComplex.doubleXIso₁ (z.app P)
            (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).hom).symm
      · exact (HomologicalComplex.isZero_double_X (z.app P)
          (by decide : (ComplexShape.up ℤ).Rel (-1) 0) i h0 h1).eq_of_src _ _

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

private theorem negative_factor_scalar_nullhomotopy
    (R : Sheaf J CommRingCat.{u})
    (b : (R.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    Nonempty (Homotopy
      (((sectionScalarNat R ⟨b.val, b.property⟩ (n + 1)).mapHomologicalComplex
        (.up ℤ)).app (ringedNegativeKoszulFactor R b n)) 0) := by
  have he : (sectionScalarNat R ⟨b.val, b.property⟩ (n + 1)).app
      (SheafOfModules.unit (rings R)) = (ringedKoszulScalar R b ^ (n + 1)).asHom :=
    sectionScalarNat_unit R ⟨b.val, b.property⟩ (n + 1)
  unfold ringedNegativeKoszulFactor
  rw [← he]
  exact negative_double_scalar_nullhomotopy _ _

private theorem negative_ordered_scalar_nullhomotopy
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (R.obj ⋙ forget CommRingCat).sections) (n : ℕ) (j : Fin r) :
    Nonempty (Homotopy
      (((sectionScalarNat R ⟨(b j).val, (b j).property⟩ (n + 1)).mapHomologicalComplex
        (.up ℤ)).app ((ringedNegativeKoszul R r b) n)) 0) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.tensorClosed R).1.some
  induction r with
  | zero => exact Fin.elim0 j
  | succ r ih =>
    let K := ringedNegativeKoszulFactor R (b 0) n
    let L := (ringedNegativeKoszul R r (fun i ↦ b i.succ)) n
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · obtain ⟨h⟩ := negative_factor_scalar_nullhomotopy R (b 0) n
      have ht := HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 L)
        (curriedTensor _) (.up ℤ)
      rw [sectionScalarNat_tensorComplex_left, tensor_map_zero_left] at ht
      exact ⟨ht⟩
    · obtain ⟨h⟩ := ih (fun i ↦ b i.succ) k
      have ht := HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K) h
        (curriedTensor _) (.up ℤ)
      rw [sectionScalarNat_tensorComplex_right, tensor_map_zero_right] at ht
      exact ⟨ht⟩

private theorem negative_koszul_torsion
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (R.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    ∀ (q : ℤ) (X : Cᵒᵖ) (a : R.obj.obj X),
      a ∈ (Ideal.span (Set.range (fun j : Fin r ↦ (b j).val X))) ^
        (r * (n + 1) + 1) →
      ∀ x : ((ringedNegativeKoszul R r b n).homology q).val.obj X,
        a • x = 0 := by
  intro q X a ha x
  let K := (ringedNegativeKoszul R r b) n
  let A := Module.annihilator (R.obj.obj X) ((K.homology q).val.obj X)
  have hgen : ∀ j ∈ (Finset.univ : Finset (Fin r)), (b j).val X ^ (n + 1) ∈ A := by
    intro j _
    apply Module.mem_annihilator.mpr
    intro y
    obtain ⟨h⟩ := negative_ordered_scalar_nullhomotopy R r b n j
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

private theorem positive_koszul_above
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (m : ℕ) (n : ℤ) (hn : (r : ℤ) < n) :
    IsZero (((ringedKoszulDiagram R r b).obj m).X n) := by
  induction r generalizing n with
  | zero =>
    exact HomologicalComplex.isZero_single_obj_X _ _ _ n (ne_of_gt hn)
  | succ r ih =>
    exact ((biprod_isZero_iff _ _).2
      ⟨ih (fun i ↦ b i.succ) n (by omega),
        ih (fun i ↦ b i.succ) (n - 1) (by omega)⟩).of_iso
          (koszulTensorXIso R (b 0) m _ n)

/-- The dual Koszul stage is supported in [-r,0], and its homology is annihilated
by the displayed power of the ideal generated by its sections.

Source: Stacks Project, more-algebra.tex, Tag 0913, and algebraization.tex, Tag 0A0E.
(auxiliary; not a blueprint node).

Proof: contract multiplication by b_i^(n+1) on its negative two-term factor and
extend the contraction across the remaining ordered tensor factors. The scalar
endomorphism on homology is therefore zero. The finite-generator pigeonhole lemma
puts the (r*(n+1)+1)-st ideal power in the annihilator. The finite-free duality
isomorphism transports this to the actual internal dual. Its degree i term is
Hom from the positive term in degree -i into R, so the positive support [0,r]
gives the stated support. The empty tensor and zero ring satisfy the same proof. -/
theorem dualKoszul_bounded_torsion
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (R.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    (∀ i : ℤ, i < -(r : ℤ) ∨ 0 < i →
      IsZero (((ringedKoszulDualTower R r b).obj (op n)).X i)) ∧
    (∀ (q : ℤ) (X : Cᵒᵖ) (a : R.obj.obj X),
      a ∈ (Ideal.span (Set.range (fun j : Fin r ↦ (b j).val X))) ^
        (r * (n + 1) + 1) →
      ∀ x : ((((ringedKoszulDualTower R r b).obj (op n)).homology q).val.obj X),
        a • x = 0) := by
  constructor
  · intro i hi
    have hz : IsZero (((ringedKoszulDiagram R r b).obj n).X (-i)) := by
      rcases hi with hi | hi
      · exact positive_koszul_above R r b n (-i) (by omega)
      · exact koszulDiagram_nonneg R r b n (-i) (by omega)
    exact ((((SheafOfModules.homFunctor R).flip.obj (SheafOfModules.unit _)).map_isZero
      hz.op)).of_iso (homSingleXIso R _ i)
  · have hd : ∃ e : ringedNegativeKoszul R r b n ≅
        (ringedKoszulDualTower R r b).obj (op n), True := by
      cases r with
      | zero =>
        obtain ⟨e, _, _⟩ := ringedNegativeKoszulZeroDuality R b
        exact ⟨e n, trivial⟩
      | succ r =>
        obtain ⟨e, _, _⟩ := ringedNegativeKoszulSuccDuality R r b
        exact ⟨e n, trivial⟩
    obtain ⟨e, _⟩ := hd
    intro q X a ha x
    let d := (HomologicalComplex.homologyFunctor _ (.up ℤ) q).mapIso e
    let f := d.hom.val.app X
    let g := d.inv.val.app X
    have hg : f (g x) = x := by
      change ((d.inv ≫ d.hom).val.app X) x = x
      rw [d.inv_hom_id]
      rfl
    rw [← hg, ← f.hom.map_smul]
    rw [negative_koszul_torsion R r b n q X a ha (g x), map_zero]

end CategoryTheory
