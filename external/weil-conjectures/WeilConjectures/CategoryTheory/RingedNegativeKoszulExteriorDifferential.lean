/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ExteriorKoszulBasisDifferential
public import WeilConjectures.CategoryTheory.SignedKoszulCompletionModel
import WeilConjectures.CategoryTheory.RingedNegativeKoszulSignedDifferential

/-! # Exterior coefficients of the canonical negative tensor differential

Source: Stacks Project, More on Algebra, Tags 0622 and 0664; Algebraization, Tag 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory

attribute [local irreducible] ringedKoszulScalar ringedNegativeKoszulFactor
  ringedNegativeKoszulBasis ringedNegativeKoszul

private theorem erase_orderEmb {r k : ℕ} (I : Finset (Fin r))
    (hI : I.card = k + 1) (i : Fin (k + 1)) :
    (fun j : Fin k ↦ I.orderEmbOfFin hI (i.succAbove j)) =
      (I.erase (I.orderEmbOfFin hI i)).orderEmbOfFin (by
        rw [Finset.card_erase_of_mem (I.orderEmbOfFin_mem hI i), hI]
        omega) := by
  apply Finset.orderEmbOfFin_unique
  · intro j
    simp only [Finset.mem_erase, ne_eq]
    exact ⟨fun h ↦ Fin.succAbove_ne i j ((I.orderEmbOfFin hI).injective h),
      I.orderEmbOfFin_mem hI _⟩
  · exact (I.orderEmbOfFin hI).strictMono.comp (Fin.strictMono_succAbove i)

private theorem earlier_card {r k : ℕ} (I : Finset (Fin r))
    (hI : I.card = k) (i : Fin k) :
    (I.filter (fun j ↦ j < I.orderEmbOfFin hI i)).card = i.val := by
  classical
  let e := I.orderEmbOfFin hI
  have he : I = Finset.univ.image e := (I.image_orderEmbOfFin_univ hI).symm
  let p : Fin r → Prop := fun j ↦ j < e i
  change (I.filter p).card = i.val
  rw [he, Finset.filter_image]
  simp only [p, e, (I.orderEmbOfFin hI).lt_iff_lt]
  rw [Finset.card_image_of_injective _ (I.orderEmbOfFin hI).injective]
  change (Finset.univ.filter (fun j : Fin k ↦ j < i)).card = i.val
  rw [show Finset.univ.filter (fun j : Fin k ↦ j < i) = Finset.Iio i by
    ext j; simp]
  exact Fin.card_Iio i

private theorem boundary_basis {A : Type w} [CommRing A] (r k : ℕ)
    (f : Fin r → A) (I : Set.powersetCard (Fin r) (k + 1)) :
    ExteriorAlgebra.koszulBoundary A r f k
        ((Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower
          (k + 1) I) =
      ∑ i : Fin (k + 1), ((-1 : A) ^ (i.val + 2) * f (I.1.orderEmbOfFin I.2 i)) •
        ((Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower k
          ⟨I.1.erase (I.1.orderEmbOfFin I.2 i), by
            change (I.1.erase _).card = k
            rw [Finset.card_erase_of_mem (I.1.orderEmbOfFin_mem I.2 i), I.2]
            omega⟩) := by
  classical
  let B : Module.Basis (Fin r) A (Fin r →₀ A) := Finsupp.basisSingleOne
  let v : Fin (k + 1) → (Fin r →₀ A) := fun i ↦ B (I.1.orderEmbOfFin I.2 i)
  obtain ⟨D, hD1, hrec, huniq, _, _, _, hf, _, _⟩ :=
    ExteriorAlgebra.koszul_differential A (Fin r →₀ A) (Finsupp.linearCombination A f)
  have hcontract : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A (Fin r →₀ A))) (Finsupp.linearCombination A f) = D := by
    apply huniq
    · exact CliffordAlgebra.contractLeft_one _ _
    · intro x y
      simpa only [Algebra.smul_def] using
        CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm A (Fin r →₀ A)))
          (Finsupp.linearCombination A f) x y
  have hform := hf k v
  have hv (i : Fin (k + 1)) : (Finsupp.linearCombination A f) (v i) =
      f (I.1.orderEmbOfFin I.2 i) := by simp [v, B]
  apply Subtype.ext
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin r →₀ A)))
      (Finsupp.linearCombination A f) _ = _
  simp only [Submodule.subtype_apply, exteriorPower.basis_apply, Submodule.coe_sum,
    Submodule.coe_smul, exteriorPower.ιMulti_family_apply_coe, ExteriorAlgebra.ιMulti_family,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rw [hcontract]
  change D (ExteriorAlgebra.ιMulti A (k + 1) v) = _
  rw [hform]
  simp only [hv, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have he := erase_orderEmb I.1 I.2 i
  change ExteriorAlgebra.ιMulti A k (v ∘ i.succAbove) =
    ExteriorAlgebra.ιMulti A k (B ∘ _)
  congr 1
  exact congrArg (B ∘ ·) he

private theorem coefficient_formula {A : Type w} [CommRing A] (r : ℕ)
    (f : Fin r → A) (q : ℤ) (I : exteriorKoszulIndex r q)
    (L : exteriorKoszulIndex r (q + 1)) :
    exteriorKoszulCoefficient r f q I L =
      ∑ i ∈ I.1, if I.1.erase i = L.1 then
        (-1 : A) ^ (I.1.filter (fun j ↦ j < i)).card * f i else 0 := by
  classical
  let k := L.1.card
  have hi : I.1.card = k + 1 := by have hI := I.2; have hL := L.2; dsimp [k]; omega
  have hq : ComplexShape.embeddingDownNat.f (k + 1) = q := by
    change -((k + 1 : ℕ) : ℤ) = q
    have hI := I.2
    omega
  have hq' : ComplexShape.embeddingDownNat.f k = q + 1 := L.2.symm
  have hb (j : ℕ) (hj : ComplexShape.embeddingDownNat.f j = q)
      (hI : I.1.card = j) : exteriorKoszulBasis r f q I =
      ModuleCat.ofHom ((LinearMap.id : A →ₗ[A] A).smulRight
        ((Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower
          j ⟨I.1, hI⟩)) ≫
        ((ExteriorAlgebra.koszulComplex A r f).extendXIso
          ComplexShape.embeddingDownNat hj).inv := by
    have he : j = (-q).toNat := by change -(j : ℤ) = q at hj; omega
    rcases he with rfl
    rfl
  have hp (j : ℕ) (hj : ComplexShape.embeddingDownNat.f j = q + 1)
      (hL : L.1.card = j) : exteriorKoszulCoordinate r f (q + 1) L =
      ((ExteriorAlgebra.koszulComplex A r f).extendXIso
          ComplexShape.embeddingDownNat hj).hom ≫
        ModuleCat.ofHom
          (((Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower
            j).coord ⟨L.1, hL⟩) := by
    have he : j = (-(q + 1)).toNat := by
      change -(j : ℤ) = q + 1 at hj
      omega
    rcases he with rfl
    rfl
  unfold exteriorKoszulCoefficient
  rw [hb (k + 1) hq hi, hp k hq' rfl]
  rw [HomologicalComplex.extend_d_eq _ _ hq hq']
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  have hd : (ExteriorAlgebra.koszulComplex A r f).d (k + 1) k =
      ModuleCat.ofHom (ExteriorAlgebra.koszulBoundary A r f k) := by
    dsimp only [ExteriorAlgebra.koszulComplex]
    exact ChainComplex.of_d _ _ k
  rw [hd]
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearMap.smulRight_apply, LinearMap.id_apply, one_smul]
  change (((Finsupp.basisSingleOne :
    Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower k).coord ⟨L.1, rfl⟩)
      (ExteriorAlgebra.koszulBoundary A r f k
        (((Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower
          (k + 1)) ⟨I.1, hi⟩)) = _
  rw [boundary_basis]
  simp only [map_sum, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]
  apply Finset.sum_bij (fun i _ ↦ I.1.orderEmbOfFin hi i)
  · intro i _
    exact I.1.orderEmbOfFin_mem hi i
  · intro i _ j _ hij
    exact (I.1.orderEmbOfFin hi).injective hij
  · intro i hi'
    obtain ⟨j, hj⟩ := (show i ∈ Set.range (I.1.orderEmbOfFin hi) from
      (I.1.range_orderEmbOfFin hi).symm ▸ hi')
    exact ⟨j, Finset.mem_univ j, hj⟩
  · intro i _
    rw [earlier_card I.1 hi i]
    have hsign : (-1 : A) ^ (i.val + 2) = (-1 : A) ^ i.val := by
      rw [pow_add, neg_one_sq, mul_one]
    simp only [hsign, smul_eq_mul]
    by_cases h : I.1.erase (I.1.orderEmbOfFin hi i) = L.1
    · simp [h]
    · simp [h, Subtype.ext_iff]

private theorem scalar_sum_comp
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) {A : Type w} [CommRing A]
    (ρ : A →+* End (SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)))
    {M : ringedSiteModules ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)}
    {r : ℕ} (I : Finset (Fin r)) (c : Fin r → A)
    (f : SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O) ⟶ M) :
    (ρ (∑ i ∈ I, c i)).asHom ≫ f = ∑ i ∈ I, (ρ (c i)).asHom ≫ f := by
  rw [map_sum, End.sum_asHom]
  exact Preadditive.sum_comp I (fun i ↦ (ρ (c i)).asHom) f

/-- The differential of a specified negative pure tensor has the actual exterior
contraction coefficients. This fixes every basis map in advance and concerns one
boundary of one negative tensor; there is no choice of coordinates or duality.

Source: Stacks Project, more-algebra.tex, Tags 0622 and 0664, contraction on ordered
wedges and the tensor Leibniz rule; algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, the finite free Koszul calculation.
(auxiliary; not a blueprint node).

Proof: use ringedNegativeKoszulBasis_signed_d for the canonical negative
basis, giving the signed sum over erased indices. Expand exterior contraction
on the increasing wedge using koszul_differential. Omitting its ith ordered
vector gives the increasing wedge on the erased subset, and its position equals
the number of earlier selected indices. The exterior coordinate projection takes
that wedge to one exactly for the erased subset and to zero otherwise. Hence
exteriorKoszulCoefficient is precisely the same signed finite sum. The ring
homomorphism preserves its sums, and composition distributes over them. Exchange
the two finite sums and sum the Kronecker coefficient over supported target
subsets. The result is the signed erased-index sum already proved for the
negative basis. No division or nonzero hypothesis is used; empty lists, zero
rings, empty sites, and zero or unit sections are included. -/
theorem ringedNegativeKoszulBasis_exterior_d
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) {A : Type w} [CommRing A]
    (ρ : A →+* End (SheafOfModules.unit
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj O)))
    (r : ℕ) (a : Fin r → A)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (hρ : ∀ i, ρ (a i) = ringedKoszulScalar O (s i))
    (n : ℕ) (q : ℤ) (I : exteriorKoszulIndex r q) :
    ringedNegativeKoszulBasis O r s n I.1 q ≫
        (ringedNegativeKoszul O r s n).d q (q + 1) =
      ∑ L : exteriorKoszulIndex r (q + 1),
        (ρ (exteriorKoszulCoefficient r (fun i ↦ a i ^ (n + 1)) q I L)).asHom ≫
          ringedNegativeKoszulBasis O r s n L.1 (q + 1) := by
  classical
  rw [ringedNegativeKoszulBasis_signed_d O ρ r a s hρ n q I]
  simp only [coefficient_formula, scalar_sum_comp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have he : q + 1 = -((I.1.erase i).card : ℤ) := by
    have hcard : (I.1.erase i).card = I.1.card - 1 := Finset.card_erase_of_mem hi
    have hI : q = -(I.1.card : ℤ) := I.2
    have hpos : 0 < I.1.card := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  symm
  rw [Finset.sum_eq_single ⟨I.1.erase i, he⟩]
  · simp only [ite_true]
  · intro L _ hL
    have hne : I.1.erase i ≠ L.1 := by
      intro h
      exact hL (Subtype.ext h.symm)
    simp only [ite_eq_right hne, map_zero, End.zero_asHom, zero_comp]
  · intro h
    exact (h (Finset.mem_univ _)).elim

end CategoryTheory
