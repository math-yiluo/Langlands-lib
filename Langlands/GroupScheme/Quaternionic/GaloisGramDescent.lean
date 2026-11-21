import Langlands.Algebra.GaloisAlgebraDescent
import Langlands.GroupScheme.Quaternionic.AntihermitianSplitRankUpper
import Langlands.GroupScheme.Quaternionic.SymplecticAffineCoordinates
import Langlands.GroupScheme.Rational.CentralSimpleNormOneCocycle

/-! # The descended Gram matrix of a symplectic cocycle -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Matrix
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

section Transform

variable {F A : Type u} [CommRing F] [Ring A] [Algebra F A] (τ : FirstKindInvolution F A)

/-- Gram congruence by a unit and its adjoint. -/
def gramTransform (p : Aˣ) (H : A) : A := (p : A) * H * τ p

theorem gramTransform_mul (p q : Aˣ) (H : A) :
    τ.gramTransform (p * q) H = τ.gramTransform p (τ.gramTransform q H) := by
  simp only [gramTransform, Units.val_mul, τ.map_mul, mul_assoc]

@[simp] theorem gramTransform_one (H : A) : τ.gramTransform 1 H = H := by
  simp [gramTransform]

theorem involution_gramTransform (p : Aˣ) (H : A) :
    τ (τ.gramTransform p H) = τ.gramTransform p (τ H) := by
  simp only [gramTransform, τ.map_mul, τ.apply_apply, mul_assoc]

@[simp] theorem gramTransform_neg (p : Aˣ) (H : A) :
    τ.gramTransform p (-H) = -τ.gramTransform p H := by
  simp [gramTransform]

theorem isUnit_gramTransform (p : Aˣ) {H : A} (hH : IsUnit H) :
    IsUnit (τ.gramTransform p H) := by
  have h : IsUnit (τ (p : A)) := by
    refine ⟨⟨τ p, τ (p⁻¹ : Aˣ), ?_, ?_⟩, rfl⟩
    · rw [← τ.map_mul, Units.inv_mul, τ.map_one]
    · rw [← τ.map_mul, Units.mul_inv, τ.map_one]
  exact (p.isUnit.mul hH).mul h

variable {R S : Type u} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

theorem map_gramTransform (f : R →ₐ[F] S) (p : (R ⊗[F] A)ˣ) (H : R ⊗[F] A) :
    Algebra.TensorProduct.map f (AlgHom.id F A) ((τ.baseChange R).gramTransform p H) =
      (τ.baseChange S).gramTransform
        (Units.map (Algebra.TensorProduct.map f (AlgHom.id F A)).toMonoidHom p)
        (Algebra.TensorProduct.map f (AlgHom.id F A) H) := by
  let m := Algebra.TensorProduct.map f (AlgHom.id F A)
  change m ((p : R ⊗[F] A) * H * τ.baseChange R p) =
    m p * m H * τ.baseChange S (m p)
  rw [_root_.map_mul, _root_.map_mul, τ.map_baseChange]

end Transform

open GaloisPoint Langlands.GaloisAlgebraDescent

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
  {n : ℕ} [NeZero n] (H : Matrix (Fin n) (Fin n) D)

local notation "A" => Matrix (Fin n) (Fin n) D
local notation "U" => CentralSimpleUnits.groupScheme F A
local notation "G" => σ.symplecticGroup H
local notation "Rₐ" R => CommAlgCat.of F R
local notation "unitEquiv[" R "]" => FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (Rₐ R)
local notation "τ" => σ.matrix (Fin n)

variable {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

omit [Algebra.IsCentral F D] [NeZero n] [FiniteDimensional F L] [IsGalois F L] in
private theorem tensorUnit_conjugate (s : L ≃ₐ[F] L) (b : (U).affinePoints (Rₐ L)) :
    unitEquiv[L] (conjugate F L U s b) =
      Units.map (coefficientConjugate F L A s).toMonoidHom (unitEquiv[L] b) :=
  FiniteAlgebraUnits.affinePointsEquiv_naturality _ (CommAlgCat.ofHom s.toAlgHom) b

omit [Algebra.IsCentral F D] [NeZero n] [FiniteDimensional F L] [IsGalois F L] in
private theorem tensorUnit_extend (b : (U).affinePoints (Rₐ F)) :
    (unitEquiv[L] (extend F L U b) : L ⊗[F] A) =
      (1 : L) ⊗ₜ[F] Algebra.TensorProduct.lid F A (unitEquiv[F] b : F ⊗[F] A) := by
  let e := Algebra.TensorProduct.lid F A
  let f := Algebra.TensorProduct.map (Algebra.ofId F L) (AlgHom.id F A)
  have h := congrArg Units.val
    (FiniteAlgebraUnits.affinePointsEquiv_naturality _ (CommAlgCat.ofHom (Algebra.ofId F L)) b)
  change (unitEquiv[L] (extend F L U b) : L ⊗[F] A) = f (unitEquiv[F] b : F ⊗[F] A) at h
  calc
    _ = f (unitEquiv[F] b : F ⊗[F] A) := h
    _ = f (e.symm (e (unitEquiv[F] b : F ⊗[F] A))) := congrArg f (e.symm_apply_apply _).symm
    _ = _ := by
      change Algebra.TensorProduct.map (Algebra.ofId F L) (AlgHom.id F A)
        ((1 : F) ⊗ₜ[F] e (unitEquiv[F] b : F ⊗[F] A)) = _
      rw [Algebra.TensorProduct.map_tmul, _root_.map_one, AlgHom.id_apply]

/-- An ambient cocycle primitive with its descended antihermitian Gram matrix. -/
structure SymplecticGramDescent (ξ : Cocycle G (GaloisCocycle.cover F L)) where
  primitive : (U).affinePoints (Rₐ L)
  gram : A
  gram_antihermitian : σ.IsAntihermitian gram
  gram_unit : IsUnit gram
  coboundary : ∀ s : L ≃ₐ[F] L,
    (G).affinePointsTarget (σ.symplecticAmbientι H) (Rₐ L) (GaloisCocycle.value ξ s) =
      primitive * (conjugate F L U s primitive)⁻¹
  tensor_gram : ((τ).baseChange L).gramTransform ((unitEquiv[L] primitive)⁻¹) (1 ⊗ₜ[F] H) = 1 ⊗ₜ[F] gram

variable [Infinite F] [Invertible (2 : F)]

/-- Noncommutative Hilbert 90 and descent of the fixed twisted Gram matrix. -/
theorem exists_symplecticGramDescent
    (hσ : Module.finrank F σ.symmetricSubspace =
      Langlands.CentralSimple.reducedDegree F D * (Langlands.CentralSimple.reducedDegree F D + 1) / 2)
    (hH : σ.IsAntihermitian H) (hu : IsUnit H) (ξ : Cocycle G (GaloisCocycle.cover F L)) :
    Nonempty (σ.SymplecticGramDescent H ξ) := by
  let j := σ.symplecticAmbientι H
  let q := AntihermitianSplitRank.toNormOne σ H
  let i := CentralSimpleUnits.normOneι F A
  obtain ⟨b, _, hb, _⟩ := CentralSimpleUnits.exists_cocycle_primitive (ξ.map q)
  have hb' (s : L ≃ₐ[F] L) : (G).affinePointsTarget j (Rₐ L) (GaloisCocycle.value ξ s) =
      b * (conjugate F L U s b)⁻¹ := by
    have h := hb s
    change (GaloisCocycle.value ξ s ≫ q.hom.hom) ≫ i.hom.hom = _ at h
    rw [Category.assoc, ← Grp.comp_hom_hom, AntihermitianSplitRank.toNormOne_comp] at h
    exact h
  let p := unitEquiv[L] b
  let Hₗ : L ⊗[F] A := 1 ⊗ₜ[F] H
  let T := ((τ).baseChange L).gramTransform p⁻¹ Hₗ
  have hfixed (s : L ≃ₐ[F] L) : coefficientConjugate F L A s T = T := by
    let c := unitEquiv[L] ((G).affinePointsTarget j (Rₐ L) (GaloisCocycle.value ξ s))
    have hc : ((τ).baseChange L).gramTransform c Hₗ = Hₗ := by
      apply sub_eq_zero.mp
      apply (σ.mem_range_symplecticAmbientι_affine_iff H hσ hH hu (Rₐ L) _).mp
      exact SubgroupFunctor.mem_range.mpr ⟨GaloisCocycle.value ξ s, rfl⟩
    let f := coefficientConjugate F L A s
    have hs : c = p * (Units.map f.toMonoidHom p)⁻¹ := by
      change unitEquiv[L] ((G).affinePointsTarget j (Rₐ L) (GaloisCocycle.value ξ s)) = _
      rw [hb', _root_.map_mul, _root_.map_inv, tensorUnit_conjugate]
    have he : Units.map f.toMonoidHom (p⁻¹) = p⁻¹ * c := by
      rw [_root_.map_inv, hs, ← mul_assoc, inv_mul_cancel, one_mul]
    change f (((τ).baseChange L).gramTransform p⁻¹ Hₗ) = _
    have hHₗ : f Hₗ = Hₗ := by simp [f, Hₗ]
    have hmap := map_gramTransform τ s.toAlgHom p⁻¹ Hₗ
    change f T = ((τ).baseChange L).gramTransform (Units.map f.toMonoidHom p⁻¹) (f Hₗ) at hmap
    rw [hmap, he, hHₗ, gramTransform_mul, hc]
  have hT : IsUnit T := ((τ).baseChange L).isUnit_gramTransform _
    (hu.map (Algebra.TensorProduct.includeRight : A →ₐ[F] L ⊗[F] A))
  let t := hT.unit
  have ht : (t : L ⊗[F] A) = T := hT.unit_spec
  let x := (unitEquiv[L]).symm t
  have hx (s : L ≃ₐ[F] L) : conjugate F L U s x = x := by
    apply (unitEquiv[L]).injective
    rw [tensorUnit_conjugate, MulEquiv.apply_symm_apply]
    apply Units.ext
    change coefficientConjugate F L A s (t : L ⊗[F] A) = t
    rw [ht, hfixed]
  let z : fixedSubgroup F L U := ⟨x, hx⟩
  let a := (fixedEquiv F L U).symm z
  let H' := Algebra.TensorProduct.lid F A (unitEquiv[F] a : F ⊗[F] A)
  have ha : (1 : L) ⊗ₜ[F] H' = T := by
    rw [← tensorUnit_extend (L := L) a, extend_fixedEquiv_symm]
    change (unitEquiv[L] ((unitEquiv[L]).symm t) : L ⊗[F] A) = T
    rw [MulEquiv.apply_symm_apply, ht]
  have hskew : τ H' = -H' := by
    apply Algebra.TensorProduct.includeRight_injective (B := A) (algebraMap F L).injective
    change (1 : L) ⊗ₜ[F] τ H' = (1 : L) ⊗ₜ[F] (-H')
    rw [← baseChange_tmul, TensorProduct.tmul_neg, ha]
    change ((τ).baseChange L) (((τ).baseChange L).gramTransform p⁻¹ Hₗ) =
      -((τ).baseChange L).gramTransform p⁻¹ Hₗ
    rw [involution_gramTransform, show ((τ).baseChange L) Hₗ = -Hₗ by
      rw [show Hₗ = 1 ⊗ₜ[F] H from rfl, baseChange_tmul, hH.1, TensorProduct.tmul_neg],
      gramTransform_neg]
  have hanti : σ.IsAntihermitian H' := by
    refine ⟨hskew, fun k => ?_⟩
    have hdiag : σ (H' k k) = -H' k k := congrFun (congrFun hskew k) k
    refine σ.mem_alternatingSubspace.mpr ⟨(⅟(2 : F)) • H' k k, ?_⟩
    rw [σ.map_smul, hdiag, smul_neg, sub_neg_eq_add, invOf_two_smul_add_invOf_two_smul]
  exact ⟨⟨b, H', hanti, (unitEquiv[F] a).isUnit.map (Algebra.TensorProduct.lid F A), hb', ha.symm⟩⟩

/-- Choose an ambient primitive together with its descended Gram matrix. -/
def symplecticGramDescent
    (hσ : Module.finrank F σ.symmetricSubspace =
      Langlands.CentralSimple.reducedDegree F D * (Langlands.CentralSimple.reducedDegree F D + 1) / 2)
    (hH : σ.IsAntihermitian H) (hu : IsUnit H) (ξ : Cocycle G (GaloisCocycle.cover F L)) :
    σ.SymplecticGramDescent H ξ :=
  Classical.choice (σ.exists_symplecticGramDescent H hσ hH hu ξ)

omit [Infinite F] [Invertible (2 : F)] in
/-- A ground-field Gram congruence corrects the primitive on the original cover. -/
theorem SymplecticGramDescent.isTrivial_of_gramTransform
    (hσ : Module.finrank F σ.symmetricSubspace =
      Langlands.CentralSimple.reducedDegree F D * (Langlands.CentralSimple.reducedDegree F D + 1) / 2)
    (hH : σ.IsAntihermitian H) (hu : IsUnit H) {ξ : Cocycle G (GaloisCocycle.cover F L)}
    (d : σ.SymplecticGramDescent H ξ) (P : Aˣ) (hP : (τ).gramTransform P H = d.gram) :
    ξ.IsTrivial := by
  let a := (unitEquiv[F]).symm (Units.map (Algebra.TensorProduct.lid F A).symm.toMonoidHom P)
  let r := extend F L U a
  have hr : (unitEquiv[L] r : L ⊗[F] A) = (1 : L) ⊗ₜ[F] (P : A) := by
    change (unitEquiv[L] (extend F L U a) : L ⊗[F] A) = _
    rw [tensorUnit_extend (L := L) a]
    change (1 : L) ⊗ₜ[F] (Algebra.TensorProduct.lid F A) ((unitEquiv[F])
      ((unitEquiv[F]).symm (Units.map (Algebra.TensorProduct.lid F A).symm.toMonoidHom P)) : F ⊗[F] A)
      = _
    rw [MulEquiv.apply_symm_apply]
    change (1 : L) ⊗ₜ[F] (Algebra.TensorProduct.lid F A)
      ((Algebra.TensorProduct.lid F A).symm (P : A)) = _
    rw [AlgEquiv.apply_symm_apply]
  have hrGram : ((τ).baseChange L).gramTransform (unitEquiv[L] r) (1 ⊗ₜ[F] H) =
      1 ⊗ₜ[F] d.gram := by
    rw [gramTransform, hr, baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
    exact congrArg (fun H' => (1 : L) ⊗ₜ[F] H') hP
  let t := d.primitive * r
  have ht : ((τ).baseChange L).gramTransform (unitEquiv[L] t) (1 ⊗ₜ[F] H) = 1 ⊗ₜ[F] H := by
    change ((τ).baseChange L).gramTransform (unitEquiv[L] (d.primitive * r)) (1 ⊗ₜ[F] H) = _
    rw [_root_.map_mul, gramTransform_mul, hrGram, ← d.tensor_gram,
      ← gramTransform_mul, mul_inv_cancel, gramTransform_one]
  let j := σ.symplecticAmbientι H
  have hx := (σ.mem_range_symplecticAmbientι_affine_iff H hσ hH hu (Rₐ L) t).mpr
    (sub_eq_zero.mpr ht)
  obtain ⟨f, hf⟩ := SubgroupFunctor.mem_range.mp hx
  refine (GaloisCocycle.isTrivial_iff ξ).2 ⟨f, fun s => ?_⟩
  apply (cancel_mono j.hom.hom).mp
  let J := (G).affinePointsTarget j (Rₐ L)
  change J (GaloisCocycle.value ξ s) = J (f * (conjugate F L G s f)⁻¹)
  have hj : J (conjugate F L G s f) = conjugate F L U s (J f) := by
    change (GaloisCocycle.arrow F L s ≫ f) ≫ j.hom.hom =
      GaloisCocycle.arrow F L s ≫ (f ≫ j.hom.hom)
    exact Category.assoc _ _ _
  have hf' : J f = t := hf
  rw [d.coboundary, _root_.map_mul, _root_.map_inv, hj, hf']
  change d.primitive * (conjugate F L U s d.primitive)⁻¹ =
    (d.primitive * r) * (conjugate F L U s (d.primitive * r))⁻¹
  rw [_root_.map_mul, show conjugate F L U s r = r from conjugate_extend F L U s a]
  group

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
