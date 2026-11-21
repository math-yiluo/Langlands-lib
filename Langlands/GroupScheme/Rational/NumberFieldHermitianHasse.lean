import Langlands.GroupScheme.Rational.HermitianGaloisLocalGram

/-! # The Hasse kernel for special unitary groups of Hermitian matrices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root Quaternionic Quaternionic.FirstKindInvolution GaloisPoint
  Langlands.GaloisAlgebraDescent FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

section Trivialization

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] {n : ℕ}

local instance : FiniteDimensional F E :=
  .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)

local notation "A" => Matrix (Fin n) (Fin n) E
local notation "τ" => FirstKindInvolution.matrix (quadraticConjugationInvolution F E) (Fin n)
local notation "U" => ambientUnits F E n
local notation "Rₐ" R => CommAlgCat.of F R
local notation "unitEquiv[" R "]" => FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (Rₐ R)
local notation "matrixEquiv[" R "]" => affineMatrixEquiv F E (Module.finBasis F A) (Rₐ R)

variable {L : Type u} [Field L] [Algebra F L]

local notation "algebraInclusion" => (Algebra.TensorProduct.includeRight : A →ₐ[F] L ⊗[F] A)
local notation "fieldInclusion" => (Algebra.TensorProduct.includeRight : E →ₐ[F] L ⊗[F] E)

omit [Algebra.IsSeparable F E] in
private def includeUnitPoint (P : GL (Fin n) E) : (U).affinePoints (Rₐ L) :=
  (unitEquiv[L]).symm (Units.map (algebraInclusion).toMonoidHom P)

omit [Algebra.IsSeparable F E] in
private theorem unitEquiv_includeUnitPoint (P : GL (Fin n) E) :
    (unitEquiv[L]) (includeUnitPoint (F := F) (L := L) P) = Units.map (algebraInclusion).toMonoidHom P :=
  MulEquiv.apply_symm_apply _ _

omit [Algebra.IsSeparable F E] in
private theorem matrixEquiv_includeUnitPoint (P : GL (Fin n) E) :
    (matrixEquiv[L]) (includeUnitPoint (F := F) (L := L) P) = GeneralLinearGroup.map (fieldInclusion).toRingHom P := by
  apply Units.ext
  change coefficientEquiv F E L ((unitEquiv[L]) (includeUnitPoint (F := F) (L := L) P)).val = _
  rw [unitEquiv_includeUnitPoint]
  exact coefficientEquiv_one_tmul_eq_map L (P : A)

omit [Algebra.IsSeparable F E] in
private theorem conjugate_includeUnitPoint (P : GL (Fin n) E) (s : L ≃ₐ[F] L) :
    conjugate F L U s (includeUnitPoint P) = includeUnitPoint P := by
  apply (unitEquiv[L]).injective
  have h := FiniteAlgebraUnits.affinePointsEquiv_naturality (Module.finBasis F A)
    (CommAlgCat.ofHom s.toAlgHom) (includeUnitPoint (F := F) (L := L) P)
  change (unitEquiv[L]) (conjugate F L U s (includeUnitPoint P)) = _ at h
  rw [h, unitEquiv_includeUnitPoint]
  apply Units.ext
  change coefficientConjugate F L A s ((1 : L) ⊗ₜ[F] (P : A)) = _
  rw [coefficientConjugate_tmul, _root_.map_one]
  rfl

omit [Algebra.IsSeparable F E] in
private theorem conjugate_matrixEquiv (s : L ≃ₐ[F] L) (b : (U).affinePoints (Rₐ L)) :
    (matrixEquiv[L]) (conjugate F L U s b) =
      GeneralLinearGroup.map (coefficientConjugate F L E s).toRingHom ((matrixEquiv[L]) b) :=
  affineMatrixEquiv_naturality F E (Module.finBasis F A) (CommAlgCat.ofHom s.toAlgHom) b

variable {G : GroupScheme (Spec (CommRingCat.of F))} {H : Form (fieldInvolution F E) (Fin n)}
  (p : SchemeModel.Presentation F E H G)
  {ξ : Cocycle G (GaloisCocycle.cover F L)}

private theorem coboundary_mul_fixed {b : (U).affinePoints (Rₐ L)}
    (hb : ∀ s, toAmbient p L (GaloisCocycle.value ξ s) = b * (conjugate F L U s b)⁻¹)
    (r : (U).affinePoints (Rₐ L)) (hr : ∀ s, conjugate F L U s r = r) (s : L ≃ₐ[F] L) :
    toAmbient p L (GaloisCocycle.value ξ s) = (b * r) * (conjugate F L U s (b * r))⁻¹ := by
  rw [hb s, _root_.map_mul, hr s]
  group

variable [FiniteDimensional F L] [IsGalois F L]

private theorem exists_base_det (b : (U).affinePoints (Rₐ L))
    (hb : ∀ s, toAmbient p L (GaloisCocycle.value ξ s) = b * (conjugate F L U s b)⁻¹)
    (hpres : Preserves (SchemeModel.coefficientForm F E H (Rₐ L))
      ((matrixEquiv[L]) b : Matrix (Fin n) (Fin n) (L ⊗[F] E))) :
    ∃ a : Eˣ, (fieldInvolution F E).bar (a : E) * (a : E) = 1 ∧
      Units.map (fieldInclusion).toMonoidHom a = GeneralLinearGroup.det ((matrixEquiv[L]) b) := by
  let u := GeneralLinearGroup.det ((matrixEquiv[L]) b)
  have hfixed (s : L ≃ₐ[F] L) : coefficientConjugate F L E s (u : L ⊗[F] E) = u := by
    have h := congrArg (fun z => GeneralLinearGroup.det ((matrixEquiv[L]) z)) (hb s)
    change GeneralLinearGroup.det ((matrixEquiv[L]) (toAmbient p L (GaloisCocycle.value ξ s))) =
      GeneralLinearGroup.det ((matrixEquiv[L]) (b * (conjugate F L U s b)⁻¹)) at h
    rw [matrixEquiv_toAmbient p, _root_.map_mul, _root_.map_inv, _root_.map_mul, _root_.map_inv,
      conjugate_matrixEquiv s b, GeneralLinearGroup.map_det] at h
    have hd : GeneralLinearGroup.det (p.affineMatrixEquiv F E (Rₐ L) (GaloisCocycle.value ξ s)).val =
        1 := (p.affineMatrixEquiv F E (Rₐ L) (GaloisCocycle.value ξ s)).property.2
    rw [hd] at h
    exact congrArg Units.val (eq_of_mul_inv_eq_one h.symm).symm
  obtain ⟨a, ha⟩ := (mem_range_includeRight_iff F L E (u : L ⊗[F] E)).mpr hfixed
  change (fieldInclusion) a = ↑u at ha
  have hi : Function.Injective fieldInclusion :=
    Algebra.TensorProduct.includeRight_injective (B := E) (algebraMap F L).injective
  let : Nontrivial (L ⊗[F] E) := hi.nontrivial
  have ha' : a ≠ 0 := by
    intro h
    exact u.ne_zero (by rw [← ha, h, _root_.map_zero])
  let v := Units.mk0 a ha'
  refine ⟨v, ?_, Units.ext ha⟩
  apply hi
  rw [_root_.map_mul, _root_.map_one]
  have hc : fieldInclusion ((fieldInvolution F E).bar a) = (tensorInvolution F E L).bar (fieldInclusion a) := rfl
  change fieldInclusion ((fieldInvolution F E).bar a) * fieldInclusion a = 1
  rw [hc, ha]
  exact bar_det_mul_det_eq_one _ _ hpres

/-- A global Gram congruence and a line determinant correction give an actual
special unitary primitive on the original Galois cover. -/
theorem GaloisGramDescent.isTrivial_of_gramCongruence (hn : 0 < n) (d : GaloisGramDescent p ξ)
    (P : GL (Fin n) E) (hP : (τ).gramTransform P (H.inverse.gram : A) = d.gram.gram) : ξ.IsTrivial := by
  let r := includeUnitPoint (F := F) (L := L) P
  have hrGram : ((τ).baseChange L).gramTransform ((unitEquiv[L]) r) (1 ⊗ₜ[F] (H.inverse.gram : A)) =
      1 ⊗ₜ[F] (d.gram.gram : A) := by
    rw [unitEquiv_includeUnitPoint]
    change ((1 : L) ⊗ₜ[F] (P : A)) * (1 ⊗ₜ[F] (H.inverse.gram : A)) *
      ((τ).baseChange L) ((1 : L) ⊗ₜ[F] (P : A)) = _
    rw [baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, one_mul]
    exact congrArg (fun x : A => (1 : L) ⊗ₜ[F] x) hP
  let b := d.primitive * r
  have hb : ∀ s, toAmbient p L (GaloisCocycle.value ξ s) = b * (conjugate F L U s b)⁻¹ :=
    coboundary_mul_fixed p d.coboundary r (conjugate_includeUnitPoint P)
  have hpres : Preserves (SchemeModel.coefficientForm F E H (Rₐ L))
      ((matrixEquiv[L]) b : Matrix (Fin n) (Fin n) (L ⊗[F] E)) := by
    apply (gramTransform_iff_preserves H L b).mp
    change ((τ).baseChange L).gramTransform ((unitEquiv[L]) (d.primitive * r))
      ((1 : L) ⊗ₜ[F] (H.inverse.gram : A)) = (1 : L) ⊗ₜ[F] (H.inverse.gram : A)
    rw [_root_.map_mul, gramTransform_mul, hrGram, ← d.tensor_gram,
      ← gramTransform_mul, mul_inv_cancel, gramTransform_one]
  obtain ⟨a, ha, hdet⟩ := exists_base_det p b hb hpres
  obtain ⟨g, hg, hga⟩ := exists_unitary_det_eq hn H a ha
  let q := includeUnitPoint (F := F) (L := L) g⁻¹
  let w := b * q
  have hw : ∀ s, toAmbient p L (GaloisCocycle.value ξ s) = w * (conjugate F L U s w)⁻¹ :=
    coboundary_mul_fixed p hb q (conjugate_includeUnitPoint g⁻¹)
  have hq : Preserves (SchemeModel.coefficientForm F E H (Rₐ L))
      ((matrixEquiv[L]) q : Matrix (Fin n) (Fin n) (L ⊗[F] E)) := by
    rw [matrixEquiv_includeUnitPoint]
    exact preserves_map (fieldInclusion).toRingHom (fun _ => rfl) rfl (preserves_inv g hg)
  have hwPres : Preserves (SchemeModel.coefficientForm F E H (Rₐ L))
      ((matrixEquiv[L]) w : Matrix (Fin n) (Fin n) (L ⊗[F] E)) := by
    change Preserves _ ((matrixEquiv[L]) (b * q) : Matrix (Fin n) (Fin n) (L ⊗[F] E))
    rw [_root_.map_mul, Units.val_mul]
    exact preserves_mul hpres hq
  have hwDet : GeneralLinearGroup.det ((matrixEquiv[L]) w) = 1 := by
    change GeneralLinearGroup.det ((matrixEquiv[L]) (b * q)) = 1
    rw [_root_.map_mul, _root_.map_mul, matrixEquiv_includeUnitPoint, GeneralLinearGroup.map_det,
      _root_.map_inv, hga, _root_.map_inv, ← hdet]
    exact mul_inv_cancel (Units.map (fieldInclusion).toMonoidHom a)
  let e := p.affineMatrixEquiv F E (Rₐ L)
  let x := e.symm ⟨(matrixEquiv[L]) w, hwPres, hwDet⟩
  have hx : toAmbient p L x = w := by
    apply (matrixEquiv[L]).injective
    rw [matrixEquiv_toAmbient p]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨(matrixEquiv[L]) w, hwPres, hwDet⟩)
  refine (GaloisCocycle.isTrivial_iff ξ).mpr ⟨x, fun s => toAmbient_injective p L ?_⟩
  have hc : toAmbient p L (conjugate F L G s x) = conjugate F L U s (toAmbient p L x) :=
    toAmbient_naturality p s.toAlgHom x
  rw [_root_.map_mul, _root_.map_inv, hc, hx, hw]

end Trivialization

/-- The special unitary group of a nonsingular Hermitian matrix over a quadratic
extension of a number field has trivial Hasse kernel on every finite Galois cover. -/
def NumberFieldHermitianHasseStatement : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (n : ℕ), 0 < n → ∀ (H : Form (fieldInvolution F E) (Fin n))
      (G : GroupScheme (Spec (CommRingCat.of F))), SchemeModel.Presentation F E H G →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
        (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- Compare the descended inverse Gram matrix everywhere locally and apply
Hermitian local-to-global congruence. -/
theorem numberFieldHermitianHasse : NumberFieldHermitianHasseStatement.{u} := by
  intro F E _ _ _ _ _ _ n hn H G p L _ _ _ _ ξ hξ
  obtain ⟨d⟩ := exists_galoisGramDescent p ξ
  have hloc (v : Global.Place F) : GramCongruentOver F E H.inverse d.gram (Global.placeCompletion F v) := by
    rcases v with v | v
    · let : CharZero v.Completion := charZero_of_injective_algebraMap (algebraMap F v.Completion).injective
      exact d.gramCongruentOver_of_baseChange_isTrivial p (K := v.Completion) (hξ (.inl v))
    · let : CharZero (Global.FiniteCompletion F v) := charZero_of_injective_algebraMap
        (algebraMap F (Global.FiniteCompletion F v)).injective
      exact d.gramCongruentOver_of_baseChange_isTrivial p (K := Global.FiniteCompletion F v) (hξ (.inr v))
  obtain ⟨P, hP⟩ := numberFieldHermitianGramCongruence F E n H.inverse d.gram hloc
  exact d.isTrivial_of_gramCongruence p hn P hP

end Langlands.GroupScheme.HermitianMatrix
