import Langlands.GroupScheme.Examples.HermitianMatrixAffinePoints
import Langlands.GroupScheme.Examples.HermitianMatrixDeterminant
import Langlands.GroupScheme.Quaternionic.GaloisGramDescent
import Langlands.GroupScheme.Rational.NumberFieldHermitianGram

/-! # Descent of the Gram matrix of a Hermitian cocycle -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root Quaternionic Quaternionic.FirstKindInvolution
  GaloisPoint Langlands.GaloisAlgebraDescent FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] {n : ℕ}

local instance : FiniteDimensional F E :=
  .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)

local notation "S" => CommRingCat.of F
local notation "A" => Matrix (Fin n) (Fin n) E
local notation "τ" => FirstKindInvolution.matrix (quadraticConjugationInvolution F E) (Fin n)
local notation "σ" => quadraticConjugationInvolution F E
local notation "Rₐ" R => CommAlgCat.of F R
local notation "basisA" => Module.finBasis F A

/-- The actual unit group of the finite matrix algebra over the base field. -/
abbrev ambientUnits (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] (n : ℕ) : GroupScheme (Spec (CommRingCat.of F)) :=
  FiniteAlgebraUnits.groupScheme (Module.finBasis F (Matrix (Fin n) (Fin n) E))

local notation "U" => ambientUnits F E n
local notation "unitEquiv[" R "]" => FiniteAlgebraUnits.affinePointsEquiv basisA (Rₐ R)
local notation "matrixEquiv[" R "]" => affineMatrixEquiv F E basisA (Rₐ R)

variable {G : GroupScheme (Spec (CommRingCat.of F))}
  {H : Form (fieldInvolution F E) (Fin n)} (p : SchemeModel.Presentation F E H G)

/-- The affine matrix embedding of a Hermitian presentation into the finite-algebra units. -/
def toAmbient (R : Type u) [CommRing R] [Algebra F R] :
    G.affinePoints (Rₐ R) →* (U).affinePoints (Rₐ R) :=
  (matrixEquiv[R]).symm.toMonoidHom.comp
    ((specialUnitarySubgroup (SchemeModel.coefficientForm F E H (Rₐ R))).subtype.comp
      (p.affineMatrixEquiv F E (Rₐ R)).toMonoidHom)

@[simp] theorem matrixEquiv_toAmbient (R : Type u) [CommRing R] [Algebra F R]
    (x : G.affinePoints (Rₐ R)) :
    (matrixEquiv[R]) (toAmbient p R x) = (p.affineMatrixEquiv F E (Rₐ R) x).val :=
  MulEquiv.apply_symm_apply _ _

/-- The embedding is injective on every affine coefficient algebra. -/
theorem toAmbient_injective (R : Type u) [CommRing R] [Algebra F R] :
    Function.Injective (toAmbient p R) := by
  intro x y h
  apply (p.affineMatrixEquiv F E (Rₐ R)).injective
  apply Subtype.ext
  have hh := congrArg (fun z => (matrixEquiv[R]) z) h
  rw [matrixEquiv_toAmbient p R x, matrixEquiv_toAmbient p R y] at hh
  exact hh

/-- The affine embedding commutes with every change of coefficient algebra. -/
theorem toAmbient_naturality {R R' : Type u} [CommRing R] [CommRing R'] [Algebra F R] [Algebra F R']
    (f : R →ₐ[F] R') (x : G.affinePoints (Rₐ R)) :
    toAmbient p R' (G.affinePointMap (CommAlgCat.ofHom f) x) =
      (U).affinePointMap (CommAlgCat.ofHom f) (toAmbient p R x) := by
  apply (matrixEquiv[R']).injective
  rw [matrixEquiv_toAmbient]
  have h := affineMatrixEquiv_naturality F E basisA (CommAlgCat.ofHom f) (toAmbient p R x)
  change (matrixEquiv[R']) ((U).affinePointMap (CommAlgCat.ofHom f) (toAmbient p R x)) = _ at h
  rw [p.affineMatrixEquiv_naturality F E (CommAlgCat.ofHom f) x, h, matrixEquiv_toAmbient]
  rfl

private theorem baseChange_involution_agrees (R : Type u) [CommRing R] [Algebra F R]
    (x : R ⊗[F] E) : (σ).baseChange R x = (tensorInvolution F E R).bar x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

/-- Preservation of the Hermitian form is the row equation for the extended inverse Gram matrix. -/
theorem gramTransform_iff_preserves (H : Form (fieldInvolution F E) (Fin n))
    (R : Type u) [CommRing R] [Algebra F R] (b : (U).affinePoints (Rₐ R)) :
    ((τ).baseChange R).gramTransform ((unitEquiv[R]) b) (1 ⊗ₜ[F] (H.inverse.gram : A)) =
        1 ⊗ₜ[F] (H.inverse.gram : A) ↔
      Preserves (SchemeModel.coefficientForm F E H (Rₐ R))
        ((matrixEquiv[R]) b : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  rw [gramTransform, isometry_iff_coefficientEquiv σ R, preserves_iff_row_inverse]
  have hGram : ((SchemeModel.coefficientForm F E H (Rₐ R)).inverse.gram :
      Matrix (Fin n) (Fin n) (R ⊗[F] E)) = (H.inverse.gram : A).map
        (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) := by
    change ((GeneralLinearGroup.map _ H.gram)⁻¹ : GL (Fin n) (R ⊗[F] E)).val = _
    rw [← _root_.map_inv]
    rfl
  rw [hGram]
  have hm : ((σ).baseChange R).matrix (Fin n) (coefficientEquiv F E R ((unitEquiv[R]) b).val) =
      adjoint (tensorInvolution F E R) (coefficientEquiv F E R ((unitEquiv[R]) b).val) := by
    ext i j
    exact baseChange_involution_agrees R _
  rw [hm]
  rfl

@[simp] theorem gramTransform_toAmbient (R : Type u) [CommRing R] [Algebra F R]
    (x : G.affinePoints (Rₐ R)) :
    ((τ).baseChange R).gramTransform ((unitEquiv[R]) (toAmbient p R x))
      (1 ⊗ₜ[F] (H.inverse.gram : A)) = 1 ⊗ₜ[F] (H.inverse.gram : A) := by
  apply (gramTransform_iff_preserves H R _).mpr
  rw [matrixEquiv_toAmbient p]
  exact (p.affineMatrixEquiv F E (Rₐ R) x).property.1

section Galois

variable {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

omit [Algebra.IsSeparable F E] [FiniteDimensional F L] [IsGalois F L] in
private theorem unitEquiv_conjugate (s : L ≃ₐ[F] L) (x : (U).affinePoints (Rₐ L)) :
    (unitEquiv[L]) (conjugate F L U s x) =
      Units.map (coefficientConjugate F L A s).toMonoidHom ((unitEquiv[L]) x) :=
  FiniteAlgebraUnits.affinePointsEquiv_naturality _ (CommAlgCat.ofHom s.toAlgHom) x

omit [FiniteDimensional F L] [IsGalois F L] in
private def tensorAut : (L ≃ₐ[F] L) →* RingAut (L ⊗[F] A) where
  toFun s := (Algebra.TensorProduct.congr s (AlgEquiv.refl : A ≃ₐ[F] A)).toRingEquiv
  map_one' := by
    change (Algebra.TensorProduct.congr AlgEquiv.refl AlgEquiv.refl).toRingEquiv = _
    rw [Algebra.TensorProduct.congr_refl]
    rfl
  map_mul' s t := by
    change (Algebra.TensorProduct.congr (t.trans s) (AlgEquiv.refl : A ≃ₐ[F] A)).toRingEquiv = _
    rw [show (AlgEquiv.refl : A ≃ₐ[F] A) = AlgEquiv.refl.trans AlgEquiv.refl from rfl,
      Algebra.TensorProduct.congr_trans]
    rfl

set_option maxHeartbeats 2400000 in
omit [IsGalois F L] in
private theorem exists_ambient_coboundary [Infinite F] (ξ : Cocycle G (GaloisCocycle.cover F L)) :
    ∃ b : (U).affinePoints (Rₐ L), ∀ s : L ≃ₐ[F] L,
      toAmbient p L (GaloisCocycle.value ξ s) = b * (conjugate F L U s b)⁻¹ := by
  let c₀ (s : L ≃ₐ[F] L) := toAmbient p L (GaloisCocycle.value ξ s)
  let c (s : L ≃ₐ[F] L) := (unitEquiv[L]) (c₀ s)
  let B : Subgroup (L ≃ₐ[F] L) := ⊤
  have hc₀ (s t : L ≃ₐ[F] L) : c₀ (s * t) = c₀ s * conjugate F L U s (c₀ t) := by
    change toAmbient p L (GaloisCocycle.value ξ (s * t)) = _
    rw [GaloisCocycle.value_mul ξ s t, _root_.map_mul]
    congr 1
    exact toAmbient_naturality p s.toAlgHom (GaloisCocycle.value ξ t)
  have hc₁ : c 1 = 1 := by
    have hval := hc₀ 1 1
    rw [one_mul, conjugate_one] at hval
    have h₁ := mul_left_cancel (hval.symm.trans (mul_one _).symm)
    change (unitEquiv[L]) (c₀ 1) = 1
    rw [h₁, _root_.map_one]
  have hc (s t : L ≃ₐ[F] L) : c (s * t) = c s * Units.map (tensorAut (n := n) s).toMonoidHom (c t) := by
    change (unitEquiv[L]) (c₀ (s * t)) = _
    rw [hc₀, _root_.map_mul, unitEquiv_conjugate]
    rfl
  obtain ⟨b, hb⟩ := Langlands.Algebra.exists_unit_coboundary B
    ((tensorAut (n := n)).comp B.subtype) (fun s => coefficientConjugate_smul F L A s.val)
    (fun s => c s.val) hc₁ (fun s t => hc s.val t.val)
  refine ⟨(unitEquiv[L]).symm b, fun s => (unitEquiv[L]).injective ?_⟩
  rw [_root_.map_mul, _root_.map_inv, unitEquiv_conjugate, MulEquiv.apply_symm_apply]
  exact eq_mul_inv_of_mul_eq (hb ⟨s, Subgroup.mem_top s⟩)

/-- A unit primitive and the actual descended inverse Gram form of a Hermitian cocycle. -/
structure GaloisGramDescent (ξ : Cocycle G (GaloisCocycle.cover F L)) where
  primitive : (U).affinePoints (Rₐ L)
  gram : Form (fieldInvolution F E) (Fin n)
  coboundary : ∀ s : L ≃ₐ[F] L,
    toAmbient p L (GaloisCocycle.value ξ s) = primitive * (conjugate F L U s primitive)⁻¹
  tensor_gram : ((τ).baseChange L).gramTransform (((unitEquiv[L]) primitive)⁻¹)
    (1 ⊗ₜ[F] (H.inverse.gram : A)) = 1 ⊗ₜ[F] (gram.gram : A)

variable [Infinite F]

/-- Finite-algebra Hilbert 90 produces a primitive whose twisted Gram matrix descends. -/
theorem exists_galoisGramDescent (ξ : Cocycle G (GaloisCocycle.cover F L)) :
    Nonempty (GaloisGramDescent p ξ) := by
  obtain ⟨b, hb⟩ := exists_ambient_coboundary p ξ
  let q := (unitEquiv[L]) b
  let Hₗ : L ⊗[F] A := 1 ⊗ₜ[F] (H.inverse.gram : A)
  let T := ((τ).baseChange L).gramTransform q⁻¹ Hₗ
  have hfix (s : L ≃ₐ[F] L) : coefficientConjugate F L A s T = T := by
    let c := (unitEquiv[L]) (toAmbient p L (GaloisCocycle.value ξ s))
    have hc : ((τ).baseChange L).gramTransform c Hₗ = Hₗ := gramTransform_toAmbient p L _
    let f := coefficientConjugate F L A s
    have hs : c = q * (Units.map f.toMonoidHom q)⁻¹ := by
      change (unitEquiv[L]) (toAmbient p L (GaloisCocycle.value ξ s)) = _
      rw [hb, _root_.map_mul, _root_.map_inv, unitEquiv_conjugate]
    have he : Units.map f.toMonoidHom (q⁻¹) = q⁻¹ * c := by
      rw [_root_.map_inv, hs, ← mul_assoc, inv_mul_cancel, one_mul]
    have hHₗ : f Hₗ = Hₗ := by simp [f, Hₗ]
    have hm := map_gramTransform τ s.toAlgHom q⁻¹ Hₗ
    change f T = ((τ).baseChange L).gramTransform (Units.map f.toMonoidHom q⁻¹) (f Hₗ) at hm
    rw [hm, he, hHₗ, gramTransform_mul, hc]
  obtain ⟨J, hJ⟩ := (mem_range_includeRight_iff F L A T).mpr hfix
  have hu : IsUnit T := ((τ).baseChange L).isUnit_gramTransform _
    (H.inverse.gram.isUnit.map (Algebra.TensorProduct.includeRight : A →ₐ[F] L ⊗[F] A))
  let i : A →ₐ[F] L ⊗[F] A := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (B := A) (algebraMap F L).injective
  let t := hu.unit
  have ht : (t : L ⊗[F] A) = T := hu.unit_spec
  have hInv (s : L ≃ₐ[F] L) : coefficientConjugate F L A s ((t⁻¹ : (L ⊗[F] A)ˣ) : L ⊗[F] A) =
      ((t⁻¹ : (L ⊗[F] A)ˣ) : L ⊗[F] A) := by
    let f := coefficientConjugate F L A s
    have hf : Units.map f.toMonoidHom t = t := Units.ext (by change f (t : L ⊗[F] A) = t; rw [ht]; exact hfix s)
    change ((Units.map f.toMonoidHom t⁻¹ : (L ⊗[F] A)ˣ) : L ⊗[F] A) = _
    rw [_root_.map_inv, hf]
  obtain ⟨Jinv, hJinv⟩ := (mem_range_includeRight_iff F L A (↑(t⁻¹) : L ⊗[F] A)).mpr hInv
  have hJu : IsUnit J := by
    refine ⟨⟨J, Jinv, ?_, ?_⟩, rfl⟩
    · apply hi
      rw [_root_.map_mul, _root_.map_one]
      change i J = T at hJ
      change i Jinv = ↑(t⁻¹) at hJinv
      rw [hJ, hJinv, ← ht, Units.mul_inv]
    · apply hi
      rw [_root_.map_mul, _root_.map_one]
      change i J = T at hJ
      change i Jinv = ↑(t⁻¹) at hJinv
      rw [hJ, hJinv, ← ht, Units.inv_mul]
  have hH : (τ) (H.inverse.gram : A) = H.inverse.gram := H.inverse.hermitian
  have hsym : (τ) J = J := by
    apply Algebra.TensorProduct.includeRight_injective (B := A) (algebraMap F L).injective
    change (1 : L) ⊗ₜ[F] ((τ) J) = (1 : L) ⊗ₜ[F] J
    rw [← baseChange_tmul, show (1 : L) ⊗ₜ[F] J = T from hJ]
    change ((τ).baseChange L) (((τ).baseChange L).gramTransform q⁻¹ Hₗ) = _
    rw [involution_gramTransform, show ((τ).baseChange L) Hₗ = Hₗ by
      rw [show Hₗ = 1 ⊗ₜ[F] (H.inverse.gram : A) from rfl, baseChange_tmul, hH]]
  let J' : Form (fieldInvolution F E) (Fin n) :=
    ⟨hJu.unit, by
      change (τ) hJu.unit.val = hJu.unit.val
      rw [hJu.unit_spec, hsym]⟩
  refine ⟨⟨b, J', hb, ?_⟩⟩
  change T = 1 ⊗ₜ[F] hJu.unit.val
  rw [hJu.unit_spec]
  exact hJ.symm

end Galois

/-- A finite-Galois Hermitian cocycle over an infinite ground field has an ambient
unit primitive and a descended inverse Gram form. -/
def HermitianGaloisGramDescentStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Infinite F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (n : ℕ) (H : Form (fieldInvolution F E) (Fin n))
    (G : GroupScheme (Spec (CommRingCat.of F))) (p : SchemeModel.Presentation F E H G)
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle G (GaloisCocycle.cover F L)), Nonempty (GaloisGramDescent p ξ)

end Langlands.GroupScheme.HermitianMatrix
