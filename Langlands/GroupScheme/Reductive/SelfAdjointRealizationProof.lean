import Langlands.GroupScheme.Reductive.SelfAdjointRealizationStatement
import Langlands.GroupScheme.Reductive.PolynomialSemisimplicity
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.MatrixRepresentationPolynomialImage
import Langlands.GroupScheme.MatrixRepresentationPositiveForm
import Langlands.Group.ClosedOrbit
import Langlands.Group.FormSelfAdjointMean
import Langlands.Global.InfiniteCompletionRCLike
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Field.ULift

/-! # Actual adjoint-stable realization of a connected reductive group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix ComplexOrder

namespace Langlands.GroupScheme.MatrixRepresentation

section BaseChange

variable {C D : Type u} [CommRing C] [CommRing D] [Algebra C D]
  {G : GroupScheme (Spec (CommRingCat.of C))} {n : Type} [Fintype n] [DecidableEq n]

/-- The scalar extension of a matrix representation has, on the rational points of the
base-changed group, the same matrices as the original representation on the corresponding
coefficient points. -/
theorem baseChange_affineMatrix_affinePointsBaseChangeMulEquiv
    (ρ : MatrixRepresentation G n) (y : G.affinePoints (CommAlgCat.of C D)) :
    (ρ.baseChange (Spec.algebraMap C D)).affineMatrix (CommAlgCat.of D D)
        (affinePointsBaseChangeMulEquiv C D D G y) =
      ρ.affineMatrix (CommAlgCat.of C D) y := by
  have hφ : Function.Injective (Corepresented.affineSectionsIso (R := CommRingCat.of D)
      (CommAlgCat.of D D)).inv.hom.toRingHom := by
    change Function.Injective (Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of D)).inv).1
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := n)
      (Corepresented.affineSectionsIso (R := CommRingCat.of D)
        (CommAlgCat.of D D)).inv.hom.toRingHom) := by
    intro a b hab
    rw [Matrix.GeneralLinearGroup.ext_iff] at hab ⊢
    exact fun i j => hφ (hab i j)
  apply hinj
  have h1 := pointMatrix_eq_affineMatrix (ρ.baseChange (Spec.algebraMap C D))
    (CommAlgCat.of D D) (affinePointsBaseChangeMulEquiv C D D G y)
  have h2 := pointMatrix_eq_affineMatrix ρ (CommAlgCat.of C D) y
  refine h1.symm.trans ?_
  rw [pointMatrix_baseChange]
  have hx : baseChangePointsEquiv (Spec.algebraMap C D) G
      ((algSpec (CommRingCat.of D)).obj (op (CommAlgCat.of D D)))
      (affinePointsBaseChangeMulEquiv C D D G y) =
        (Langlands.AlgebraicGeometry.PointTopology.ringTestRestrictScalarsIso C D D).hom ≫ y := by
    change baseChangePointsEquiv (Spec.algebraMap C D) G _
      ((baseChangePointsEquiv (Spec.algebraMap C D) G _).symm _) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [hx, pointMatrix_naturality]
  exact h2

/-- Scalar extension preserves the scheme-theoretic closed-embedding property. -/
theorem isClosedSubgroup_baseChange {R R' : CommRingCat.{u}} {G : GroupScheme (Spec R)}
    (ρ : MatrixRepresentation G n) (b : Spec R' ⟶ Spec R) (hρ : IsClosedSubgroup ρ) :
    IsClosedSubgroup (ρ.baseChange b) := by
  have : IsClosedImmersion ((GroupScheme.baseChange b).map ρ).hom.hom.left :=
    IsClosedSubgroup.baseChange b hρ
  have : IsIso (GeneralLinear.baseChangeIso n b).hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (GeneralLinear.baseChangeIso n b).hom.hom.hom))
  change IsClosedImmersion (_ ≫ _)
  infer_instance

end BaseChange

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.SelfAdjointRealization

open Langlands.Group Langlands.Group.FormSelfAdjointMean
open Langlands.Group.AlgebraicMatrixPowers (IsPolynomiallyDefined)
open Langlands.GroupScheme.GeneralLinear (values)

variable {n : Type} [Fintype n] [DecidableEq n]

section AlgClosed

variable {S : Type u} [RCLike S] [IsAlgClosed S] {G : GroupScheme (Spec (CommRingCat.of S))}

/-- **Algebraically closed case.** Over an algebraically closed real or complex field, the
rational image of a closed matrix representation of a connected reductive group is
self-adjoint for some positive definite Hermitian form. -/
theorem exists_posDef_form (hG : IsConnectedReductive G) (ρ : MatrixRepresentation G n)
    (hρ : IsClosedSubgroup ρ) :
    ∃ J : GL n S, J.val.PosDef ∧ ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of S S)).range,
      J⁻¹ * star g * J ∈ (ρ.affineMatrix (CommAlgCat.of S S)).range := by
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have hH : IsPolynomiallyDefined (ρ.affineMatrix (CommAlgCat.of S S)).range :=
    ρ.affineMatrix_range_isPolynomiallyDefined S
  have : Representation.IsSemisimpleRepresentation
      (ClosedOrbit.subgroupRep (ρ.affineMatrix (CommAlgCat.of S S)).range) :=
    PolynomialSemisimplicity.isSemisimpleRepresentation_rightTranslation
      hG.isPseudoReductive ρ
  obtain ⟨x, hx⟩ := ClosedOrbit.exists_conj_star_mem _ hH
  exact ⟨star x * x, posDef_star_mul_self x, isFormSelfAdjoint_star_mul_self x hx⟩

end AlgClosed

section Real

variable {k S : Type u} [RCLike k] [RCLike S] [Algebra k S] [IsScalarTower ℝ k S]

omit [IsScalarTower ℝ k S] in
/-- An element of a field with trivial conjugation is the real number given by its real
part. -/
private theorem ofReal_re_eq (hreal : ∀ z : k, star z = z) (z : k) : (RCLike.re z : k) = z :=
  RCLike.conj_eq_iff_re.mp (hreal z)

/-- Through a compatible real scalar tower, every element of a field with trivial
conjugation maps to the real number given by its real part. -/
private theorem algebraMap_eq_ofReal_re (hreal : ∀ z : k, star z = z) (z : k) :
    algebraMap k S z = (RCLike.re z : S) := by
  calc algebraMap k S z = algebraMap k S (algebraMap ℝ k (RCLike.re z)) := by
        rw [RCLike.algebraMap_eq_ofReal, ofReal_re_eq hreal]
    _ = (RCLike.re z : S) := by
        rw [← IsScalarTower.algebraMap_apply, RCLike.algebraMap_eq_ofReal]

private theorem star_algebraMap (hreal : ∀ z : k, star z = z) (z : k) :
    star (algebraMap k S z) = algebraMap k S z := by
  rw [algebraMap_eq_ofReal_re hreal]
  exact RCLike.conj_ofReal _

private theorem semiconj_algebraMap (hreal : ∀ z : k, star z = z) :
    Function.Semiconj (algebraMap k S) star star := fun z => by
  rw [hreal z, star_algebraMap hreal]

omit [DecidableEq n] in
/-- Positive definiteness descends along a compatible extension of a field with trivial
conjugation. -/
private theorem posDef_of_map (hreal : ∀ z : k, star z = z) {M : Matrix n n k}
    (hM : (M.map (algebraMap k S)).PosDef) : M.PosDef := by
  have hs := semiconj_algebraMap (S := S) hreal
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hM ⊢
  refine ⟨(Matrix.isHermitian_map_iff hs (algebraMap k S).injective).mp hM.1, fun x hx => ?_⟩
  have hx' : (fun i => algebraMap k S (x i)) ≠ 0 := fun h =>
    hx (funext fun i => (algebraMap k S).injective (by simpa using congrFun h i))
  have h := hM.2 hx'
  have heq : star (fun i => algebraMap k S (x i)) ⬝ᵥ
      (M.map (algebraMap k S) *ᵥ fun i => algebraMap k S (x i)) =
        algebraMap k S (star x ⬝ᵥ (M *ᵥ x)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hs (x i)]
  rw [heq, algebraMap_eq_ofReal_re hreal, RCLike.ofReal_pos] at h
  rw [← ofReal_re_eq hreal (star x ⬝ᵥ (M *ᵥ x))]
  exact RCLike.ofReal_pos.mpr h

/-- Entrywise algebra maps commute with conjugate transposition. -/
private theorem map_star (hreal : ∀ z : k, star z = z) (g : GL n k) :
    Matrix.GeneralLinearGroup.map (algebraMap k S) (star g) =
      star (Matrix.GeneralLinearGroup.map (algebraMap k S) g) := by
  apply Units.ext
  change (star g.val).map (algebraMap k S) = star (g.val.map (algebraMap k S))
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_map _ (semiconj_algebraMap hreal)]

/-- A matrix unit fixed by entrywise conjugation comes from the base field. -/
private theorem exists_map_eq_of_conjGL_eq (g : GL n S) (hg : conjGL g = g) :
    ∃ a : GL n k, Matrix.GeneralLinearGroup.map (algebraMap k S) a = g := by
  have hfix (h : GL n S) (hh : conjGL h = h) :
      (h.val.map fun z => ((RCLike.re z : ℝ) : k)).map (algebraMap k S) = h.val := by
    ext i j
    have hij : starRingEnd S (h.val i j) = h.val i j :=
      congrArg (fun q : GL n S => q.val i j) hh
    simp only [Matrix.map_apply]
    rw [← RCLike.algebraMap_eq_ofReal, ← IsScalarTower.algebraMap_apply,
      RCLike.algebraMap_eq_ofReal]
    exact RCLike.conj_eq_iff_re.mp hij
  have hgi : conjGL g⁻¹ = g⁻¹ := by rw [map_inv, hg]
  set A := g.val.map fun z => ((RCLike.re z : ℝ) : k)
  set B := (g⁻¹).val.map fun z => ((RCLike.re z : ℝ) : k)
  have hA : A.map (algebraMap k S) = g.val := hfix g hg
  have hB : B.map (algebraMap k S) = (g⁻¹).val := hfix g⁻¹ hgi
  have hinj : Function.Injective fun M : Matrix n n k => M.map (algebraMap k S) :=
    fun M N h => Matrix.ext fun i j => (algebraMap k S).injective (congrFun (congrFun h i) j)
  have hAB : A * B = 1 := hinj (by
    change (A * B).map (algebraMap k S) = (1 : Matrix n n k).map (algebraMap k S)
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv)
  have hBA : B * A = 1 := hinj (by
    change (B * A).map (algebraMap k S) = (1 : Matrix n n k).map (algebraMap k S)
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul)
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

variable {G : GroupScheme (Spec (CommRingCat.of k))}

omit [IsScalarTower ℝ k S] in
/-- Membership in the range of a closed representation reflects through an injective
scalar extension. -/
private theorem map_mem_range_iff (ρ : MatrixRepresentation G n)
    [IsClosedImmersion ρ.hom.hom.left] (g : GL n k) :
    Matrix.GeneralLinearGroup.map (algebraMap k S) g ∈
        (ρ.affineMatrix (CommAlgCat.of k S)).range ↔
      g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range := by
  rw [ρ.mem_affineMatrix_range_iff_zeroLocus S, ρ.mem_affineMatrix_range_iff_zeroLocus k]
  constructor
  · intro hg p hp
    apply (algebraMap k S).injective
    rw [map_zero]
    have h := hg p hp
    rw [GeneralLinear.values_map] at h
    change MvPolynomial.aeval
      (fun v => (Algebra.ofId k S) (GeneralLinear.values g v)) p = 0 at h
    rw [← MvPolynomial.comp_aeval_apply] at h
    exact h
  · exact GeneralLinear.map_mem_zeroLocus (Algebra.ofId k S)

/-- The coefficient-point range of a closed representation over a field with trivial
conjugation is stable under entrywise conjugation. -/
private theorem conjGL_mem_range (hreal : ∀ z : k, star z = z) (ρ : MatrixRepresentation G n)
    [IsClosedImmersion ρ.hom.hom.left] (g : GL n S)
    (hg : g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range) :
    conjGL g ∈ (ρ.affineMatrix (CommAlgCat.of k S)).range := by
  rw [ρ.mem_affineMatrix_range_iff_zeroLocus S] at hg ⊢
  intro p hp
  have hc : (starRingEnd S).comp (algebraMap k S) = algebraMap k S :=
    RingHom.ext (star_algebraMap hreal)
  change MvPolynomial.aeval (values (Matrix.GeneralLinearGroup.map (starRingEnd S) g)) p = 0
  rw [GeneralLinear.values_map, MvPolynomial.aeval_def, ← hc,
    ← MvPolynomial.eval₂_comp_left, ← MvPolynomial.aeval_def, hg p hp, map_zero]

/-- **Real case.** If a field with trivial conjugation embeds into an algebraically closed
real or complex field compatibly with the real scalars, the rational image of a closed matrix
representation of a connected reductive group over it is self-adjoint for a positive
definite form over the original field. -/
theorem exists_posDef_form_of_real [IsAlgClosed S] (hreal : ∀ z : k, star z = z)
    (hG : IsConnectedReductive G) (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ) :
    ∃ J : GL n k, J.val.PosDef ∧ ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range,
      J⁻¹ * star g * J ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range := by
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have hGS := connectedReductiveFieldExtensionStatement k S G hG
  have hσ := ρ.isClosedSubgroup_baseChange (Spec.algebraMap k S) hρ
  obtain ⟨J, hJ, hform⟩ := exists_posDef_form hGS _ hσ
  have hrange : ((ρ.baseChange (Spec.algebraMap k S)).affineMatrix
      (CommAlgCat.of S S)).range = (ρ.affineMatrix (CommAlgCat.of k S)).range := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(affinePointsBaseChangeMulEquiv k S S G).symm x, ?_⟩
      rw [← MatrixRepresentation.baseChange_affineMatrix_affinePointsBaseChangeMulEquiv,
        MulEquiv.apply_symm_apply]
    · rintro ⟨y, rfl⟩
      exact ⟨_, MatrixRepresentation.baseChange_affineMatrix_affinePointsBaseChangeMulEquiv ρ y⟩
  rw [hrange] at hform
  obtain ⟨m, hm, hmc, hmA⟩ := exists_real_form _ (ρ.affineMatrix_range_isPolynomiallyDefined S)
    (conjGL_mem_range hreal ρ) hJ hform
  obtain ⟨m₀, rfl⟩ := exists_map_eq_of_conjGL_eq (k := k) m hmc
  refine ⟨m₀, posDef_of_map hreal hm, fun g hg => ?_⟩
  apply (map_mem_range_iff (S := S) ρ _).mp
  rw [map_mul, map_mul, map_inv, map_star hreal]
  exact hmA _ ((map_mem_range_iff ρ g).mpr hg)

end Real

section Transfer

/-- Algebraic closure transfers through a ring equivalence between fields in different
universes. -/
private theorem isAlgClosed_of_ringEquiv {A : Type} [Field A] [IsAlgClosed A]
    (B : Type u) [Field B] (e : A ≃+* B) : IsAlgClosed B := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : (p.map e.symm.toRingHom).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hp)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (k := A) (p.map e.symm.toRingHom) hpe
  refine ⟨e x, ?_⟩
  rw [Polynomial.IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

/-- The complex numbers in the universe `u`, with their norm transported along `ULift`. -/
@[instance_reducible]
private def liftRCLike : RCLike (ULift.{u} ℂ) := by
  let : NormedField (ULift.{u} ℂ) :=
    NormedField.induced _ _ ULift.ringEquiv ULift.down_injective
  exact Analytic.rclikeOfNormPreservingRingEquiv ULift.ringEquiv (fun _ => rfl)

/-- A field with `I = 0` embeds into the lifted complex numbers through its real part. -/
@[instance_reducible]
private def liftAlgebra {k : Type u} [RCLike k] (hI : (RCLike.I : k) = 0) :
    Algebra k (ULift.{u} ℂ) :=
  ((ULift.ringEquiv : ULift.{u} ℂ ≃+* ℂ).symm.toRingHom.comp
    (Complex.ofRealHom.comp (RCLike.realRingEquiv hI).toRingHom)).toAlgebra

private theorem liftAlgebra_scalarTower {k : Type u} [RCLike k] (hI : (RCLike.I : k) = 0) :
    letI := liftRCLike.{u}
    letI := liftAlgebra hI
    IsScalarTower ℝ k (ULift.{u} ℂ) := by
  let := liftRCLike.{u}
  let := liftAlgebra hI
  apply IsScalarTower.of_algebraMap_eq
  intro r
  apply ULift.down_injective
  change (r : ℂ) = (RCLike.re (algebraMap ℝ k r) : ℂ)
  rw [RCLike.ofReal_re]

end Transfer

/-- **Adjoint-stable closed realization.** Every connected reductive group over a real or
complex field has a closed matrix representation whose rational image is stable under
conjugate transpose. -/
theorem connectedReductiveSelfAdjointRealizationStatement :
    ConnectedReductiveSelfAdjointRealizationStatement.{u} := by
  intro k _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G hG.isAffineHom inferInstance
  suffices h : ∃ J : GL (Fin N) k, J.val.PosDef ∧
      ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range,
        J⁻¹ * star g * J ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range by
    obtain ⟨J, hJ, hform⟩ := h
    obtain ⟨σ, hσ, -, hstar⟩ := ρ.exists_closed_starStable_of_positiveForm hρ J hJ hform
    exact ⟨N, σ, hσ, hstar⟩
  by_cases hI : (RCLike.I : k) = 0
  · let := liftRCLike.{u}
    let := liftAlgebra hI
    have := liftAlgebra_scalarTower hI
    have : IsAlgClosed (ULift.{u} ℂ) := isAlgClosed_of_ringEquiv _ ULift.ringEquiv.symm
    exact exists_posDef_form_of_real (S := ULift.{u} ℂ)
      (fun z => RCLike.conj_eq_iff_im.mpr (RCLike.im_eq_zero hI z)) hG ρ hρ
  · have : IsAlgClosed k := isAlgClosed_of_ringEquiv k
      (RCLike.complexRingEquiv ((RCLike.I_eq_zero_or_im_I_eq_one (K := k)).resolve_left hI)).symm
    exact exists_posDef_form hG ρ hρ

/-- The size of a chosen adjoint-stable closed matrix realization of a connected reductive
group over a real or complex field. -/
def realizationDim (k : Type u) [RCLike k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) : ℕ :=
  Classical.choose (connectedReductiveSelfAdjointRealizationStatement k G hG)

/-- A chosen closed matrix realization of a connected reductive group over a real or complex
field whose rational image is stable under conjugate transpose. -/
def realization (k : Type u) [RCLike k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) : MatrixRepresentation G (Fin (realizationDim k G hG)) :=
  Classical.choose
    (Classical.choose_spec (connectedReductiveSelfAdjointRealizationStatement k G hG))

/-- The chosen realization is a closed immersion with adjoint-stable rational image. -/
theorem realization_spec (k : Type u) [RCLike k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) :
    IsClosedSubgroup (realization k G hG) ∧
      ∀ q ∈ ((realization k G hG).affineMatrix (CommAlgCat.of k k)).range,
        star q ∈ ((realization k G hG).affineMatrix (CommAlgCat.of k k)).range :=
  Classical.choose_spec
    (Classical.choose_spec (connectedReductiveSelfAdjointRealizationStatement k G hG))

end Langlands.GroupScheme.SelfAdjointRealization
