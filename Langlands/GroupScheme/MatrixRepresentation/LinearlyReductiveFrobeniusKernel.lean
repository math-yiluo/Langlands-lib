import Langlands.GroupScheme.MatrixRepresentation.HeightOneDiagonal
import Langlands.GroupScheme.MatrixRepresentation.TangentDiagonalization
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusPower
import Langlands.GroupScheme.KernelPresentation
import Langlands.GroupScheme.Torus.CentralExtensionHopfSpec
import Langlands.GroupScheme.Torus.NagataReductionStatements

/-! # The first Frobenius kernel of a linearly reductive group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.GroupScheme.Lie

variable {k : Type u} [Field k] {n : ℕ}

private theorem map_matrix_values {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (M : GL (Fin n) A) (v : GeneralLinear.Coordinate (Fin n)) :
    f (GeneralLinear.values M v) =
      GeneralLinear.values (Matrix.GeneralLinearGroup.map f M) v := by
  cases v with
  | entry i j => rfl
  | inverseEntry i j =>
    change f (M⁻¹ i j) = (Matrix.GeneralLinearGroup.map f M)⁻¹ i j
    rw [← map_inv]
    rfl

private theorem classify_pow_is_scalar (p : ℕ) [ExpChar k p]
    {A : Type u} [CommRing A] [Algebra k A] (M : GL (Fin n) A)
    (hM : Matrix.GeneralLinearGroup.map (GeneralLinear.algebraFrobenius k p A) M = 1)
    (a : GeneralLinear.CoordinateRing (Fin n) k) :
    ∃ c : k, algebraMap k A c = GeneralLinear.classify M a ^ p := by
  let F := GeneralLinear.algebraFrobenius k p A
  change ∃ c : k, algebraMap k A c = F (GeneralLinear.classify M a)
  have hgen (v : GeneralLinear.Coordinate (Fin n)) :
      algebraMap k A (GeneralLinear.values (1 : GL (Fin n) k) v) =
        F (GeneralLinear.classify M (GeneralLinear.quotient (Fin n) k (MvPolynomial.X v))) := by
    have h := map_matrix_values (algebraMap k A) (1 : GL (Fin n) k) v
    rw [map_one] at h
    rw [GeneralLinear.classify_quotient, MvPolynomial.aeval_X, map_matrix_values F, hM]
    exact h
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  change ∃ c, algebraMap k A c = F (GeneralLinear.classify M (GeneralLinear.quotient (Fin n) k q))
  induction q using MvPolynomial.induction_on with
  | C c =>
    refine ⟨c ^ p, ?_⟩
    rw [GeneralLinear.classify_quotient, MvPolynomial.aeval_C,
      GeneralLinear.algebraFrobenius_apply, map_pow]
  | add q r hq hr =>
    obtain ⟨c, hc⟩ := hq
    obtain ⟨d, hd⟩ := hr
    exact ⟨c + d, by rw [map_add, map_add, map_add, map_add, hc, hd]⟩
  | mul_X q v hq =>
    obtain ⟨c, hc⟩ := hq
    exact ⟨c * GeneralLinear.values (1 : GL (Fin n) k) v, by
      rw [map_mul, map_mul, map_mul, map_mul, hc, hgen]⟩

private theorem coordinate_pow_eq_origin_of_frobenius_eq_one
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (p : ℕ) [ExpChar k p] (ρ : MatrixRepresentation H (Fin n)) (hρ : IsClosedSubgroup ρ)
    (hF : Matrix.GeneralLinearGroup.map (GeneralLinear.algebraFrobenius k p (coordinateAlgebra H))
      (ρ.affineMatrix (coordinateAlgebra H) (universalPoint H)) = 1)
    (a : coordinateAlgebra H) :
    a ^ p = algebraMap k (coordinateAlgebra H) (coordinateOrigin H a) ^ p := by
  let R := CommRingCat.of k
  let A := coordinateAlgebra H
  let x := universalPoint H ≫ ρ.hom.hom
  let M := ρ.affineMatrix A (universalPoint H)
  let φ : GeneralLinear.CoordinateRing (Fin n) k →ₐ[k] A := GeneralLinear.classify M
  have hx : (algSpec R).map (CommAlgCat.ofHom φ).op = x := by
    have h := GeneralLinear.affinePointsEquiv_symm_apply (n := Fin n) (R := R) A
      (GeneralLinear.affinePointsEquiv (Fin n) R A x)
    exact h.symm.trans ((GeneralLinear.affinePointsEquiv (Fin n) R A).symm_apply_apply x)
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    change IsClosedImmersion (((algSpec R).map (CommAlgCat.ofHom φ).op).left)
    rw [hx]
    change IsClosedImmersion ((CharacterUnits.universalPoint H ≫ ρ.hom.hom).left)
    rw [CharacterUnits.universalPoint_eq, Over.comp_left]
    let : IsIso (coordinateIso H).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).mapIso (coordinateIso H)).hom)
    infer_instance
  have hφ : Function.Surjective φ :=
    CentralExtensionHopfSpec.surjective_of_isClosedImmersion (CommRingCat.ofHom φ.toRingHom)
  obtain ⟨b, rfl⟩ := hφ a
  obtain ⟨c, hc⟩ := classify_pow_is_scalar p M hF b
  calc
    φ b ^ p = algebraMap k A c := hc.symm
    _ = algebraMap k A (coordinateOrigin H (φ b ^ p)) := by
      rw [← hc, (coordinateOrigin H).commutes]
      rfl
    _ = algebraMap k A (coordinateOrigin H (φ b)) ^ p := by rw [map_pow, map_pow]

/-- The first matrix Frobenius kernel of a closed representation of a linearly
reductive group over an algebraically closed field is of multiplicative type. -/
theorem isMultiplicativeType_frobeniusPowerOne_kernel_of_linearlyReductive
    [IsAlgClosed k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : ℕ) [ExpChar k p] (hp : 1 < p)
    (hG : ∀ d (σ : MatrixRepresentation G (Fin d)), σ.IsSemisimple)
    (ρ : MatrixRepresentation G (Fin n)) (hρ : IsClosedSubgroup ρ) :
    IsMultiplicativeType (kernel (ρ.frobeniusPower p 1)) := by
  let R := CommRingCat.of k
  let ψ := ρ.frobeniusPower p 1
  let K := kernel ψ
  let j : K ⟶ G := kernelι ψ
  let : IsAffineHom (GeneralLinear.groupScheme (Fin n) R).X.hom :=
    GeneralLinear.isAffineHom_groupScheme (Fin n) R
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let : IsFinite (GeneralLinear.frobeniusHom k p (Fin n)).hom.hom.left :=
    GeneralLinear.isFinite_frobeniusHom k p (Fin n)
  have hψ : IsFinite ψ.hom.hom.left := by
    change IsFinite (ρ.hom.hom.left ≫ (GeneralLinear.frobeniusHom k p (Fin n)).hom.hom.left)
    infer_instance
  let : IsFinite K.X.hom := MorphismProperty.of_isPullback (kernel_isPullback_scheme ψ) hψ
  let : IsAffineHom K.X.hom := isAffineHom_kernel_of_closed ψ
  let A := coordinateAlgebra K
  have hfin : IsFinite ((algSpec R).obj (op A)).hom := by
    rw [← Over.w (coordinateIso K).hom]
    let : IsIso (coordinateIso K).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).mapIso (coordinateIso K)).hom)
    infer_instance
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k A))) at hfin
  let : Module.Finite k A := by
    rw [IsFinite.SpecMap_iff] at hfin
    change (algebraMap k A).Finite at hfin
    exact RingHom.finite_algebraMap.mp hfin
  have hj : IsClosedSubgroup j := inferInstanceAs (IsClosedImmersion (kernelι ψ).hom.hom.left)
  have htest : ((universalPoint K) ≫ j.hom.hom) ≫ ψ.hom.hom = 1 :=
    (mem_range_kernelι_iff ψ _).mp ⟨universalPoint K, rfl⟩
  have hfrob : Matrix.GeneralLinearGroup.map (GeneralLinear.algebraFrobenius k p A)
      ((ρ.restrict j).affineMatrix A (universalPoint K)) = 1 := by
    have h := congrArg (GeneralLinear.affinePointsEquiv (Fin n) R A) htest
    rw [map_one] at h
    change GeneralLinear.affinePointsEquiv (Fin n) R A
      ((universalPoint K ≫ j.hom.hom) ≫ (ρ ≫ GeneralLinear.frobeniusHom k p (Fin n)).hom.hom) = 1 at h
    rw [Grp.comp_hom_hom, ← Category.assoc, GeneralLinear.affinePointsEquiv_frobeniusHom] at h
    exact h
  have hheight := coordinate_pow_eq_origin_of_frobenius_eq_one p (ρ.restrict j)
    (hj.comp hρ) hfrob
  have hprime := (expChar_is_prime_or_one k p).resolve_right (by omega : p ≠ 1)
  let : CharP k p := (expChar_prime_iff k hprime).mp inferInstance
  obtain ⟨b, hb⟩ := exists_conjugate_tangentMatrix_diagonal_of_linearlyReductive p
    (by omega : p ≠ 0) hG ρ
  apply isMultiplicativeType_of_diagonal_tangent_heightOne p hp hheight
    ((ρ.conjugate (basisCoordinatePoint b)).restrict j) (hj.comp (hρ.comp_iso _))
  intro X i l hil
  rw [tangentMatrix_restrict]
  exact hb (targetMap j k X) i l hil

/-- The first-kernel multiplicative-type implication used in Frobenius induction. -/
def LinearlyReductiveFrobeniusKernelStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [ExpChar k p], 1 < p →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
      IsLinearlyReductive G → ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
        IsClosedSubgroup ρ → IsMultiplicativeType (kernel (ρ.frobeniusPower p 1))

theorem linearlyReductiveFrobeniusKernel : LinearlyReductiveFrobeniusKernelStatement.{u} := by
  intro k _ _ p _ hp G _ hG n ρ hρ
  exact isMultiplicativeType_frobeniusPowerOne_kernel_of_linearlyReductive p hp hG ρ hρ

end Langlands.GroupScheme.MatrixRepresentation
