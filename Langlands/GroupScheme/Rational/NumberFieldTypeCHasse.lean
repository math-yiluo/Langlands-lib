import Langlands.GroupScheme.Quaternionic.AntihermitianScalarIsometry
import Langlands.GroupScheme.Quaternionic.GaloisGramLocalCongruence
import Langlands.GroupScheme.Quaternionic.LocalWittIndexOneDimension
import Langlands.GroupScheme.Rational.NumberFieldTypeCModels
import Langlands.GroupScheme.SplitUnipotentTorsor.VectorRetract
import Langlands.GroupScheme.SymplecticMatrix.GaloisCoboundary
import Langlands.LinearAlgebra.NumberFieldQuadraticIsometryProof

/-! # The number-field Hasse kernel in simply connected type C -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace SymplecticMatrix

set_option maxHeartbeats 800000 in
private theorem isTrivial_finiteGalois {F L : Type u} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (n : ℕ)
    (ξ : Cocycle (groupScheme (Fin n) (CommRingCat.of F)) (GaloisCocycle.cover F L)) :
    ξ.IsTrivial := by
  let G := groupScheme (Fin n) (CommRingCat.of F)
  let R := CommAlgCat.of F L
  let e := Corepresented.affinePointsEquiv (functor (Fin n) (CommRingCat.of F))
    (corepresentableBy (Fin n) (CommRingCat.of F)) R
  let E : (G.affinePoints R) →* GL (Fin n ⊕ Fin n) L := toGL.comp e.toMonoidHom
  have hE : Function.Injective E := fun _ _ h =>
    e.injective (Subtype.ext (congrArg Units.val h))
  have hact (s : L ≃ₐ[F] L) (x : G.affinePoints R) :
      E (GaloisPoint.conjugate F L G s x) = GeneralLinearGroup.map s.toRingHom (E x) := by
    apply Units.ext
    have h := Corepresented.affinePointsEquiv_naturality
      (functor (Fin n) (CommRingCat.of F)) (corepresentableBy (Fin n) (CommRingCat.of F))
      (CommAlgCat.ofHom s.toAlgHom) x
    change e (GaloisPoint.conjugate F L G s x) = map (Fin n) s.toRingHom (e x) at h
    exact congrArg Subtype.val h
  let c (s : L ≃ₐ[F] L) := E (GaloisCocycle.value ξ s)
  have hc (s t : L ≃ₐ[F] L) : c (s * t) = c s * GeneralLinearGroup.map s.toRingHom (c t) := by
    change E (GaloisCocycle.value ξ (s * t)) = _
    rw [GaloisCocycle.value_mul, _root_.map_mul, hact]
  have hs (s : L ≃ₐ[F] L) : (c s : Matrix _ _ L) ∈ Matrix.symplecticGroup (Fin n) L :=
    (e (GaloisCocycle.value ξ s)).property
  obtain ⟨b, hb, h⟩ := exists_symplectic_coboundary c hc hs
  let a := e.symm ⟨(b : Matrix _ _ L), hb⟩
  have ha : E a = b := by
    change toGL (e (e.symm ⟨(b : Matrix _ _ L), hb⟩)) = b
    rw [e.apply_symm_apply]
    exact Units.ext rfl
  refine (GaloisCocycle.isTrivial_iff ξ).mpr ⟨a, fun s => hE ?_⟩
  change c s = E (a * (GaloisPoint.conjugate F L G s a)⁻¹)
  rw [_root_.map_mul, _root_.map_inv, hact, ha]
  exact eq_mul_inv_of_mul_eq (h s)

end SymplecticMatrix

namespace Quaternionic.FirstKindInvolution

private def isometry_comp_linearEquiv {F V W : Type u} [CommRing F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (q : QuadraticForm F V) (e : W ≃ₗ[F] V) : (q.comp e.toLinearMap).IsometryEquiv q :=
  { e with map_app' := fun _ => rfl }

private def baseChange_isometry_comp_linearEquiv {F K V W : Type u} [Field F] [CommRing K] [Algebra F K]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] [Invertible (2 : F)]
    (q : QuadraticForm F V) (e : W ≃ₗ[F] V) :
    (QuadraticForm.baseChange K (q.comp e.toLinearMap)).IsometryEquiv (q.baseChange K) := by
  let f := e.baseChange F K W V
  have h : QuadraticForm.baseChange K (q.comp e.toLinearMap) = (q.baseChange K).comp f.toLinearMap := by
    apply baseChange_ext
    intro x
    simp only [QuadraticForm.baseChange_tmul, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
      f, LinearEquiv.baseChange_tmul]
  rw [h]
  exact isometry_comp_linearEquiv (q.baseChange K) f

private theorem nondegenerate_comp_linearEquiv {F V W : Type u} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (q : QuadraticForm F V) (e : W ≃ₗ[F] V) (h : q.polarBilin.Nondegenerate) :
    (q.comp e.toLinearMap).polarBilin.Nondegenerate := by
  have hp (x y : W) : (q.comp e.toLinearMap).polarBilin x y = q.polarBilin (e x) (e y) := by
    rw [QuadraticMap.polarBilin_comp]
    rfl
  constructor
  · intro x hx
    apply e.injective
    rw [_root_.map_zero]
    apply h.1
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    exact (hp x z).symm.trans (hx z)
  · intro x hx
    apply e.injective
    rw [_root_.map_zero]
    apply h.2
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    exact (hp z x).symm.trans (hx z)

private theorem quadraticEquivalent_of_local {F V : Type u} [Field F] [NumberField F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q q' : QuadraticForm F V) (hq : q.polarBilin.Nondegenerate) (hq' : q'.polarBilin.Nondegenerate) :
    let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
    (∀ v : Global.Place F, (q.baseChange (Global.placeCompletion F v)).Equivalent
      (q'.baseChange (Global.placeCompletion F v))) → q.Equivalent q' := by
  intro inst hlocal
  let e := (Module.finBasis F V).equivFun.symm
  obtain ⟨f⟩ := numberFieldQuadraticIsometry F (Module.finrank F V)
    (q.comp e.toLinearMap) (q'.comp e.toLinearMap)
    (nondegenerate_comp_linearEquiv q e hq) (nondegenerate_comp_linearEquiv q' e hq') (fun v => by
      obtain ⟨g⟩ := hlocal v
      let K := Global.placeCompletion F v
      exact ⟨((baseChange_isometry_comp_linearEquiv (K := K) q e).trans g).trans
        (baseChange_isometry_comp_linearEquiv (K := K) q' e).symm⟩)
  exact ⟨((isometry_comp_linearEquiv q e).symm.trans f).trans (isometry_comp_linearEquiv q' e)⟩

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  (σ : FirstKindInvolution F D) {r : ℕ}

private theorem scalarQuadratic_equivalent_of_tensorGramCongruent [Invertible (2 : F)]
    (ℓ : D →ₗ[F] F) (H H' : Matrix (Fin r) (Fin r) D)
    (K : Type u) [Field K] [Algebra F K] (h : σ.TensorGramCongruent H H' K) :
    ((σ.scalarQuadratic ℓ H').baseChange K).Equivalent ((σ.scalarQuadratic ℓ H).baseChange K) := by
  obtain ⟨P, hP⟩ := h
  let e := FiniteAlgebraUnits.MatrixPoints.coefficientEquiv (m := Fin r) F D K
  let Q := Units.map e.toMonoidHom P
  let Hd := H.map (Algebra.TensorProduct.includeRight : D →ₐ[F] K ⊗[F] D)
  let Hd' := H'.map (Algebra.TensorProduct.includeRight : D →ₐ[F] K ⊗[F] D)
  have hQ : (Q : Matrix (Fin r) (Fin r) (K ⊗[F] D)) * Hd * (σ.baseChange K).matrix (Fin r) Q = Hd' := by
    have hp := congrArg e hP
    change e ((P : K ⊗[F] Matrix (Fin r) (Fin r) D) * ((1 : K) ⊗ₜ[F] H) *
      (σ.matrix (Fin r)).baseChange K P) = e ((1 : K) ⊗ₜ[F] H') at hp
    change e P * Hd * (σ.baseChange K).matrix (Fin r) (e P) = Hd'
    simpa only [e, _root_.map_mul, coefficientEquiv_matrix_baseChange,
      coefficientEquiv_one_tmul_eq_map] using hp
  rw [σ.scalarQuadratic_baseChange ℓ H' K, σ.scalarQuadratic_baseChange ℓ H K]
  let a := baseChangeScalarFunctional ℓ K
  let f := TensorProduct.piRight F K K (fun _ : Fin r => D)
  exact ⟨((isometry_comp_linearEquiv ((σ.baseChange K).scalarQuadratic a Hd') f).trans
      ((σ.baseChange K).scalarQuadraticIsometry a Q hQ)).trans
      (isometry_comp_linearEquiv ((σ.baseChange K).scalarQuadratic a Hd) f).symm⟩

variable [NumberField F] [FiniteDimensional F D] [Algebra.IsCentral F D] [NeZero r]

set_option maxHeartbeats 800000 in
private theorem isTrivial_of_locallyTrivial_typeC_division
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3)
    (H : Matrix (Fin r) (Fin r) D) (hH : σ.IsAntihermitian H) (hu : IsUnit H)
    {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle (σ.symplecticGroup H) (GaloisCocycle.cover F L)) (hlocal : ξ.LocallyTrivial) :
    ξ.IsTrivial := by
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  have hσ : Module.finrank F σ.symmetricSubspace =
      Langlands.CentralSimple.reducedDegree F D * (Langlands.CentralSimple.reducedDegree F D + 1) / 2 := by
    rw [reducedDegree_eq_two_of_finrank_four hdim]
    exact hsym
  let d := σ.symplecticGramDescent H hσ hH hu ξ
  have hline := σ.finrank_alternatingSubspace_of_dimensions hdim hsym
  let ℓ := σ.alternatingCoordinate hline
  have hcoord (a : D) (ha : a ∈ σ.alternatingSubspace) (h : ℓ a = 0) : a = 0 :=
    (σ.alternatingCoordinate_eq_zero_iff hline ha).mp h
  have hℓ : ∃ a, ℓ (a - σ a) ≠ 0 := by
    have hne : σ.alternatingSubspace ≠ ⊥ := by
      intro hh
      rw [hh, finrank_bot] at hline
      exact Nat.zero_ne_one hline
    obtain ⟨a, ha, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨b, hb⟩ := σ.mem_alternatingSubspace.mp ha
    exact ⟨b, fun h => hn (hcoord a ha (hb ▸ h))⟩
  have he : (σ.scalarQuadratic ℓ d.gram).Equivalent (σ.scalarQuadratic ℓ H) := by
    apply quadraticEquivalent_of_local _ _ (σ.scalarQuadratic_nondegenerate ℓ d.gram_antihermitian d.gram_unit hℓ)
      (σ.scalarQuadratic_nondegenerate ℓ hH hu hℓ)
    intro v
    rcases v with v | v
    · let : CharZero v.Completion := charZero_of_injective_algebraMap
        (algebraMap F v.Completion).injective
      exact σ.scalarQuadratic_equivalent_of_tensorGramCongruent ℓ H d.gram v.Completion
        (SymplecticGramDescent.exists_tensor_gramTransform_of_baseChange_isTrivial
          σ H d hσ hH hu (hlocal (.inl v)))
    · let : CharZero (Global.FiniteCompletion F v) := charZero_of_injective_algebraMap
        (algebraMap F (Global.FiniteCompletion F v)).injective
      exact σ.scalarQuadratic_equivalent_of_tensorGramCongruent ℓ H d.gram (Global.FiniteCompletion F v)
        (SymplecticGramDescent.exists_tensor_gramTransform_of_baseChange_isTrivial
          σ H d hσ hH hu (hlocal (.inr v)))
  obtain ⟨P, hP⟩ := matrixScalarIsometryReflection F D σ (Fin r) ℓ H d.gram
    hℓ hcoord hH d.gram_antihermitian hu d.gram_unit he
  exact SymplecticGramDescent.isTrivial_of_gramTransform σ H hσ hH hu d P hP

end Quaternionic.FirstKindInvolution

/-- The localization kernel for simply connected absolutely almost-simple type C groups. -/
def NumberFieldTypeCSimplyConnectedGaloisHasseKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (r : ℕ) (e : d.Vertex ≃ Fin r),
    2 ≤ r → IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.C r (e a) (e b)) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The type C Hasse kernel follows by symplectic Hilbert 90 and the quaternionic
Gram comparison with the Hasse–Minkowski isometry theorem. -/
theorem numberFieldTypeCSimplyConnectedGaloisHasseKernel :
    NumberFieldTypeCSimplyConnectedGaloisHasseKernelStatement.{u} := by
  intro F _ _ G _ _ d r e hr hsc habs hC L _ _ _ _ ξ hξ
  rcases numberFieldTypeCModels F G d r e hr hsc habs hC with hsplit | hdiv
  · obtain ⟨j⟩ := hsplit
    exact Cocycle.IsTrivial.of_map_retract j.hom j.inv j.hom_inv_id
      (SymplecticMatrix.isTrivial_finiteGalois r (ξ.map j.hom))
  · obtain ⟨_, D, _, _, _, _, hD, σ, hσ, H, hH, hu, ⟨j⟩⟩ := hdiv
    exact Cocycle.IsTrivial.of_map_retract j.hom j.inv j.hom_inv_id
      (Quaternionic.FirstKindInvolution.isTrivial_of_locallyTrivial_typeC_division σ hD hσ H hH hu
        (ξ.map j.hom) (hξ.map j.hom))

end Langlands.GroupScheme
