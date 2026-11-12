import Langlands.GroupScheme.Unipotent.CharZeroIdempotents
import Langlands.GroupScheme.CoalgebraUnipotence.ConilpotenceFromMatrix
import Langlands.GroupScheme.UnipotentMatrixCriterion.Criterion
import Langlands.GroupScheme.KostantRosenlicht.Hopf

/-!
# Connectedness of characteristic-zero unipotent coordinate algebras

Translations act locally unipotently on the coordinate algebra. They therefore
fix its idempotents. Over an algebraically closed field, reduced rational-point
density makes those idempotents constant.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Unipotent

open AffineLinearEmbedding CoalgebraUnipotence KostantRosenlicht

section Coalgebra

variable {k B : Type*} [Field k] [Ring B] [Bialgebra k B]

theorem rightAct_sub_functionals (g f : Module.Dual k B) :
    rightAct (g - f) = rightAct g - rightAct f := by
  simp only [rightAct, LinearMap.lTensor_sub, LinearMap.sub_comp, LinearMap.comp_sub]

/-- Membership in the reduced filtration bounds nilpotence of each reduced
translation on the given vector. -/
theorem pow_rightAct_eq_zero_of_mem_reducedLevel (n : ℕ)
    (g : Module.Dual k B) (hg : g 1 = 0) {b : B}
    (hb : b ∈ reducedLevel k B n) : (rightAct g ^ n) b = 0 := by
  induction n generalizing b with
  | zero => simpa using (mem_reducedLevel_zero b).mp hb
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply]
    exact ih ((mem_reducedLevel_succ n b).mp hb g hg)

end Coalgebra

variable {k : Type u} [Field k] [CharZero k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

omit [CharZero k] in
/-- Every coordinate translation of a unipotent group is locally unipotent. -/
theorem charTranslate_locally_unipotent
    (hU : IsUnipotent (Corepresented.groupScheme F e))
    (v : B →ₐ[CommRingCat.of k] CommRingCat.of k) :
    ∀ b : B, ∃ m : ℕ, (((charTranslate e v).toLinearMap - 1) ^ m) b = 0 := by
  let := bialgebra e
  have hmatrix : IsMatrixUnipotent k B :=
    (UnipotentMatrixCriterion.corepresentedMatrixUnipotence k F B e).mp hU
  have hB := isLocallyConilpotent_of_isMatrixUnipotent hmatrix
  let ε : Module.Dual k B := Coalgebra.counit
  have hdiff : (charTranslate e v).toLinearMap - 1 = rightAct (v.toLinearMap - ε) := by
    rw [rightAct_sub_functionals]
    have hv : (charTranslate e v).toLinearMap = rightAct v.toLinearMap :=
      LinearMap.ext (charTranslate_eq_rightAct e v)
    have he : rightAct ε = (1 : Module.End k B) := by
      ext b
      exact rightAct_counit b
    rw [hv, he]
  intro b
  obtain ⟨m, hm⟩ := hB b
  refine ⟨m, ?_⟩
  rw [hdiff]
  exact pow_rightAct_eq_zero_of_mem_reducedLevel m (v.toLinearMap - ε)
    (by simp [ε]) hm

/-- Coordinate translations fix idempotents in characteristic zero. -/
theorem charTranslate_idempotent_fixed [IsNoetherianRing B]
    (hU : IsUnipotent (Corepresented.groupScheme F e))
    (v : B →ₐ[CommRingCat.of k] CommRingCat.of k) {b : B}
    (hb : IsIdempotentElem b) : charTranslate e v b = b := by
  let := finite_idempotents_of_noetherian B
  exact idempotent_fixed_of_locally_unipotent
    (charTranslate e v) (charTranslate e (charInv e v))
    (charTranslate_charTranslate_charInv e v)
    (charTranslate_locally_unipotent e hU v) hb

set_option linter.defProp false in
/-- A reduced, finitely generated coordinate algebra of a unipotent group over
an algebraically closed characteristic-zero field has connected spectrum. -/
def connectedSpace_primeSpectrum_of_isUnipotent [IsAlgClosed k]
    [Algebra.FiniteType (CommRingCat.of k) B] [IsReduced B]
    (hU : IsUnipotent (Corepresented.groupScheme F e)) :
    ConnectedSpace (PrimeSpectrum B) := by
  let : IsNoetherianRing B :=
    Algebra.FiniteType.isNoetherianRing (CommRingCat.of k) B
  let : Nontrivial B := (counit e).toRingHom.domain_nontrivial
  let := bialgebra e
  have hconstant : ∀ b : B, IsIdempotentElem b →
      b = algebraMap (CommRingCat.of k) B (counit e b) := by
    intro b hb
    apply sub_eq_zero.mp
    apply eq_zero_of_forall_algHom (k := CommRingCat.of k)
    intro v
    have h := apply_leftAct v.toLinearMap (Coalgebra.counit (R := k) (A := B)) b
    rw [leftAct_counit, ← charTranslate_eq_rightAct e v,
      charTranslate_idempotent_fixed e hU v hb] at h
    have heval : v b = counit e b := h
    simp [heval]
  apply connectedSpace_iff_clopen.mpr
  refine ⟨inferInstance, ?_⟩
  intro s hs
  obtain ⟨b, hb, rfl⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hs
  have hc := hconstant b hb
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (hb.map (counit e)) with h0 | h1
  · left
    have hb0 : b = 0 := by simpa [h0] using hc
    simp [hb0]
  · right
    have hb1 : b = 1 := by simpa [h1] using hc
    simp [hb1]

end Langlands.GroupScheme.Unipotent
