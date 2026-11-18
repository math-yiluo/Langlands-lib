import Langlands.GroupScheme.Unipotent.FiniteEtaleOrderStatement
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricRank
import Langlands.Cohomology.Tate.PGroupTateVanishingProof
import Langlands.GroupScheme.Rational.UnipotentCompactSubgroups
import Langlands.GroupScheme.Reductive.InvariantLinearForm
import Langlands.GroupScheme.Unipotent.CharZeroPeriodic
import Langlands.GroupScheme.Unipotent.FieldReflectionProof
import Mathlib.LinearAlgebra.Matrix.CharP

/-! # The order of a finite étale unipotent group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

private theorem isPGroup_rationalPoints_of_isUnipotent {K : Type u} [Field K]
    {p : ℕ} [ExpChar K p] (H : GroupScheme (Spec (CommRingCat.of K)))
    [IsFinite H.X.hom] [Finite (rationalPoints H)] (hH : IsUnipotent H) :
    IsPGroup p (rationalPoints H) := by
  classical
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨n, ρ, hρ, hdiag, hlower⟩ := exists_unitriangular_closedRepresentation H hH
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : Mono ρ.hom.hom := Over.mono_of_mono_left _
  let e : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K) :=
    Matrix.toLinAlgEquiv'
  let r : rationalPoints H →* Matrix (Fin n) (Fin n) K :=
    (Units.coeHom _).comp ρ.rationalMatrix
  have hr : Function.Injective r := Units.val_injective.comp ρ.rationalMatrix_injective
  intro g
  let M := r g - 1
  have htri : M.IsUpperTriangular := by
    intro i j hji
    change j < i at hji
    have hij : i ≠ j := hji.ne'
    change (ρ.rationalMatrix g : Matrix _ _ K) i j - (1 : Matrix _ _ K) i j = 0
    simp [hlower g i j hji, hij]
  have hcharpoly : M.charpoly = (Polynomial.X : Polynomial K) ^ n := by
    rw [Matrix.charpoly_of_isUpperTriangular M htri]
    have hzero (i : Fin n) : M i i = 0 := by
      change (ρ.rationalMatrix g : Matrix _ _ K) i i - (1 : Matrix _ _ K) i i = 0
      simp [hdiag g i]
    simp [hzero]
  have hnil : M ^ n = 0 := by
    simpa [hcharpoly] using Matrix.aeval_self_charpoly M
  rcases expChar_is_prime_or_one K p with hp | rfl
  · refine ⟨n, hr ?_⟩
    rw [map_pow, map_one]
    by_cases hn : Nonempty (Fin n)
    · let := hn
      have hz : M ^ (p ^ n) = 0 := pow_eq_zero_of_le (Nat.lt_pow_self hp.one_lt).le hnil
      change (r g - 1) ^ (p ^ n) = 0 at hz
      rw [sub_pow_expChar_pow_of_commute _ _ (Commute.one_right _), one_pow] at hz
      exact sub_eq_zero.mp hz
    · let : IsEmpty (Fin n) := not_nonempty_iff.mp hn
      exact Subsingleton.elim _ _
  · let : CharZero K := charZero_of_expChar_one' K
    refine ⟨0, ?_⟩
    simp only [one_pow, pow_one]
    apply hr
    rw [map_one]
    apply e.injective
    rw [map_one]
    have hpow : e (r g) ^ Nat.card (rationalPoints H) = 1 := by
      rw [← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]
    refine Unipotent.eq_one_of_isNilpotent_sub_one_of_pow_eq_one ?_ Nat.card_pos.ne' hpow
    rw [← map_one e, ← map_sub]
    exact (show IsNilpotent M from ⟨n, hnil⟩).map e.toRingHom

private theorem isUnipotent_of_isPGroup_rationalPoints {K : Type u} [Field K] [IsAlgClosed K]
    {p : ℕ} [ExpChar K p] (H : GroupScheme (Spec (CommRingCat.of K)))
    [Smooth H.X.hom] [Finite (rationalPoints H)] (hH : IsPGroup p (rationalPoints H)) :
    IsUnipotent H := by
  intro n _ _ _ ρ
  obtain ⟨v, hv⟩ := exists_ne (0 : n → K)
  rcases expChar_is_prime_or_one K p with hp | rfl
  · let : Fact p.Prime := ⟨hp⟩
    let : CharP K p := (expChar_prime_iff K hp).mp inferInstance
    have hkill (w : n → K) : p • w = 0 := by
      rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p, zero_smul]
    obtain ⟨w, _, hw, hfix⟩ :=
      Langlands.Tate.PGroupVanishing.exists_fixed_ne_zero hH ρ.rationalRepresentation hkill hv
    exact ⟨w, hw, (ρ.isFixedVector_iff_rationalRepresentation w).mpr hfix⟩
  · have : Subsingleton (rationalPoints H) := isPGroup_one_iff_subsingleton.mp hH
    refine ⟨v, hv, (ρ.isFixedVector_iff_rationalRepresentation v).mpr (fun g => ?_)⟩
    rw [Subsingleton.elim g 1, map_one]
    rfl

/-- The order of a finite étale group scheme over a field is a power of the characteristic
exponent exactly when the group scheme is unipotent. -/
theorem finiteEtaleUnipotentOrder : FiniteEtaleUnipotentOrderStatement.{u} := by
  intro k _ p _ Ks _ _ _ G _ _
  let K := AlgebraicClosure k
  let b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let H := (GroupScheme.baseChange b).obj G
  have : IsFinite H.X.hom := by
    change IsFinite (pullback.snd G.X.hom b)
    infer_instance
  have : Etale H.X.hom := by
    change Etale (pullback.snd G.X.hom b)
    infer_instance
  have : ExpChar K p := expChar_of_injective_ringHom (algebraMap k K).injective p
  have : IsSepClosed Ks := IsSepClosure.sep_closed k
  let sectionEquiv (L : Type u) [Field L] [Algebra k L] :
      G.affinePoints (CommAlgCat.of k L) ≃
        {x : Spec (CommRingCat.of L) ⟶ G.X.left //
          x ≫ G.X.hom = Spec.map (CommRingCat.ofHom (algebraMap k L))} :=
    { toFun := fun x => ⟨x.left, x.w⟩
      invFun := fun x => Over.homMk x.1 x.2
      left_inv := fun _ => Over.OverMorphism.ext rfl
      right_inv := fun _ => rfl }
  let e : rationalPoints H ≃ G.affinePoints (CommAlgCat.of k K) :=
    (baseChangePointsEquiv b G (Over.mk (𝟙 (Spec (CommRingCat.of K))))).toEquiv
  have : Finite {x : Spec (CommRingCat.of K) ⟶ H.X.left // x ≫ H.X.hom = 𝟙 _} :=
    Langlands.AlgebraicGeometry.FiniteEtale.finite_sections_of_isFinite H.X.hom
  have : Finite (rationalPoints H) :=
    Finite.of_injective (fun x : rationalPoints H => ⟨x.left, x.w⟩ :
      rationalPoints H → {x : Spec (CommRingCat.of K) ⟶ H.X.left // x ≫ H.X.hom = 𝟙 _})
      (fun _ _ hx => Over.OverMorphism.ext (congrArg Subtype.val hx))
  have hcard (L : Type u) [Field L] [Algebra k L] [IsSepClosed L] :
      Nat.card (G.affinePoints (CommAlgCat.of k L)) = G.X.hom.finrank default := by
    let t : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k L))
    calc
      _ = Nat.card {x : Spec (CommRingCat.of L) ⟶ G.X.left // x ≫ G.X.hom = t} :=
        Nat.card_congr (sectionEquiv L)
      _ = G.X.hom.finrank (t default) :=
        Langlands.AlgebraicGeometry.FiniteEtale.natCard_lifts_eq_finrank G.X.hom t default
      _ = _ := congrArg G.X.hom.finrank (Subsingleton.elim _ _)
  have hcompare : Nat.card (rationalPoints H) = Nat.card (G.affinePoints (CommAlgCat.of k Ks)) :=
    (Nat.card_congr e).trans ((hcard K).trans (hcard Ks).symm)
  rw [← hcompare]
  constructor
  · intro h
    have hP := isPGroup_rationalPoints_of_isUnipotent (p := p) H (IsUnipotent.baseChange h)
    rcases expChar_is_prime_or_one K p with hp | rfl
    · let : Fact p.Prime := ⟨hp⟩
      exact hP.exists_card_eq
    · have : Subsingleton (rationalPoints H) := isPGroup_one_iff_subsingleton.mp hP
      exact ⟨0, Nat.card_unique⟩
  · rintro ⟨n, hn⟩
    exact IsUnipotent.of_baseChange (isUnipotent_of_isPGroup_rationalPoints H (IsPGroup.of_card hn))

end Langlands.GroupScheme
