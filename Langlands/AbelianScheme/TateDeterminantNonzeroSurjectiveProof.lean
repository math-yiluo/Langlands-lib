import Langlands.AbelianScheme.TateDeterminantNonzeroSurjectiveStatement
import Langlands.AbelianScheme.Tate.PrimePowerTorsionDensity
import Langlands.AbelianScheme.Tate.RestrictedProductProof
import Langlands.AbelianScheme.Tate.PrimeAdicSeparation
import Langlands.AbelianScheme.Tate.GeometricPrimeAdicRankProof
import Langlands.AbelianScheme.AlgClosedPointDivisibility
import Langlands.AbelianScheme.StructureCohomologyVanishing

/-! # An endomorphism with invertible rational Tate map is surjective -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.TateDeterminantNonzeroSurjective

open GroupScheme.Tate

variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : AbelianScheme (Spec (CommRingCat.of k))) (p : ℕ) [Fact p.Prime]

omit [IsAlgClosed k] in
/-- Iterated transitions: the section at level `n` is `p ^ m` times the section at
level `n + m`. -/
theorem toSection_evaluation_add (x : PrimeAdic.Integral A.toGrp (Over.mk (𝟙 _)) p)
    (n m : ℕ) :
    toSection A.toGrp (Over.mk (𝟙 _)) (p ^ n) (PrimeAdic.evaluation A.toGrp _ p n x) =
      p ^ m • toSection A.toGrp (Over.mk (𝟙 _)) (p ^ (n + m))
        (PrimeAdic.evaluation A.toGrp _ p (n + m) x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih, ← PrimeAdic.evaluation_transition A.toGrp _ p (n + m) x,
      PrimeAdic.toSection_transition_succ, smul_smul, ← pow_succ]
    rfl

/-- If the rational Tate map of `α` is surjective, every `p`-power torsion section lifts
through `α`. -/
theorem exists_lift [CharZero k] (α : A ⟶ A)
    (hsurj : Function.Surjective (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α))
    (n : ℕ) (s : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X) (hs : s ^ (p ^ n) = 1) :
    ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X, z ≫ (groupHom α).hom.hom = s := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  have hdiv : ∀ y : T ⟶ A.toGrp.X, ∃ x, x ^ p = y := fun y =>
    algClosedPointDivisibility _ A k (𝟙 _) p
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) y
  let y : Level A.toGrp T (p ^ n) :=
    Additive.ofMul ⟨s, (mem_levelGroup A.toGrp T (p ^ n) s).mpr hs⟩
  obtain ⟨x, hx⟩ := PrimeAdic.evaluation_surjective_of_pow A.toGrp T p hdiv n y
  obtain ⟨w, hw⟩ := hsurj (PrimeAdic.toRational A.toGrp T p x)
  obtain ⟨m, w', hw'⟩ := PrimeAdic.exists_prime_pow_nsmul_mem_integralImage A.toGrp T p w
  have hmap : PrimeAdic.map T p (groupHom α) w' = ((p ^ m : ℕ) : ℤ_[p]) • x := by
    apply PrimeAdic.toRational_injective A.toGrp T p
    rw [map_smul, Nat.cast_smul_eq_nsmul]
    have h1 : PrimeAdic.toRational A.toGrp T p (PrimeAdic.map T p (groupHom α) w') =
        Tate.PrimeAdic.rationalMap T p α (PrimeAdic.toRational A.toGrp T p w') := by
      simp [PrimeAdic.toRational_apply]
      rfl
    rw [h1, hw', map_nsmul, hw]
  refine ⟨Additive.toMul (toSection A.toGrp T (p ^ (n + m))
    (PrimeAdic.evaluation A.toGrp T p (n + m) w')), ?_⟩
  have h2 : Additive.toMul (toSection A.toGrp T (p ^ (n + m))
      (PrimeAdic.evaluation A.toGrp T p (n + m) w')) ≫ (groupHom α).hom.hom =
        Additive.toMul (toSection A.toGrp T (p ^ (n + m))
          (PrimeAdic.evaluation A.toGrp T p (n + m) (PrimeAdic.map T p (groupHom α) w'))) :=
    rfl
  rw [h2, hmap, PrimeAdic.evaluation_natCast_smul, map_nsmul,
    ← toSection_evaluation_add A p x n m, hx]
  rfl

/-- If the rational Tate map of `α` is surjective, the underlying morphism of `α` is
surjective. -/
theorem surjective_of_rationalMap [CharZero k] (α : A ⟶ A)
    (hsurj : Function.Surjective (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α)) :
    Surjective (hom α) := by
  have hsub : Tate.PrimePowerTorsion.locus A p ⊆ Set.range (hom α) := by
    rintro _ ⟨n, s, hs, rfl⟩
    obtain ⟨z, hz⟩ := exists_lift A p α hsurj n s hs
    refine ⟨z.left (default : Spec (CommRingCat.of k)), ?_⟩
    rw [← hz, Over.comp_left, Scheme.Hom.comp_apply]
  have : IsProper (hom α ≫ A.X.hom) := by
    rw [show hom α ≫ A.X.hom = A.X.hom from Over.w (groupHom α).hom.hom]
    infer_instance
  have : IsProper (hom α) := .of_comp _ A.X.hom
  have hclosed : IsClosed (Set.range (hom α)) := (hom α).isClosedMap.isClosed_range
  have huniv : Set.range (hom α) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← (Tate.PrimePowerTorsion.dense_locus A p).closure_eq, ← hclosed.closure_eq]
    exact closure_mono hsub
  exact ⟨Set.range_eq_univ.mp huniv⟩

end Langlands.AbelianScheme.TateDeterminantNonzeroSurjective

namespace Langlands.AbelianScheme

/-- In characteristic zero, an endomorphism of an abelian scheme over an algebraically
closed field whose rational `p`-adic Tate map has nonzero determinant is surjective. -/
theorem tateDeterminantNonzeroSurjective : TateDeterminantNonzeroSurjectiveStatement.{u} := by
  intro k _ _ _ A p _ α hdet
  obtain ⟨g, hA⟩ := exists_hasRelativeDimension_of_field A
  have hp : IsUnit ((p : ℕ) : Γ(Scheme.Spec.obj (Opposite.op (CommRingCat.of k)), ⊤)) := by
    have hp' : ((p : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    simpa using (Ne.isUnit hp').map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  obtain ⟨-, hfin, -⟩ := Tate.PrimeAdic.geometricPrimeAdicRank _ A g hA p hp k (𝟙 _)
  have : Module.Finite ℚ_[p] (Tate.PrimeAdic.Rational A
      (Over.mk (𝟙 (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))) p) := hfin
  have hunit : IsUnit (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr hdet.isUnit
  exact TateDeterminantNonzeroSurjective.surjective_of_rationalMap A p α
    ((Module.End.isUnit_iff _).mp hunit).2

end Langlands.AbelianScheme
