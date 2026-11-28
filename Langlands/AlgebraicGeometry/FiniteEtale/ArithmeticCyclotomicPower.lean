import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.PrimeField
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Cyclotomic powers over arithmetic fields -/

noncomputable section
universe u

open IntermediateField Polynomial

namespace Langlands.AlgebraicGeometry.FiniteEtale

private theorem primeFieldPower (K C : Type*) [Field K] [Field C] [IsAlgClosed C]
    [Algebra (⊥ : Subfield K) C] [IsAlgClosure (⊥ : Subfield K) C]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ q : ℕ, 1 < q ∧ ∀ n : ℕ, ∃ σ : C ≃ₐ[↥(⊥ : Subfield K)] C,
      ∀ z : C, z ^ (ℓ ^ n) = 1 → σ z = z ^ q := by
  let F := (⊥ : Subfield K)
  obtain h | ⟨p, hp, hchar⟩ := CharP.exists' K
  · have : CharZero F := (Subfield.subtype F).charZero
    have : CharZero C := charZero_of_injective_algebraMap (algebraMap F C).injective
    refine ⟨ℓ + 1, by have := ‹Fact ℓ.Prime›.out.two_le; omega, ?_⟩
    intro n
    have hm : 0 < ℓ ^ n := pow_pos ‹Fact ℓ.Prime›.out.pos _
    let : NeZero ((ℓ ^ n : ℕ) : F) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
    let : NeZero ((ℓ ^ n : ℕ) : C) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
    have hirr : Irreducible (cyclotomic (ℓ ^ n) F) := by
      rw [← map_cyclotomic _ (Subfield.botEquivRat (K := K)).symm.toRingHom]
      exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv (Subfield.botEquivRat (K := K)).symm)).2
        (cyclotomic.irreducible_rat hm)
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot C (ℓ ^ n)
    have hbase : (ℓ + 1).Coprime ℓ := by
      rw [add_comm, Nat.coprime_add_self_left]
      exact Nat.coprime_one_left ℓ
    have hcop : (ℓ + 1).Coprime (ℓ ^ n) := hbase.pow_right n
    have hz' := hz.pow_of_coprime (ℓ + 1) hcop
    have heq : minpoly F (z ^ (ℓ + 1)) = minpoly F z :=
      (hz'.minpoly_eq_cyclotomic_of_irreducible hirr).symm.trans
        (hz.minpoly_eq_cyclotomic_of_irreducible hirr)
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic z)
      (heq ▸ minpoly.aeval F (z ^ (ℓ + 1)))
    refine ⟨σ, ?_⟩
    intro y hy
    obtain ⟨m, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hy
    rw [map_pow, hσ, pow_right_comm]
  · let : Algebra (ZMod p) K := ZMod.algebra K p
    have : CharP F p := (Subfield.subtype F).charP (Subfield.subtype F).injective p
    have : CharP C p := charP_of_injective_algebraMap (algebraMap F C).injective p
    let σ := AlgEquiv.ofRingEquiv (f := frobeniusEquiv C p) (R := F) (by
      intro x
      obtain ⟨y, rfl⟩ := (Subfield.botEquivZMod (K := K) p).symm.surjective x
      rw [← ZMod.natCast_zmod_val y, map_natCast, map_natCast, map_natCast])
    exact ⟨p, hp.out.one_lt, fun _ ↦ ⟨σ, fun _ _ ↦ rfl⟩⟩

private theorem extendConstantAutomorphism {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsAlgClosed E] {ι : Type*} {x : ι → E} (hx : AlgebraicIndependent F x)
    [Algebra.IsAlgebraic (adjoin F (Set.range x)) E]
    (σ : algebraicClosure F E ≃ₐ[F] algebraicClosure F E) :
    ∃ φ : E ≃ₐ[↥(adjoin F (Set.range x))] E,
      ∀ c : algebraicClosure F E, φ c = (σ c : E) := by
  let C := algebraicClosure F E
  let T := adjoin F (Set.range x)
  let B := adjoin C (Set.range x)
  have hCB : AlgebraicIndependent C x := hx.extendScalars C
  have hTB : T ≤ B.restrictScalars F := adjoin_le_iff.mpr (subset_adjoin C _)
  let : Algebra T B := (IntermediateField.inclusion hTB).toRingHom.toAlgebra
  have : IsScalarTower T B E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  have : Algebra.IsAlgebraic B E := Algebra.IsAlgebraic.tower_top (K := T) (A := E) B
  let α := hCB.aevalEquivField.toRingEquiv
  let β := IsFractionRing.ringEquivOfRingEquiv
    (K := FractionRing (MvPolynomial ι C)) (L := FractionRing (MvPolynomial ι C))
    (MvPolynomial.mapEquiv ι σ.toRingEquiv)
  let τ := (α.symm.trans β).trans α
  have hτ : ∀ P : MvPolynomial ι C, (τ (hCB.aevalEquivField (algebraMap _ _ P)) : E) =
      MvPolynomial.aeval x (MvPolynomial.map σ.toRingHom P) := by
    intro P
    change (α (β (α.symm (α (algebraMap _ _ P)))) : E) = _
    rw [RingEquiv.symm_apply_apply, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact hCB.aevalEquivField_algebraMap_apply_coe _
  have hτc (c : C) : (τ (algebraMap C B c) : E) = (σ c : E) := by
    have hc : hCB.aevalEquivField (algebraMap _ _ (MvPolynomial.C c)) = algebraMap C B c :=
      Subtype.ext (by rw [hCB.aevalEquivField_algebraMap_apply_coe, MvPolynomial.aeval_C]; rfl)
    rw [← hc, hτ, MvPolynomial.map_C, MvPolynomial.aeval_C]
    rfl
  have : IsScalarTower F B E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  let τF : B →ₐ[F] E :=
    { toRingHom := (algebraMap B E).comp τ.toRingHom
      commutes' := fun c ↦ by
        change (τ (algebraMap F B c) : E) = algebraMap F E c
        rw [IsScalarTower.algebraMap_apply F C B, hτc, AlgEquiv.commutes,
          IntermediateField.coe_algebraMap_apply] }
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic
    (K := F) (L := B) (E := E) (M := E) τF
  have hφB (b : B) : φ (algebraMap B E b) = (τ b : E) :=
    DFunLike.congr_fun hφ b
  have hφT : φ.comp T.val = T.val := by
    apply adjoin_algHom_ext
    rintro _ ⟨i, rfl⟩
    let P : MvPolynomial ι C := MvPolynomial.X i
    have hxP : (hCB.aevalEquivField (algebraMap _ _ P) : E) = x i := by
      rw [hCB.aevalEquivField_algebraMap_apply_coe]; simp [P]
    change φ (x i) = x i
    calc
      φ (x i) = φ (algebraMap B E (hCB.aevalEquivField (algebraMap _ _ P))) := congrArg φ hxP.symm
      _ = x i := by rw [hφB, hτ]; simp [P]
  let φT : E →ₐ[T] E :=
    { toRingHom := φ.toRingHom
      commutes' := DFunLike.congr_fun hφT }
  have : IsAlgClosure T E := ⟨inferInstance, inferInstance⟩
  let e := AlgEquiv.ofBijective φT (AlgHom.normal_bijective T E E φT)
  refine ⟨e, fun c ↦ ?_⟩
  change φ (c : E) = _
  rw [show (c : E) = algebraMap B E (algebraMap C B c) from rfl, hφB, hτc]

private theorem pow_apply_eq_of_root_action {T E : Type*} [Field T] [Field E] [Algebra T E]
    (σ : E ≃ₐ[T] E) (m q : ℕ) (hσ : ∀ z : E, z ^ m = 1 → σ z = z ^ q)
    (j : ℕ) {z : E} (hz : z ^ m = 1) : (σ ^ j) z = z ^ (q ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, AlgEquiv.mul_apply, hσ z hz, map_pow, ih, ← pow_mul, pow_succ]

/-- A field purely inseparable over a finitely generated field admits one positive integral
cyclotomic power greater than one at every level of a prime-power tower. -/
def ArithmeticCyclotomicPowerStatement : Prop :=
  ∀ (K : Type u) [Field K] (k : Subfield K), Field.FG k → IsPurelyInseparable k K →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ q : ℕ, 1 < q ∧
      ∀ n : ℕ, ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
        ∀ z : SeparableClosure K, z ^ (ℓ ^ n) = 1 → σ z = z ^ q

set_option maxHeartbeats 500000 in
/-- A cyclotomic power over the prime field extends across a transcendence basis. One power
of its permutation on field embeddings then fixes the finitely generated field. -/
theorem arithmeticCyclotomicPower : ArithmeticCyclotomicPowerStatement := by
  intro K _ k hk hpure ℓ hℓ
  classical
  let F := (⊥ : Subfield k)
  let E := AlgebraicClosure K
  let C := algebraicClosure F E
  have : IsAlgClosed C := IsAlgClosure.isAlgClosed F
  obtain ⟨q, hq, hpow⟩ := primeFieldPower k C ℓ
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' F k
  let T := adjoin F (Set.range x)
  let xE := (IsScalarTower.toAlgHom F k E) ∘ x
  let TE := adjoin F (Set.range xE)
  have hmap : T.map (IsScalarTower.toAlgHom F k E) = TE := by
    change (adjoin F (Set.range x)).map _ = adjoin F (Set.range xE)
    rw [adjoin_map, Set.range_comp]
  let eT : T ≃ₐ[F] TE := (IntermediateField.equivMap _ _).trans (IntermediateField.equivOfEq hmap)
  have : Algebra.EssFiniteType F k := Field.fg_iff_essFiniteType.mp hk
  have : Algebra.EssFiniteType T k := Algebra.EssFiniteType.of_comp F T k
  have : Algebra.IsAlgebraic T k := hx.isAlgebraic_field
  have : Module.Finite T k := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : Algebra.IsAlgebraic k K := IsPurelyInseparable.isAlgebraic k K
  have : Algebra.IsAlgebraic k E := Algebra.IsAlgebraic.trans k K E
  have : Algebra.IsAlgebraic T E := Algebra.IsAlgebraic.trans T k E
  have : Algebra.IsAlgebraic TE E := by
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨P, hP, hz⟩ := Algebra.IsAlgebraic.isAlgebraic (R := T) z
    refine ⟨P.map eT.toRingHom, (Polynomial.map_ne_zero_iff eT.injective).mpr hP, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap TE E).comp eT.toRingHom = algebraMap T E := rfl
    rwa [hcomp, ← Polynomial.aeval_def]
  have hxE : AlgebraicIndependent F xE := hx.1.map (IsScalarTower.toAlgHom F k E).injective.injOn
  let d := Nat.card (Equiv.Perm (k →ₐ[T] E))
  have hd : 0 < d := Nat.card_pos
  refine ⟨q ^ d, one_lt_pow₀ hq hd.ne', ?_⟩
  intro n
  obtain ⟨σ, hσ⟩ := hpow n
  obtain ⟨φ, hφ⟩ := extendConstantAutomorphism hxE σ
  let ψ : E ≃ₐ[T] E := AlgEquiv.ofRingEquiv (f := φ.toRingEquiv) (fun z ↦ φ.commutes (eT z))
  let perm : (E ≃ₐ[T] E) →* Equiv.Perm (k →ₐ[T] E) :=
    { toFun := fun u ↦ AlgEquiv.arrowCongr (AlgEquiv.refl : k ≃ₐ[T] k) u
      map_one' := by ext f z; rfl
      map_mul' := by intro u v; ext f z; rfl }
  have hfix (z : k) : (ψ ^ d) (algebraMap k E z) = algebraMap k E z := by
    have hperm : perm (ψ ^ d) = 1 := (map_pow perm ψ d).trans pow_card_eq_one'
    exact DFunLike.congr_fun (DFunLike.congr_fun hperm (Algebra.ofId k E |>.restrictScalars T)) z
  obtain ⟨p, hp⟩ := ExpChar.exists k
  let : ExpChar k p := hp
  let : ExpChar E p := expChar_of_injective_ringHom (algebraMap k E).injective p
  have hfixK (z : K) : (ψ ^ d) (algebraMap K E z) = algebraMap K E z := by
    obtain ⟨j, y, hy⟩ := IsPurelyInseparable.pow_mem k p z
    have hh : (algebraMap K E z) ^ (p ^ j) = algebraMap k E y := by
      rw [← map_pow, ← hy, ← IsScalarTower.algebraMap_apply]
    apply iterateFrobenius_inj E p j
    change ((ψ ^ d) (algebraMap K E z)) ^ (p ^ j) = _ ^ (p ^ j)
    rw [← map_pow, hh, hfix]
  let φK : E ≃ₐ[K] E := AlgEquiv.ofRingEquiv (f := (ψ ^ d).toRingEquiv) hfixK
  refine ⟨φK.separableClosure, fun z hz ↦ Subtype.ext ?_⟩
  change (ψ ^ d) (z : E) = (z : E) ^ (q ^ d)
  apply pow_apply_eq_of_root_action ψ (ℓ ^ n) q _ d (congrArg Subtype.val hz)
  intro w hw
  have hmem : w ∈ C := by
    refine mem_algebraicClosure_iff'.mpr ⟨X ^ (ℓ ^ n) - Polynomial.C 1,
      monic_X_pow_sub_C _ (pow_ne_zero _ hℓ.out.ne_zero), ?_⟩
    change aeval w ((X : F[X]) ^ (ℓ ^ n) - Polynomial.C 1) = 0
    rw [map_sub, map_pow, aeval_X, aeval_C, map_one, hw, sub_self]
  have hroot : (⟨w, hmem⟩ : C) ^ (ℓ ^ n) = 1 := Subtype.ext hw
  change φ ((⟨w, hmem⟩ : C) : E) = _
  rw [hφ, hσ _ hroot]
  rfl

end Langlands.AlgebraicGeometry.FiniteEtale
