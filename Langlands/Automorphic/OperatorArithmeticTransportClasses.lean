import Langlands.Automorphic.OperatorArithmeticTransport

/-! # Arithmetic transport of full automorphic classes and the Galois action

Arithmetic pullback descends to the full-operator classes of actual realizations and to the
classes of actual irreducible cuspidal realizations. For a cuspidal class the pullback is the
unique arithmetic transport, and Galois automorphisms act on cuspidal classes by
`c ↦ c ∘ σ⁻¹`. Both act rank by rank on mixed positive-rank cuspidal classes.
-/

noncomputable section
universe uK uL uM

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M] {n : ℕ}

namespace OperatorRealization

private theorem nonempty_equivalence_refl (S : OperatorRealization K n) :
    Nonempty (S.Equivalence S) :=
  isArithmeticTransport_refl_iff.mp (IsArithmeticTransport.refl S)

/-- Arithmetic pullback preserves and reflects full equivalence. -/
theorem arithmeticComap_equivalence_iff (e : K ≃+* L) {S T : OperatorRealization L n} :
    Nonempty ((S.arithmeticComap e).Equivalence (T.arithmeticComap e)) ↔
      Nonempty (S.Equivalence T) := by
  constructor
  · intro h
    exact (S.isArithmeticTransport_arithmeticComap e).target_equivalent
      ((T.isArithmeticTransport_iff e (S.arithmeticComap e)).mpr h)
  · intro h
    apply (T.isArithmeticTransport_iff e (S.arithmeticComap e)).mp
    exact (isArithmeticTransport_congr (nonempty_equivalence_refl _) h).mp
      (S.isArithmeticTransport_arithmeticComap e)

namespace IsoClass

/-- Descent of arithmetic pullback to full-operator realization classes. -/
def arithmeticComap (e : K ≃+* L) (c : IsoClass L n) : IsoClass K n :=
  Quotient.lift (s := equivalenceSetoid L n) (fun S => (S.arithmeticComap e).isoClass)
    (fun S T hST => ((S.arithmeticComap e).isoClass_eq_iff (T.arithmeticComap e)).mpr
      ((arithmeticComap_equivalence_iff e).mpr hST)) c

@[simp] theorem arithmeticComap_isoClass (e : K ≃+* L) (S : OperatorRealization L n) :
    arithmeticComap e S.isoClass = (S.arithmeticComap e).isoClass := rfl

@[simp] theorem arithmeticComap_refl (c : IsoClass K n) :
    arithmeticComap (RingEquiv.refl K) c = c := by
  refine Quotient.inductionOn c ?_
  intro S
  change (S.arithmeticComap (RingEquiv.refl K)).isoClass = S.isoClass
  rw [OperatorRealization.arithmeticComap_refl]

theorem arithmeticComap_trans (e : K ≃+* L) (a : L ≃+* M) (c : IsoClass M n) :
    arithmeticComap (e.trans a) c = arithmeticComap e (arithmeticComap a c) := by
  refine Quotient.inductionOn c ?_
  intro S
  change (S.arithmeticComap (e.trans a)).isoClass = ((S.arithmeticComap a).arithmeticComap e).isoClass
  rw [OperatorRealization.arithmeticComap_trans]

@[simp] theorem arithmeticComap_symm_arithmeticComap (e : K ≃+* L) (c : IsoClass L n) :
    arithmeticComap e.symm (arithmeticComap e c) = c := by
  rw [← arithmeticComap_trans, RingEquiv.symm_trans_self, arithmeticComap_refl]

@[simp] theorem arithmeticComap_arithmeticComap_symm (e : K ≃+* L) (c : IsoClass K n) :
    arithmeticComap e (arithmeticComap e.symm c) = c := by
  rw [← arithmeticComap_trans, RingEquiv.self_trans_symm, arithmeticComap_refl]

/-- Arithmetic pullback is a bijection of full-operator classes. -/
def arithmeticComapEquiv (e : K ≃+* L) : IsoClass L n ≃ IsoClass K n where
  toFun := arithmeticComap e
  invFun := arithmeticComap e.symm
  left_inv := arithmeticComap_symm_arithmeticComap e
  right_inv := arithmeticComap_arithmeticComap_symm e

end IsoClass
end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
  [CompactSpace (AdeleQuotient M)] {r : ℕ}

namespace IsoClass

/-- Descent of arithmetic pullback to the classes of actual irreducible cuspidal
realizations of rank `r + 1`. -/
def arithmeticComap (e : K ≃+* L) (c : IsoClass L r) : IsoClass K r :=
  Quotient.lift (s := equivalenceSetoid L r) (fun S => (S.arithmeticComap e).isoClass)
    (fun S T hST => ((S.arithmeticComap e).isoClass_eq_iff (T.arithmeticComap e)).mpr
      ((OperatorRealization.arithmeticComap_equivalence_iff e).mpr hST)) c

@[simp] theorem arithmeticComap_isoClass (e : K ≃+* L) (S : CuspidalOperatorRealization L r) :
    arithmeticComap e S.isoClass = (S.arithmeticComap e).isoClass := rfl

@[simp] theorem toOperatorClass_arithmeticComap (e : K ≃+* L) (c : IsoClass L r) :
    (arithmeticComap e c).toOperatorClass =
      OperatorRealization.IsoClass.arithmeticComap e c.toOperatorClass := by
  refine Quotient.inductionOn c ?_
  intro S
  rfl

@[simp] theorem arithmeticComap_refl (c : IsoClass K r) :
    arithmeticComap (RingEquiv.refl K) c = c := by
  apply toOperatorClass_injective
  rw [toOperatorClass_arithmeticComap, OperatorRealization.IsoClass.arithmeticComap_refl]

theorem arithmeticComap_trans (e : K ≃+* L) (a : L ≃+* M) (c : IsoClass M r) :
    arithmeticComap (e.trans a) c = arithmeticComap e (arithmeticComap a c) := by
  apply toOperatorClass_injective
  rw [toOperatorClass_arithmeticComap, toOperatorClass_arithmeticComap,
    toOperatorClass_arithmeticComap, OperatorRealization.IsoClass.arithmeticComap_trans]

@[simp] theorem arithmeticComap_symm_arithmeticComap (e : K ≃+* L) (c : IsoClass L r) :
    arithmeticComap e.symm (arithmeticComap e c) = c := by
  rw [← arithmeticComap_trans, RingEquiv.symm_trans_self, arithmeticComap_refl]

@[simp] theorem arithmeticComap_arithmeticComap_symm (e : K ≃+* L) (c : IsoClass K r) :
    arithmeticComap e (arithmeticComap e.symm c) = c := by
  rw [← arithmeticComap_trans, RingEquiv.self_trans_symm, arithmeticComap_refl]

/-- Arithmetic pullback is a bijection of cuspidal classes. -/
def arithmeticComapEquiv (e : K ≃+* L) : IsoClass L r ≃ IsoClass K r where
  toFun := arithmeticComap e
  invFun := arithmeticComap e.symm
  left_inv := arithmeticComap_symm_arithmeticComap e
  right_inv := arithmeticComap_arithmeticComap_symm e

/-- The class of `S ∘ e⁻¹` is the transport of `c` along `e`: the relation of
`ArithmeticTransportRelation` holds exactly for the pulled-back class. -/
theorem isArithmeticTransport_iff_eq (e : K ≃+* L) (c : IsoClass K r) (d : IsoClass L r) :
    IsArithmeticTransport e c d ↔ c = arithmeticComap e d := by
  refine Quotient.inductionOn₂ c d ?_
  intro S T
  change IsArithmeticTransport e S.isoClass T.isoClass ↔ S.isoClass = arithmeticComap e T.isoClass
  rw [isArithmeticTransport_isoClass_iff, arithmeticComap_isoClass, isoClass_eq_iff]
  exact T.realization.isArithmeticTransport_iff e S.realization

theorem isArithmeticTransport_arithmeticComap_symm (e : K ≃+* L) (c : IsoClass K r) :
    IsArithmeticTransport e c (arithmeticComap e.symm c) :=
  (isArithmeticTransport_iff_eq e c _).mpr (arithmeticComap_arithmeticComap_symm e c).symm

/-- Every cuspidal class has an actual arithmetic transport. -/
theorem exists_isArithmeticTransport (e : K ≃+* L) (c : IsoClass K r) :
    ∃ d : IsoClass L r, IsArithmeticTransport e c d :=
  ⟨_, isArithmeticTransport_arithmeticComap_symm e c⟩

section Galois

variable {F : Type*} [Field F] [Algebra F K]

/-- The Galois conjugate class `c ∘ σ⁻¹`: pullback along `σ⁻¹`. -/
def galoisConj (σ : K ≃ₐ[F] K) (c : IsoClass K r) : IsoClass K r :=
  arithmeticComap σ.toRingEquiv.symm c

theorem isGaloisConjugate_iff (σ : K ≃ₐ[F] K) (c d : IsoClass K r) :
    c.IsGaloisConjugate σ d ↔ d = galoisConj σ c := by
  unfold IsGaloisConjugate
  rw [isArithmeticTransport_iff_eq]
  constructor
  · intro h
    rw [h, galoisConj, arithmeticComap_symm_arithmeticComap]
  · intro h
    rw [h, galoisConj, arithmeticComap_arithmeticComap_symm]

theorem isGaloisConjugate_galoisConj (σ : K ≃ₐ[F] K) (c : IsoClass K r) :
    c.IsGaloisConjugate σ (galoisConj σ c) :=
  (isGaloisConjugate_iff σ c _).mpr rfl

theorem isGaloisStable_iff (σ : K ≃ₐ[F] K) (c : IsoClass K r) :
    c.IsGaloisStable σ ↔ galoisConj σ c = c :=
  (isGaloisConjugate_iff σ c c).trans eq_comm

@[simp] theorem galoisConj_one (c : IsoClass K r) : galoisConj (1 : K ≃ₐ[F] K) c = c :=
  arithmeticComap_refl c

theorem galoisConj_mul (σ τ : K ≃ₐ[F] K) (c : IsoClass K r) :
    galoisConj (σ * τ) c = galoisConj σ (galoisConj τ c) := by
  have h := (isGaloisConjugate_galoisConj τ c).trans (isGaloisConjugate_galoisConj σ (galoisConj τ c))
  exact ((isGaloisConjugate_iff (σ * τ) c _).mp h).symm

/-- The Galois action on actual cuspidal classes, as an installable action. -/
@[instance_reducible]
def galoisAction : MulAction (K ≃ₐ[F] K) (IsoClass K r) where
  smul := galoisConj
  one_smul := galoisConj_one
  mul_smul := galoisConj_mul

end Galois
end IsoClass
end CuspidalOperatorRealization

namespace PositiveRankCuspidalClass

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
  [CompactSpace (AdeleQuotient M)]

/-- Arithmetic pullback in the original positive-rank fiber. -/
def arithmeticComap (e : K ≃+* L) (c : PositiveRankCuspidalClass L) :
    PositiveRankCuspidalClass K :=
  ⟨c.1, c.2.arithmeticComap e⟩

@[simp] theorem rankIndex_arithmeticComap (e : K ≃+* L) (c : PositiveRankCuspidalClass L) :
    (c.arithmeticComap e).rankIndex = c.rankIndex := rfl

@[simp] theorem rank_arithmeticComap (e : K ≃+* L) (c : PositiveRankCuspidalClass L) :
    (c.arithmeticComap e).rank = c.rank := rfl

@[simp] theorem arithmeticComap_ofFixedRank (e : K ≃+* L) {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass L r) :
    (ofFixedRank c).arithmeticComap e = ofFixedRank (c.arithmeticComap e) := rfl

@[simp] theorem arithmeticComap_refl (c : PositiveRankCuspidalClass K) :
    c.arithmeticComap (RingEquiv.refl K) = c := by
  obtain ⟨r, c⟩ := c
  change Sigma.mk r (c.arithmeticComap (RingEquiv.refl K)) = Sigma.mk r c
  rw [CuspidalOperatorRealization.IsoClass.arithmeticComap_refl]

theorem arithmeticComap_trans (e : K ≃+* L) (a : L ≃+* M) (c : PositiveRankCuspidalClass M) :
    c.arithmeticComap (e.trans a) = (c.arithmeticComap a).arithmeticComap e := by
  obtain ⟨r, c⟩ := c
  change Sigma.mk r (c.arithmeticComap (e.trans a)) =
    Sigma.mk r ((c.arithmeticComap a).arithmeticComap e)
  rw [CuspidalOperatorRealization.IsoClass.arithmeticComap_trans]

@[simp] theorem arithmeticComap_symm_arithmeticComap (e : K ≃+* L)
    (c : PositiveRankCuspidalClass L) :
    (c.arithmeticComap e).arithmeticComap e.symm = c := by
  rw [← arithmeticComap_trans, RingEquiv.symm_trans_self, arithmeticComap_refl]

@[simp] theorem arithmeticComap_arithmeticComap_symm (e : K ≃+* L)
    (c : PositiveRankCuspidalClass K) :
    (c.arithmeticComap e.symm).arithmeticComap e = c := by
  rw [← arithmeticComap_trans, RingEquiv.self_trans_symm, arithmeticComap_refl]

/-- Arithmetic pullback is a rank-preserving bijection of mixed positive-rank classes. -/
def arithmeticComapEquiv (e : K ≃+* L) :
    PositiveRankCuspidalClass L ≃ PositiveRankCuspidalClass K where
  toFun := arithmeticComap e
  invFun := arithmeticComap e.symm
  left_inv := arithmeticComap_symm_arithmeticComap e
  right_inv := arithmeticComap_arithmeticComap_symm e

section Galois

variable {F : Type*} [Field F] [Algebra F K]

/-- The Galois conjugate `c ∘ σ⁻¹` of a mixed positive-rank class, in its own rank fiber. -/
def galoisConj (σ : K ≃ₐ[F] K) (c : PositiveRankCuspidalClass K) :
    PositiveRankCuspidalClass K :=
  ⟨c.1, CuspidalOperatorRealization.IsoClass.galoisConj σ c.2⟩

theorem galoisConj_eq_arithmeticComap (σ : K ≃ₐ[F] K) (c : PositiveRankCuspidalClass K) :
    galoisConj σ c = c.arithmeticComap σ.toRingEquiv.symm := rfl

@[simp] theorem rankIndex_galoisConj (σ : K ≃ₐ[F] K) (c : PositiveRankCuspidalClass K) :
    (galoisConj σ c).rankIndex = c.rankIndex := rfl

@[simp] theorem rank_galoisConj (σ : K ≃ₐ[F] K) (c : PositiveRankCuspidalClass K) :
    (galoisConj σ c).rank = c.rank := rfl

@[simp] theorem galoisConj_ofFixedRank (σ : K ≃ₐ[F] K) {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass K r) :
    galoisConj σ (ofFixedRank c) =
      ofFixedRank (CuspidalOperatorRealization.IsoClass.galoisConj σ c) := rfl

@[simp] theorem galoisConj_one (c : PositiveRankCuspidalClass K) :
    galoisConj (1 : K ≃ₐ[F] K) c = c := by
  obtain ⟨r, c⟩ := c
  change Sigma.mk r (CuspidalOperatorRealization.IsoClass.galoisConj (1 : K ≃ₐ[F] K) c) =
    Sigma.mk r c
  rw [CuspidalOperatorRealization.IsoClass.galoisConj_one]

theorem galoisConj_mul (σ τ : K ≃ₐ[F] K) (c : PositiveRankCuspidalClass K) :
    galoisConj (σ * τ) c = galoisConj σ (galoisConj τ c) := by
  obtain ⟨r, c⟩ := c
  change Sigma.mk r (CuspidalOperatorRealization.IsoClass.galoisConj (σ * τ) c) =
    Sigma.mk r (CuspidalOperatorRealization.IsoClass.galoisConj σ
      (CuspidalOperatorRealization.IsoClass.galoisConj τ c))
  rw [CuspidalOperatorRealization.IsoClass.galoisConj_mul]

/-- A fixed-rank class is `σ`-stable exactly when its mixed class is fixed by `σ`. -/
theorem isGaloisStable_iff_galoisConj_ofFixedRank (σ : K ≃ₐ[F] K) {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass K r) :
    c.IsGaloisStable σ ↔ galoisConj σ (ofFixedRank c) = ofFixedRank c := by
  rw [CuspidalOperatorRealization.IsoClass.isGaloisStable_iff, galoisConj_ofFixedRank,
    (ofFixedRank_injective r).eq_iff]

/-- The rank-preserving Galois action on mixed positive-rank cuspidal classes, as an
installable action. -/
@[instance_reducible]
def galoisAction : MulAction (K ≃ₐ[F] K) (PositiveRankCuspidalClass K) where
  smul := galoisConj
  one_smul := galoisConj_one
  mul_smul := galoisConj_mul

end Galois
end PositiveRankCuspidalClass
end Langlands.Automorphic
