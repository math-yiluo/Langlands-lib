import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.PicardGroup
import Langlands.GroupScheme.Torus.Lattice

/-! # Group algebras of finite integer lattices

For a commutative domain `R` and a finite type `I`, the group algebra `R[ℤ^I]` is the ring of
Laurent polynomials in the variables indexed by `I`. Its units are the monomials with unit
coefficients, it is a unique factorization domain when `R` is, and over a field its Picard
group is trivial. -/

noncomputable section

universe u v

open Polynomial

namespace Langlands.IntLatticeAlgebra

variable (R : Type v) [CommRing R]

/-- The group algebra of `ℤ^(Option I)` is the Laurent polynomial ring in one more variable over
the group algebra of `ℤ^I`. -/
def optionEquiv (I : Type u) :
    AddMonoidAlgebra R (Option I → ℤ) ≃ₐ[R] AddMonoidAlgebra (AddMonoidAlgebra R (I → ℤ)) ℤ :=
  (AddMonoidAlgebra.domCongr R R (RingEquiv.piOptionEquivProd (R := fun _ => ℤ)).toAddEquiv).trans
    (AddMonoidAlgebra.curryAlgEquiv R)

theorem optionEquiv_symm_single_single {I : Type u} (n : ℤ) (m : I → ℤ) (c : R) :
    (optionEquiv R I).symm (AddMonoidAlgebra.single n (AddMonoidAlgebra.single m c)) =
      AddMonoidAlgebra.single
        ((RingEquiv.piOptionEquivProd (R := fun _ => ℤ)).symm (n, m)) c := by
  rw [optionEquiv, AlgEquiv.symm_trans_apply, AddMonoidAlgebra.curryAlgEquiv_symm_single,
    AddMonoidAlgebra.domCongr_symm, AddMonoidAlgebra.domCongr_single]
  rfl

/-- The lattice isomorphism `ℤ^I ≃ ℤ^J` induced by `e : I ≃ J`. -/
def lattice {I J : Type u} (e : I ≃ J) : (I → ℤ) ≃+ (J → ℤ) :=
  (LinearEquiv.funCongrLeft ℤ ℤ e.symm).toAddEquiv

/-- Changing the index type of the lattice. -/
def congrEquiv {I J : Type u} (e : I ≃ J) :
    AddMonoidAlgebra R (I → ℤ) ≃ₐ[R] AddMonoidAlgebra R (J → ℤ) :=
  AddMonoidAlgebra.domCongr R R (lattice e)

/-- A Laurent polynomial ring over a unique factorization domain is a unique factorization
domain. -/
theorem uniqueFactorizationMonoid_laurent (S : Type v) [CommRing S] [IsDomain S]
    [UniqueFactorizationMonoid S] : UniqueFactorizationMonoid (LaurentPolynomial S) :=
  UniqueFactorizationMonoid.of_isLocalization (Submonoid.powers (X : S[X])) _

variable [IsDomain R]

/-- The group algebra of a finite integer lattice over a unique factorization domain is a unique
factorization domain. -/
theorem uniqueFactorizationMonoid [UniqueFactorizationMonoid R] (I : Type u) [Finite I] :
    UniqueFactorizationMonoid (AddMonoidAlgebra R (I → ℤ)) := by
  induction I using Finite.induction_empty_option with
  | of_equiv e h =>
    exact (congrEquiv R e).toMulEquiv.uniqueFactorizationMonoid h
  | h_empty =>
    exact (AddMonoidAlgebra.uniqueAlgEquiv R (PEmpty → ℤ)).symm.toMulEquiv.uniqueFactorizationMonoid
      inferInstance
  | @h_option I _ h =>
    have := uniqueFactorizationMonoid_laurent (AddMonoidAlgebra R (I → ℤ))
    exact (optionEquiv R I).symm.toMulEquiv.uniqueFactorizationMonoid this

/-- Units of the group algebra of a finite integer lattice over a domain are monomials with unit
coefficients. -/
theorem exists_eq_single_of_isUnit (I : Type u) [Finite I] :
    ∀ {f : AddMonoidAlgebra R (I → ℤ)}, IsUnit f →
      ∃ (m : I → ℤ) (c : Rˣ), f = AddMonoidAlgebra.single m (c : R) := by
  induction I using Finite.induction_empty_option with
  | @of_equiv I J e h =>
    intro f hf
    obtain ⟨m, c, hm⟩ := h (hf.map (congrEquiv R e).symm)
    refine ⟨lattice e m, c, ?_⟩
    rw [← (congrEquiv R e).apply_symm_apply f, hm, congrEquiv, AddMonoidAlgebra.domCongr_single]
  | h_empty =>
    intro f hf
    let e := AddMonoidAlgebra.uniqueAlgEquiv R (A := R) (PEmpty → ℤ)
    refine ⟨0, (hf.map e).unit, ?_⟩
    rw [IsUnit.unit_spec]
    conv_lhs => rw [← e.symm_apply_apply f]
    exact AddMonoidAlgebra.uniqueAlgEquiv_symm_apply R (PEmpty → ℤ) (e f)
  | @h_option I _ h =>
    intro f hf
    obtain ⟨c, n, hcn⟩ :=
      Langlands.GroupScheme.Gm.exists_eq_C_mul_T_of_isUnit (hf.map (optionEquiv R I))
    obtain ⟨m, d, hd⟩ := h c.isUnit
    refine ⟨(RingEquiv.piOptionEquivProd (R := fun _ => ℤ)).symm (n, m), d, ?_⟩
    rw [← (optionEquiv R I).symm_apply_apply f, hcn, hd, ← LaurentPolynomial.single_eq_C_mul_T,
      optionEquiv_symm_single_single]

end Langlands.IntLatticeAlgebra

namespace Langlands.IntLatticeAlgebra

variable (K : Type v) [Field K] (I : Type u) [Finite I]

/-- Every invertible module over the group algebra of a finite integer lattice over a field is
free: its Picard group is trivial. -/
theorem subsingleton_pic : Subsingleton (CommRing.Pic (AddMonoidAlgebra K (I → ℤ))) := by
  have := uniqueFactorizationMonoid K I
  infer_instance

end Langlands.IntLatticeAlgebra
