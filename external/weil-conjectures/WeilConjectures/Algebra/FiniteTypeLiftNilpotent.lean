/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.NakayamaNilpotent

/-! # Finite type lifts along a nilpotent ideal

Source: More on Morphisms, Lemma 09ZW, proof, “The translation of (2) into algebra”
(blueprint: lem-weil-pbc-finite-type-lift-nilpotent)
-/

@[expose] public section

open scoped Polynomial

/-- If a quotient by a nilpotent ideal is of finite type, then the original ring map
is of finite type.  This is the ring translation of More on Morphisms, Lemma 09ZW.
The proof lifts generators and applies Nakayama's lemma for a nilpotent ideal.
(blueprint: lem-weil-pbc-finite-type-lift-nilpotent) -/
theorem finiteType_of_quotient_finiteType_nilpotent
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A)
    (hI : ∃ n : ℕ, I ^ (n + 1) = ⊥)
    (hquot : RingHom.FiniteType
      (Ideal.quotientMap (I.map φ) φ (Ideal.le_comap_map))) :
    RingHom.FiniteType φ := by
  classical
  let : Algebra A B := φ.toAlgebra
  have hcomp := hquot.comp (RingHom.FiniteType.of_surjective (Ideal.Quotient.mk I)
    (Ideal.Quotient.mk_surjective))
  rw [Ideal.quotientMap_comp_mk] at hcomp
  have hft : Algebra.FiniteType A (B ⧸ I.map φ) := by
    apply (RingHom.finiteType_algebraMap).mp
    exact hcomp
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  choose b hb using fun j : Fin n ↦ Ideal.Quotient.mk_surjective (f (MvPolynomial.X j))
  let g : MvPolynomial (Fin n) A →ₐ[A] B := MvPolynomial.aeval b
  have hfg : (Ideal.Quotient.mkₐ A (I.map φ)).comp g = f := by
    ext j
    simpa [g] using hb j
  have hmod : Function.Surjective
      ((I • ⊤ : Submodule A (MvPolynomial (Fin n) A)).mapQ
        (I • ⊤ : Submodule A B) g.toLinearMap
        (Submodule.smul_top_le_comap_smul_top I g.toLinearMap)) := by
    intro y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective (I • ⊤ : Submodule A B) y
    obtain ⟨p, hp⟩ := hf (Ideal.Quotient.mk (I.map φ) c)
    refine ⟨Submodule.Quotient.mk p, ?_⟩
    rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
    rw [Ideal.smul_top_eq_map]
    change g p - c ∈ I.map φ
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    have heq : Ideal.Quotient.mk (I.map φ) (g p) = f p :=
      DFunLike.congr_fun hfg p
    rw [heq, hp, sub_self]
  have hsur : Function.Surjective g := by
    apply RingTheory.surjective_of_surjective_mod_nilpotent A
      (MvPolynomial (Fin n) A) B I g.toLinearMap _ hmod
    obtain ⟨k, hk⟩ := hI
    exact ⟨k + 1, Nat.succ_pos k, hk⟩
  exact Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr ⟨n, g, hsur⟩
