import Langlands.Algebra.EssFinitePresentationFiberwiseFlatness
import Langlands.Algebra.LocalTowerResidueFiberSystem
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Rank one reflected from the residue fibre of a local algebra

This is an internal consequence of the published essentially finitely presented
fibrewise flatness criterion and the finite-flat freeness theorem for local rings.
-/

open scoped TensorProduct

universe uR uA uB uM

namespace Langlands.Algebra.LocalFiberRankOne

section FlatLocal

variable (A : Type uA) (B : Type uB) (M : Type uM)
  [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
  [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- Rank one of a finite module descends along a flat local ring map. -/
theorem nonempty_linearEquiv_of_flatLocalBaseChange
    (e : (B ⊗[A] M) ≃ₗ[B] B) : Nonempty (M ≃ₗ[A] A) := by
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Module.Flat B (B ⊗[A] M) := Module.Flat.of_linearEquiv e
  have : Module.Flat A M := Module.Flat.of_flat_tensorProduct A M B
  have : Module.Free A M := Module.free_of_flat_of_isLocalRing
  have hrank : Module.finrank A M = 1 := by
    calc
      Module.finrank A M = Module.finrank B (B ⊗[A] M) :=
        (Module.finrank_baseChange (R := B) (S := A) (M' := M)).symm
      _ = Module.finrank B B := e.finrank_eq
      _ = 1 := Module.finrank_self B
  obtain ⟨b⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hrank
  exact ⟨b.symm⟩

/-- Choose a rank-one trivialization descended along a flat local map. -/
noncomputable def linearEquivOfFlatLocalBaseChange
    (e : (B ⊗[A] M) ≃ₗ[B] B) : M ≃ₗ[A] A :=
  (nonempty_linearEquiv_of_flatLocalBaseChange A B M e).some

end FlatLocal

section ResidueFiber

variable (R : Type uR) (A : Type uA) (M : Type uM)
  [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
  [Algebra R A] [IsLocalHom (algebraMap R A)]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  [Module.FinitePresentation A M] [Module.Flat R M]

/-- A finitely presented, base-flat module over an essentially finitely
presented local algebra is free of rank one if its actual residue fibre is. -/
theorem nonempty_linearEquiv_of_residueFiber
    (hRA : EssFinitePresentation R A)
    (e : ((A ⊗[R] IsLocalRing.ResidueField R) ⊗[A] M) ≃ₗ[
      A ⊗[R] IsLocalRing.ResidueField R] (A ⊗[R] IsLocalRing.ResidueField R)) :
    Nonempty (M ≃ₗ[A] A) := by
  let F := A ⊗[R] IsLocalRing.ResidueField R
  have : Nontrivial M := by
    by_contra hM
    have : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
    have hzero : (0 : F) = 1 := by
      calc
        0 = e 0 := (map_zero e).symm
        _ = e (e.symm 1) := congrArg e (Subsingleton.elim _ _)
        _ = 1 := e.apply_symm_apply 1
    exact zero_ne_one hzero
  have : Module.Flat F (F ⊗[A] M) := Module.Flat.of_linearEquiv e
  have : Module.Flat A M :=
    (essFinitePresentationFiberwiseFlatness R A A M hRA hRA
      inferInstance inferInstance inferInstance inferInstance).2
  have : Module.Free A M := Module.free_of_flat_of_isLocalRing
  have hrank : Module.finrank A M = 1 := by
    calc
      Module.finrank A M = Module.finrank F (F ⊗[A] M) :=
        (Module.finrank_baseChange (R := F) (S := A) (M' := M)).symm
      _ = Module.finrank F F := e.finrank_eq
      _ = 1 := Module.finrank_self F
  obtain ⟨b⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hrank
  exact ⟨b.symm⟩

/-- A choice of an actual rank-one trivialization reflected from the residue
fibre; no compatibility with the input fibre trivialization is asserted. -/
noncomputable def linearEquivOfResidueFiber
    (hRA : EssFinitePresentation R A)
    (e : ((A ⊗[R] IsLocalRing.ResidueField R) ⊗[A] M) ≃ₗ[
      A ⊗[R] IsLocalRing.ResidueField R] (A ⊗[R] IsLocalRing.ResidueField R)) :
    M ≃ₗ[A] A :=
  (nonempty_linearEquiv_of_residueFiber R A M hRA e).some

variable (B : Type uB) [CommRing B] [IsLocalRing B]
  [Algebra (A ⊗[R] IsLocalRing.ResidueField R) B]
  [IsLocalHom (algebraMap (A ⊗[R] IsLocalRing.ResidueField R) B)]
  [Module.Flat (A ⊗[R] IsLocalRing.ResidueField R) B]

/-- Residue-fibre rank one can be tested after any flat local extension of
the actual fibre ring. -/
noncomputable def linearEquivOfResidueFiberBaseChange
    (hRA : EssFinitePresentation R A)
    (e : (B ⊗[A ⊗[R] IsLocalRing.ResidueField R]
      ((A ⊗[R] IsLocalRing.ResidueField R) ⊗[A] M)) ≃ₗ[B] B) :
    M ≃ₗ[A] A :=
  linearEquivOfResidueFiber R A M hRA
    (linearEquivOfFlatLocalBaseChange
      (A ⊗[R] IsLocalRing.ResidueField R) B
      ((A ⊗[R] IsLocalRing.ResidueField R) ⊗[A] M) e)

end ResidueFiber

end Langlands.Algebra.LocalFiberRankOne
