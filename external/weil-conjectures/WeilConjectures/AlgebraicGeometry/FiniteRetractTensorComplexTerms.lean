/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.KFlat

import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.Data.Int.Interval

/-! # Terms of an ordinary bounded finite-projective tensor complex

Source: Stacks Project, Tags 0DJQ and 01Y0.
(blueprint: lem-pc-finite-retract-tensor-complex-terms).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

noncomputable local instance tensorComplexTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

private theorem coherent_retract {X : Scheme.{u}}
    {F G : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    (ι : F ⟶ G) (π : G ⟶ F) (h : ι ≫ π = 𝟙 F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    RingedSpace.IsCoherent X.toRingedSpace F := by
  let d : G ⟶ G := 𝟙 G - π ≫ ι
  have hi : ι ≫ d = 0 := by simp [d, Preadditive.comp_sub, ← Category.assoc, h]
  have hk : kernel.ι d ≫ π ≫ ι = kernel.ι d := by
    have hd := kernel.condition d
    have hd' : kernel.ι d - kernel.ι d ≫ π ≫ ι = 0 := by
      simpa only [d, Preadditive.comp_sub, Category.comp_id] using hd
    exact (sub_eq_zero.mp hd').symm
  let e : kernel d ≅ F :=
    { hom := kernel.ι d ≫ π
      inv := kernel.lift d ι hi
      hom_inv_id := by
        apply (cancel_mono (kernel.ι d)).1
        simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
        exact hk
      inv_hom_id := by simp [← Category.assoc, h] }
  obtain ⟨hc, _, _, _, he⟩ := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
  exact he _ _ e (hc _ _ d hG hG).1

private theorem coherent_biproduct {X : Scheme.{u}} {J : Type*} [Finite J]
    (F : J → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : ∀ j, RingedSpace.IsCoherent X.toRingedSpace (F j)) :
    RingedSpace.IsCoherent X.toRingedSpace (⨁ F) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  let G : Fin n → SheafOfModules.{u} (moduleRings X.toRingedSpace) := fun j ↦ F (e.symm j)
  let c : (⨁ G) ≅ ⨁ F :=
    biproduct.whiskerEquiv e.symm (fun _ ↦ Iso.refl _)
  obtain ⟨_, _, hs, _, he⟩ := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
  exact he _ _ c (hs n G (fun j ↦ hF (e.symm j)))

private theorem coherent_free_tensor {X : Scheme.{u}}
    (G : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) (m : ℕ) :
    RingedSpace.IsCoherent X.toRingedSpace
      (SheafOfModules.free (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin m)) ⊗ G) := by
  let e :
      (SheafOfModules.free (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin m)) ⊗ G) ≅
        ⨁ (fun _ : ULift.{u} (Fin m) ↦ G) :=
    ((biproduct.isoCoproduct
      (fun _ : ULift.{u} (Fin m) ↦ SheafOfModules.unit (moduleRings X.toRingedSpace))).symm
        ⊗ᵢ Iso.refl G) ≪≫
      (tensorRight G).mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ λ_ G)
  obtain ⟨_, _, _, _, he⟩ := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
  exact he _ _ e.symm (coherent_biproduct _ (fun _ ↦ hG))

/-- The ordinary total tensor of a bounded finite-free-retract complex with a termwise
coherent complex has coherent terms, even if the second complex is unbounded.
Source: Stacks Project, perfect.tex, Tag 0DJQ, local tensor calculation;
coherent.tex, Tag 01Y0, label lemma-coherent-abelian-Noetherian.
(blueprint: lem-pc-finite-retract-tensor-complex-terms).

Proof: In total degree n the summands are P^p tensor N^q for p+q=n.
The bounds of P make a summand zero unless a<=p<=b.
For each such p the equation determines q=n-p, so there are finitely many pairs. Remove the
zero summands using the coproduct universal property. Every remaining summand
is a retract of (N^q)^{oplus m}, by tensoring the given retraction of P^p
from the rank-m free module and using distribution of tensor over finite sums.
Finite sums of coherent modules are coherent. A retract is coherent: it is the
kernel of 1 minus the idempotent given by the splitting, up to the canonical
isomorphism. Thus each total term is coherent. The argument includes zero ranks,
reversed bounds for P, empty schemes and the zero complex; it imposes no bounds on N.
It involves no homology, derived localization,
restriction functor or choice of local model. -/
theorem finiteRetract_tensorComplex_coherent_terms
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a b : ℤ)
    (hPbounds : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hPfree : ∀ n : ℤ, ∃ m : ℕ,
      ∃ (ι : P.X n ⟶ SheafOfModules.free
          (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin m)) ⟶ P.X n),
        ι ≫ π = 𝟙 (P.X n))
    (hNcoherent : ∀ n : ℤ, RingedSpace.IsCoherent X.toRingedSpace (N.X n)) :
    ∀ i : ℤ, RingedSpace.IsCoherent X.toRingedSpace
        ((CochainComplex.mapBifunctor P N (curriedTensor _)).X i) := by
  classical
  intro i
  let J := {pq : ℤ × ℤ // pq.1 + pq.2 = i ∧ pq.1 ∈ Finset.Icc a b}
  have : Finite J := Finite.of_injective
    (fun j : J ↦ (⟨j.1.1, j.2.2⟩ : ↥(Finset.Icc a b))) (by
      intro j k h
      apply Subtype.ext
      have hp : j.1.1 = k.1.1 := congrArg Subtype.val h
      apply Prod.ext hp
      have hj := j.2.1
      have hk := k.2.1
      omega)
  let F : J → SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
    fun j ↦ P.X j.1.1 ⊗ N.X j.1.2
  have hF : ∀ j, RingedSpace.IsCoherent X.toRingedSpace (F j) := by
    intro j
    obtain ⟨m, ι, π, h⟩ := hPfree j.1.1
    exact coherent_retract ((tensorRight (N.X j.1.2)).map ι)
      ((tensorRight (N.X j.1.2)).map π)
      (by
        rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]
        rfl)
      (coherent_free_tensor _ (hNcoherent j.1.2) m)
  let backMap : (⨁ F) ⟶ (CochainComplex.mapBifunctor P N (curriedTensor _)).X i :=
    biproduct.desc (fun j ↦ HomologicalComplex.ιMapBifunctor P N (curriedTensor _)
      (ComplexShape.up ℤ) j.1.1 j.1.2 i (by exact j.2.1))
  let forwardMap : (CochainComplex.mapBifunctor P N (curriedTensor _)).X i ⟶ (⨁ F) :=
    HomologicalComplex.mapBifunctorDesc
      (K₁ := P) (K₂ := N) (F := curriedTensor _) (c := ComplexShape.up ℤ)
      (fun p q h ↦ if hp : p ∈ Finset.Icc a b then
        biproduct.ι F ⟨(p, q), ⟨h, hp⟩⟩ else 0)
  apply coherent_retract forwardMap backMap ?_ (coherent_biproduct F hF)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  dsimp only [forwardMap, backMap]
  rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  by_cases hp : p ∈ Finset.Icc a b
  · simp only [dite_eq_left hp, biproduct.ι_desc, Category.comp_id]
  · rw [dite_eq_right hp, zero_comp]
    have hz : IsZero (P.X p ⊗ N.X q) :=
      Functor.map_isZero (tensorRight (N.X q)) (hPbounds p (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hp
        exact hp))
    exact hz.eq_of_src _ _

end AlgebraicGeometry.Scheme
