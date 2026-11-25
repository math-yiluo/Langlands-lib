/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # Bounded finite representatives of pseudo-coherent complexes

Source: Stacks Project, More on Algebra, Tag 066E.
(blueprint: lem-weil-pbc-bounded-finite-pseudocoherent-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A cohomologically bounded pseudo-coherent object over a Noetherian ring has
finite terms in precisely the prescribed interval.
Source: Stacks, More on Algebra, Tag 066E, and truncation of complexes.
(blueprint: lem-weil-pbc-bounded-finite-pseudocoherent-model).

Proof: take a bounded-above finite-free representative from pseudo-coherence.
Truncate above b, replacing degree b by its cycles, a finite submodule over the
Noetherian ring. The upper cohomology bound makes this a quasi-isomorphism.
Truncate below a, replacing degree a by the cokernel of the incoming differential,
which is finite. The lower bound makes the second truncation a quasi-isomorphism.
Compose the two localization isomorphisms. Both strict term bounds hold even when
a>b, since then the derived object is zero. -/
theorem exists_boundedFinite_model {R : Type u} [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{v} (ModuleCat.{u} R)]
    (C : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) (hC : DerivedCategory.IsPseudoCoherent C)
    (hvan : ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj C)) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Finite R (P.X i)) ∧ Nonempty (DerivedCategory.Q.obj P ≅ C) := by
  obtain ⟨E, c, hc, hfiniteE, ⟨eE⟩⟩ := hC
  have : (DerivedCategory.Q.obj E).IsLE b := (DerivedCategory.isLE_iff _ _).2
    fun i hi ↦ (hvan i (Or.inr hi)).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso eE)
  have : E.IsLE b := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    infer_instance
  let P := E.truncLE b
  let e : DerivedCategory.Q.obj P ≅ C :=
    asIso (DerivedCategory.Q.map (E.ιTruncLE b)) ≪≫ eE
  have hfinite (i : ℤ) : Module.Finite R (P.X i) := by
    obtain hi | rfl | hi := lt_trichotomy i b
    · have : Module.Finite R (E.X i) := (hfiniteE i).2
      exact Module.Finite.equiv (E.truncLEXIso b i hi).toLinearEquiv.symm
    · have : Module.Finite R (E.X i) := (hfiniteE i).2
      have : Module.Finite R (E.cycles i) :=
        Module.Finite.of_injective (E.iCycles i).hom
          ((ModuleCat.mono_iff_injective _).1 inferInstance)
      exact Module.Finite.equiv (E.truncLEXIsoCycles i).toLinearEquiv.symm
    · have : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.1
        (CochainComplex.isZero_of_isStrictlyLE P b i hi)
      infer_instance
  have : (DerivedCategory.Q.obj P).IsGE a := (DerivedCategory.isGE_iff _ _).2 fun i hi ↦
    (hvan i (Or.inl hi)).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e)
  have : P.IsGE a := by
    rw [← DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  let L := P.truncGE a
  refine ⟨L, ?_, ?_, ⟨(asIso (DerivedCategory.Q.map (P.πTruncGE a))).symm ≪≫ e⟩⟩
  · intro i hi
    rcases hi with hi | hi
    · exact L.isZero_of_isStrictlyGE a i hi
    · exact L.isZero_of_isStrictlyLE b i hi
  · intro i
    obtain hi | rfl | hi := lt_trichotomy i a
    · have : Subsingleton ((P.truncGE a).X i) :=
        ModuleCat.isZero_iff_subsingleton.1
          (CochainComplex.isZero_of_isStrictlyGE _ a i hi)
      infer_instance
    · have : Module.Finite R (P.X i) := hfinite i
      have : Module.Finite R (P.opcycles i) :=
        Module.Finite.of_surjective (P.pOpcycles i).hom
          ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      exact Module.Finite.equiv (P.truncGEXIsoOpcycles i).toLinearEquiv.symm
    · have : Module.Finite R (P.X i) := hfinite i
      exact Module.Finite.equiv (P.truncGEXIso a i hi).toLinearEquiv.symm

end AlgebraicGeometry.Scheme
