/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.SingleSupportedFiniteFreeHomQC
import WeilConjectures.AlgebraicGeometry.LocalizedComplexQCHomologyExtension
import WeilConjectures.Algebra.Homology.StupidTailHomShortExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentExtension
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Quasi-coherent cohomology of Hom from a finite free complex

Source: Stacks Project, Tags 0A6H (2) and 08I5, finite-column Hom calculation.
(blueprint: lem-sc-finite-free-hom-complex-qc-cohomology)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Hom from a bounded complex of finite free modules preserves quasi-coherent cohomology.

Source: Stacks Project, Tag 0A6H (2), using the finite-column calculation in Tag 08I5.

Proof: filter the finite source complex by its stupid truncations. The successive quotients
are single finite free modules placed in one degree. Applying internal Hom gives a finite
filtration, split in each degree, whose successive quotient complexes are shifts of finite
biproducts of the target complex. Finite free internal Hom is a finite biproduct, so its
cohomology is a finite biproduct of the target's cohomology and is quasi-coherent. Induct
along the finite filtration. For each short exact sequence of Hom complexes A → B → C,
the long exact sequence gives 0 → coker δ^(n-1) → H^n(B) → ker δ^n → 0, where
δ^(n-1) : H^(n-1)(C) → H^n(A) and δ^n : H^n(C) → H^(n+1)(A) are the connecting
maps. Kernels, cokernels, and extensions of quasi-coherent sheaves on a scheme are
quasi-coherent, so H^n(B) is quasi-coherent.
For the localized site of U, transport these facts through the exact equivalence with
module sheaves on U.toScheme. Transport back to obtain the stated property. Empty support
and rank zero give zero complexes and zero cohomology; no boundedness of the target is used.
(blueprint: lem-sc-finite-free-hom-complex-qc-cohomology). -/
theorem finiteFree_homComplex_qc_cohomology
    (X : Scheme.{u}) (U : X.Opens)
    (E I : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hEbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i))
    (hEfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (E.X i ≅ SheafOfModules.free
      (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r))))
    (hI : ∀ i : ℤ, (I.homology i).IsQuasicoherent) (n : ℤ) :
    ((homComplex (R := X.toRingedSpace.sheaf.over U) E I).homology n).IsQuasicoherent := by
  classical
  -- Reuse the sheafification instances throughout the truncation induction.
  let J := (Opens.grothendieckTopology X.toRingedSpace).over U
  have : HasSheafify J AddCommGrpCat.{u} := inferInstance
  have : J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  have : ∀ V, HasSheafify (J.over V) AddCommGrpCat.{u} := inferInstance
  have : ∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let A := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  have transport {K L : CochainComplex A ℤ} (e : K ≅ L)
      (hL : ∀ i : ℤ, (L.homology i).IsQuasicoherent) :
      ∀ i : ℤ, (K.homology i).IsQuasicoherent := by
    intro i
    exact (SheafOfModules.isQuasicoherent
      ((moduleRings X.toRingedSpace).over U)).prop_of_iso
      ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i).mapIso e).symm (hL i)
  have bounded (d : ℕ) : ∀ (a : ℤ) (K : CochainComplex A ℤ),
      (∀ i : ℤ, i < a ∨ a + d < i → IsZero (K.X i)) →
      (∀ i : ℤ, a ≤ i → i ≤ a + d → ∃ r : ℕ,
        Nonempty (K.X i ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r)))) →
      ∀ i : ℤ,
        ((homComplex (R := X.toRingedSpace.sheaf.over U) K I).homology i).IsQuasicoherent := by
    induction d with
    | zero =>
      intro a K hK hf i
      exact single_supported_finiteFree_hom_qc X U K I a
        (fun j hj ↦ hK j (by omega)) (hf a le_rfl (by simp)) hI i
    | succ d ih =>
      intro a K hK hf i
      let e := ComplexShape.embeddingUpIntGE (a + 1)
      let T := K.stupidTrunc e
      have hT (j : ℤ) (hj : j < a + 1 ∨ (a + 1) + d < j) : IsZero (T.X j) := by
        by_cases h : a + 1 ≤ j
        · obtain ⟨m, hm⟩ := Int.le.dest h
          have he : e.f m = j := by
            simp only [e, ComplexShape.embeddingUpIntGE_f]
            omega
          exact (hK j (by omega)).of_iso (K.stupidTruncXIso e he)
        · apply K.isZero_stupidTrunc_X e
          intro m
          simp only [e, ComplexShape.embeddingUpIntGE_f]
          omega
      have hfT (j : ℤ) (haj : a + 1 ≤ j) (hjd : j ≤ (a + 1) + d) :
          ∃ r : ℕ, Nonempty (T.X j ≅ SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r))) := by
        obtain ⟨m, hm⟩ := Int.le.dest haj
        have he : e.f m = j := by
          simp only [e, ComplexShape.embeddingUpIntGE_f]
          omega
        obtain ⟨r, ⟨hr⟩⟩ := hf j (by omega) (by omega)
        exact ⟨r, ⟨K.stupidTruncXIso e he ≪≫ hr⟩⟩
      have htail := ih (a + 1) T hT hfT
      obtain ⟨S, S', φ, hS, _, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
        exists_homComplex_stupid_tail_shortExact _
          (X.toRingedSpace.sheaf.over U) K a
          (fun j hj ↦ hK j (Or.inl hj)) (𝟙 I)
      have hsingle : ∀ j : ℤ,
          ((homComplex (R := X.toRingedSpace.sheaf.over U)
            ((HomologicalComplex.single A (ComplexShape.up ℤ) a).obj (K.X a)) I).homology j
          ).IsQuasicoherent := by
        intro j
        apply single_supported_finiteFree_hom_qc X U _ I a
        · intro l hl
          exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hl
        · simpa using hf a le_rfl (by omega)
        · exact hI
      have h₁ := transport (Arrow.leftFunc.mapIso e₁) hsingle
      have h₃ := transport (Arrow.leftFunc.mapIso e₃) htail
      have h₂ := localized_complex_qc_homology_extension X U S hS h₁ h₃
      exact transport (Arrow.leftFunc.mapIso e₂).symm h₂ i
  obtain ⟨a, b, hab⟩ := hEbounded
  exact bounded (b - a).toNat a E
    (fun i hi ↦ hab i (by omega)) (fun i _ _ ↦ hEfree i) n

end AlgebraicGeometry
