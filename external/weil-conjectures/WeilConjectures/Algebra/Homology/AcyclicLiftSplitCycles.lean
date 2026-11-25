/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Split cycles in a finite projective tail

Source: Stacks Project, Tag 0BC9, proof, first paragraph.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The leftmost cycle module of a finite projective exact tail belongs to the term class,
and its kernel sequence stays exact and monic after reduction.

Source: Stacks Project, Tag 0BC9, proof, first paragraph
(blueprint: lem-sc-acyclic-lift-split-cycles).

Proof. Obtain a zero member of P by applying the summand condition to any term
and its decomposition as itself plus zero. The same condition, using this zero
member, gives invariance under module isomorphisms. Above the upper bound the
cycle module is zero. Descend through the finite interval to n. Exactness at i+1
makes the differential onto the cycle module in degree i+1 surjective.
That cycle module is projective by the induction hypothesis, so split this
surjection. The degree-i term becomes the product of the next cycle module and
its own cycle module. Since the term and the next cycle module belong to P, the
summand condition puts the degree-i cycle module in P, hence makes it projective.
Take Z to be the cycle module in degree n, with its kernel inclusion. The
splittings in degrees n and n+1 identify the outgoing differential with the
projection onto the next cycle module followed by its split inclusion.
Consequently the sequence Z -> C^n -> C^(n+1) is exact and its first arrow is
monic. Extension of scalars preserves those splitting equations and the product
isomorphisms, giving the same assertions after reduction. If n exceeds b, all
these modules are zero and the same reasoning applies with an empty interval. -/
theorem exists_acyclicLift_splitCycles
    (R : Type u) [CommRing R] (I : Ideal R)
    (P : ModuleCat.{max u v} R → Prop)
    (hprojective : ∀ M, P M → Projective M)
    (hsummand : ∀ M₁ M₂ M₁₂ : ModuleCat.{max u v} R,
      P M₁ → P M₁₂ → Nonempty (M₁₂ ≅ ModuleCat.of R (M₁ × M₂)) → P M₂)
    (C : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (b n : ℤ) (hupper : C.IsStrictlyLE b)
    (hP : ∀ i, P (C.X i)) (hexact : ∀ i, n < i → C.ExactAt i) :
    ∃ Z : ModuleCat.{max u v} R, P Z ∧
      ∃ ι : Z ⟶ C.X n, ∃ hz : ι ≫ C.d n (n + 1) = 0,
        ∃ hzF : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map ι ≫
          (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map (C.d n (n + 1)) = 0,
          Mono ι ∧ (ShortComplex.mk ι (C.d n (n + 1)) hz).Exact ∧
          Mono ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map ι) ∧
          (ShortComplex.mk
            ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map ι)
            ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map (C.d n (n + 1)))
            hzF).Exact  := by
  classical
  let O : ModuleCat.{max u v} R := ModuleCat.of R PUnit.{max u v + 1}
  have hO : P O := hsummand (C.X n) O (C.X n) (hP n) (hP n)
    ⟨(LinearEquiv.prodUnique (R := R) (M := C.X n) (M₂ := O)).symm.toModuleIso⟩
  have hIso (M N : ModuleCat.{max u v} R) (hM : P M) (e : M ≅ N) : P N :=
    hsummand O N M hO hM
      ⟨e ≪≫ (LinearEquiv.prodUnique (R := R) (M := N) (M₂ := O)).symm.toModuleIso ≪≫
        (LinearEquiv.prodComm R N O).toModuleIso⟩
  let S (i : ℤ) : ShortComplex (ModuleCat.{max u v} R) :=
    ShortComplex.mk (C.iCycles i) (C.toCycles i (i + 1)) (by
      rw [← cancel_mono (C.iCycles (i + 1)), Category.assoc]
      simp)
  have hSexact (i : ℤ) : (S i).Exact := by
    let T : ShortComplex (ModuleCat.{max u v} R) :=
      ShortComplex.mk (C.iCycles i) (C.d i (i + 1)) (C.iCycles_d i (i + 1))
    have hT : T.Exact := T.exact_of_f_is_kernel (C.cyclesIsKernel i (i + 1) (by simp))
    let f : S i ⟶ T :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := C.iCycles (i + 1)
        comm₁₂ := by simp [S, T]
        comm₂₃ := by simp [S, T] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mpr hT
  have hEpi (i : ℤ) (hi : n ≤ i) : Epi (S i).g := by
    have hs : (C.sc' i (i + 1) (i + 2)).Exact :=
      (C.exactAt_iff' i (i + 1) (i + 2) (by simp) (by simp; omega)).mp
        (hexact (i + 1) (by omega))
    have : Epi (C.sc' i (i + 1) (i + 2)).toCycles := hs.epi_toCycles
    let E := C.cyclesIsoSc' i (i + 1) (i + 2) (by simp) (by simp; omega)
    have he : Epi (C.toCycles i (i + 1) ≫ E.hom) := by
      rw [C.toCycles_cyclesIsoSc'_hom i (i + 1) (i + 2) (by simp) (by simp; omega)]
      infer_instance
    have : Epi ((C.toCycles i (i + 1) ≫ E.hom) ≫ E.inv) := inferInstance
    simpa only [Category.assoc, E.hom_inv_id, Category.comp_id] using this
  have hSplit (i : ℤ) (hi : n ≤ i) (hnext : P (C.cycles (i + 1))) :
      Nonempty ((S i).Splitting) := by
    have : Projective (C.cycles (i + 1)) := hprojective _ hnext
    have hSE : (S i).ShortExact :=
      { exact := hSexact i
        mono_f := inferInstance
        epi_g := hEpi i hi }
    exact ⟨hSE.splittingOfProjective⟩
  have hCycle (k : ℕ) (i : ℤ) (hi : n ≤ i)
      (hb : ∀ j : ℤ, i + k < j → IsZero (C.X j)) : P (C.cycles i) := by
    induction k generalizing i with
    | zero =>
      have hd : C.d i (i + 1) = 0 := (hb (i + 1) (by omega)).eq_of_tgt _ _
      exact hIso (C.X i) (C.cycles i) (hP i)
        (C.iCyclesIso i (i + 1) (by simp) hd).symm
    | succ k ih =>
      have hnext : P (C.cycles (i + 1)) := ih (i + 1) (by omega)
        (fun j hj ↦ hb j (by omega))
      obtain ⟨sp⟩ := hSplit i hi hnext
      exact hsummand (C.cycles (i + 1)) (C.cycles i) (C.X i) hnext (hP i)
        ⟨sp.isoBinaryBiproduct ≪≫ biprod.braiding _ _ ≪≫ ModuleCat.biprodIsoProd _ _⟩
  have hCycleP (i : ℤ) (hi : n ≤ i) : P (C.cycles i) := by
    apply hCycle (b - i).toNat i hi
    intro j hj
    exact (C.isStrictlyLE_iff b).mp hupper j (by omega)
  obtain ⟨sp⟩ := hSplit n le_rfl (hCycleP (n + 1) (by omega))
  obtain ⟨spnext⟩ := hSplit (n + 1) (by omega) (hCycleP (n + 1 + 1) (by omega))
  let F := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  have : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
  have hFzero : F.map (C.iCycles n) ≫ F.map (C.d n (n + 1)) = 0 := by
    rw [← F.map_comp, C.iCycles_d, F.map_zero]
  let T : ShortComplex (ModuleCat.{max u v} (R ⧸ I)) :=
    ShortComplex.mk (F.map (C.iCycles n)) (F.map (C.d n (n + 1))) hFzero
  have hTF : T.Exact := by
    have : Mono (F.map (C.iCycles (n + 1))) := (spnext.map F).mono_f
    let f : (S n).map F ⟶ T :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := F.map (C.iCycles (n + 1))
        comm₁₂ := by simp [S, T]
        comm₂₃ := by simp [S, T, ← F.map_comp] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mp (sp.map F).exact
  exact ⟨C.cycles n, hCycleP n le_rfl, C.iCycles n, C.iCycles_d n (n + 1),
    hFzero, inferInstance,
    (ShortComplex.mk _ _ (C.iCycles_d n (n + 1))).exact_of_f_is_kernel
      (C.cyclesIsKernel n (n + 1) (by simp)), (sp.map F).mono_f, hTF⟩

end CochainComplex
