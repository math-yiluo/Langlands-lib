/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

import WeilConjectures.Algebra.Homology.ResidueBottomDifferential
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Projectivity of zeroth opcycles from connective residue homology

Source: Stacks Project, Tag 00O0, negative-tail splitting argument.
(blueprint: lem-sc-residue-connective-projective-opcycles).
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The last cokernel in a bounded finite projective negative tail is finite projective
if every residue complex is exact in negative degrees.

Source: Stacks Project, Tag 00O0; the negative-tail cancellation argument in
lem-sc-universal-h0-projective-normalization.
(blueprint: lem-sc-residue-connective-projective-opcycles).

Proof: Choose a lower support bound a and induct on max(0,-a). If a is nonnegative,
P^(-1) is zero, so opcycles in degree zero is P^0 and is finite projective.
Otherwise the incoming term at a is zero. Negative residue homology vanishing
makes d:P^a -> P^(a+1) residue-injective at every prime. Tag 00O0 makes this
map injective with projective cokernel locally. Its cokernel is finitely presented
as the cokernel of a map between finitely presented modules. The local-to-global
criterion Module.projective_of_localization_maximal therefore makes it projective
globally; it is finite as a quotient of P^(a+1). Split the map, remove P^a and
its image, and replace P^(a+1) by its cokernel. The resulting complex has a higher
lower bound and finite projective terms. The removed pair is contractible, so
scalar extension preserves its homotopy equivalence and the residue vanishing.
If a < -1, the degree-zero term and the image of its incoming differential are
unchanged, hence so are zeroth opcycles. If a = -1, the new degree-zero term
is exactly the original zeroth opcycles. Apply induction, transferring along
these identifications. This is a statement about the canonical quotient P.opcycles 0,
not a choice of a new complex. Empty support intervals and the zero ring are allowed. -/
theorem residueConnective_projective_opcycles
    (R : Type v) [CommRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hf : ∀ n : ℤ, Module.Finite R (P.X n))
    (hp : ∀ n : ℤ, Module.Projective R (P.X n))
    (hnegative : ∀ (p : Ideal R) [p.IsPrime],
      let Pp := ((ModuleCat.extendScalars (algebraMap R p.ResidueField)).mapHomologicalComplex
        (.up ℤ)).obj P
      ∀ i : ℤ, i < 0 → IsZero (Pp.homology i)) :
    Module.Finite R (P.opcycles 0) ∧ Module.Projective R (P.opcycles 0) := by
  classical
  have hfinite (K : CochainComplex (ModuleCat.{v} R) ℤ)
      (hK : Module.Finite R (K.X 0)) : Module.Finite R (K.opcycles 0) := by
    have := hK
    exact Module.Finite.of_surjective (K.pOpcycles 0).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  obtain ⟨a, b, hbound⟩ := hb
  have aux (k : ℕ) : ∀ K : CochainComplex (ModuleCat.{v} R) ℤ,
      (∀ n : ℤ, n < -(k : ℤ) → IsZero (K.X n)) →
      (∀ n : ℤ, b < n → IsZero (K.X n)) →
      (∀ n : ℤ, Module.Finite R (K.X n)) →
      (∀ n : ℤ, Module.Projective R (K.X n)) →
      (∀ (p : Ideal R) [p.IsPrime],
        let Kp := ((ModuleCat.extendScalars (algebraMap R p.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj K
        ∀ i : ℤ, i < 0 → IsZero (Kp.homology i)) →
      Module.Projective R (K.opcycles 0) := by
    induction k with
    | zero =>
      intro K hl hu hf hp hn
      let e := (K.pOpcyclesIso (-1) 0 (by simp)
        ((hl (-1) (by norm_num)).eq_of_src _ _)).toLinearEquiv
      have := hp 0
      exact Module.Projective.of_equiv' e
    | succ k ih =>
      intro K hl hu hf hp hn
      let c : ℤ := -(k : ℤ)
      obtain ⟨hm, hc⟩ := residue_bottom_differential R K (c - 1)
        (hl (c - 1 - 1) (by dsimp [c]; omega))
        (hf _) (hf _) (hp _) (hp _)
        (fun p _ ↦ hn p (c - 1) (by dsimp [c]; omega))
      have heq : c - 1 + 1 = c := by omega
      rw [heq] at hm hc
      have hm' : Mono (K.d (c - 1) c) := hm
      have hc' : Module.Projective R (K.opcycles c) := hc
      by_cases hk : k = 0
      · subst k
        exact hc'
      let Q := K.truncGE c
      have hlow (n : ℤ) (hn : n < c) : IsZero (Q.X n) :=
        Q.isZero_of_isStrictlyGE c n hn
      have hterms (n : ℤ) : Module.Finite R (Q.X n) ∧ Module.Projective R (Q.X n) := by
        rcases lt_trichotomy n c with hn | rfl | hn
        · have := ModuleCat.subsingleton_of_isZero (hlow n hn)
          exact ⟨inferInstance, inferInstance⟩
        · let e := (K.truncGEXIsoOpcycles c).toLinearEquiv
          have := hc'
          have : Module.Finite R (K.opcycles c) := by
            have := hf c
            exact Module.Finite.of_surjective (K.pOpcycles c).hom
              ((ModuleCat.epi_iff_surjective _).mp inferInstance)
          exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩
        · let e := (K.truncGEXIso c n hn).toLinearEquiv
          have := hf n
          have := hp n
          exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩
      have hupper (n : ℤ) (hn : max b c < n) : IsZero (Q.X n) :=
        (hu n (by omega)).of_iso (K.truncGEXIso c n (by omega))
      have : K.IsStrictlyLE b := (K.isStrictlyLE_iff b).mpr hu
      have : Q.IsStrictlyLE (max b c) := (Q.isStrictlyLE_iff _).mpr hupper
      have (n : ℤ) : CategoryTheory.Projective (K.X n) := by
        have := hp n
        infer_instance
      have (n : ℤ) : CategoryTheory.Projective (Q.X n) := by
        have := (hterms n).2
        infer_instance
      have : K.IsKProjective := isKProjective_of_projective K b
      have : Q.IsKProjective := isKProjective_of_projective Q (max b c)
      have : K.IsGE c := (K.isGE_iff c).mpr (fun n hn ↦ by
        by_cases he : n = c - 1
        · subst n
          rw [K.exactAt_iff' (j := c - 1) (i := c - 2) (k := c)
            (by simp; omega) (by simp)]
          have : Mono (K.sc' (c - 2) (c - 1) c).g := hm'
          exact (ShortComplex.exact_iff_mono _
            ((hl (c - 2) (by dsimp [c]; omega)).eq_of_src _ _)).mpr inferInstance
        · exact HomologicalComplex.ExactAt.of_isZero (hl n (by dsimp [c] at *; omega)))
      obtain ⟨e, _⟩ := (IsKProjective.quasiIso_iff (K.πTruncGE c)).mp inferInstance
      have hres (p : Ideal R) [p.IsPrime] (i : ℤ) (hi : i < 0) :
          IsZero ((((ModuleCat.extendScalars (algebraMap R p.ResidueField)).mapHomologicalComplex
            (.up ℤ)).obj Q).homology i) := by
        have : (ModuleCat.extendScalars (algebraMap R p.ResidueField)).Additive :=
          (ModuleCat.extendRestrictScalarsAdj (algebraMap R p.ResidueField)).left_adjoint_additive
        let ep := (ModuleCat.extendScalars (algebraMap R p.ResidueField)).mapHomotopyEquiv e
        exact (hn p i hi).of_iso (ep.toHomologyIso i).symm
      have hqUpper (n : ℤ) (hn : b < n) : IsZero (Q.X n) := by
        by_cases hnc : n < c
        · exact hlow n hnc
        by_cases he : n = c
        · subst n
          have hz := hu c hn
          have hzq : IsZero (K.opcycles c) := IsZero.of_epi (K.pOpcycles c) hz
          exact hzq.of_iso (K.truncGEXIsoOpcycles c)
        · exact (hu n hn).of_iso (K.truncGEXIso c n (by omega))
      have hq := ih Q hlow hqUpper (fun n ↦ (hterms n).1) (fun n ↦ (hterms n).2) hres
      have hi0 : IsIso ((K.πTruncGE c).f 0) := by
        change IsIso ((HomologicalComplex.πTruncGE K (ComplexShape.embeddingUpIntGE c)).f 0)
        dsimp only [HomologicalComplex.πTruncGE]
        rw [(ComplexShape.embeddingUpIntGE c).isIso_liftExtend_f_iff _ _
          (show (ComplexShape.embeddingUpIntGE c).f ((-c).toNat) = 0 by
            simp [ComplexShape.embeddingUpIntGE,
              Int.toNat_of_nonneg (show 0 ≤ -c by dsimp [c]; omega)])]
        apply HomologicalComplex.isIso_restrictionToTruncGE'
        rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
        dsimp [c]
        omega
      have : IsIso (HomologicalComplex.opcyclesMap (K.πTruncGE c) 0) :=
        ShortComplex.isIso_opcyclesMap_of_isIso_of_epi'
          ((HomologicalComplex.shortComplexFunctor _ _ 0).map (K.πTruncGE c)) hi0
          (by change Epi ((K.πTruncGE c).f ((ComplexShape.up ℤ).prev 0))
              dsimp [πTruncGE]; infer_instance)
      have := hq
      exact Module.Projective.of_equiv'
        (asIso (HomologicalComplex.opcyclesMap (K.πTruncGE c) 0)).toLinearEquiv.symm
  exact ⟨hfinite P (hf 0), aux (-a).toNat P
    (fun n hn ↦ hbound n (Or.inl (by omega)))
    (fun n hn ↦ hbound n (Or.inr hn)) hf hp hnegative⟩

end CochainComplex
