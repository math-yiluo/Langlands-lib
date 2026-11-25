/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.Algebra.Homology.TowerSplitComplexReplacement
import WeilConjectures.Algebra.Homology.RoosSplitComparison
import WeilConjectures.Algebra.Homology.RoosComparisonHomotopyRetract
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Roos complexes for inverse limits

Source: Stacks Project, derived.tex, Tag 070M (lemma-difficulty-K-injectives),
extended to arbitrary K-injective towers by the node's split-envelope argument
(blueprint: lem-weil-derived-limit-roos-complex).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem homotopy_retraction_of_quasiIso
    {B : Type u} [Category.{v} B] [Abelian B]
    {I J : CochainComplex B ℤ} [I.IsKInjective]
    (u : I ⟶ J) [QuasiIso u] : ∃ r : J ⟶ I, Nonempty (Homotopy (u ≫ r) (𝟙 I)) := by
  let _ := HasDerivedCategory.standard B
  let H := HomotopyCategory.quotient B (ComplexShape.up ℤ)
  have hq : (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) (H.map u) := by
    change (HomotopyCategory.quasiIso B _)
      ((HomotopyCategory.quotient B _).map u)
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have hiso : IsIso (DerivedCategory.Qh.map (H.map u)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B _) _ hq
  obtain ⟨r, hr⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (H.obj J) I).surjective
    (inv (DerivedCategory.Qh.map (H.map u)))
  obtain ⟨r, rfl⟩ := H.map_surjective r
  refine ⟨r, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (H.obj I) I).injective
  change DerivedCategory.Qh.map (H.map (u ≫ r)) = DerivedCategory.Qh.map (H.map (𝟙 I))
  rw [H.map_comp, H.map_id, DerivedCategory.Qh.map_comp, DerivedCategory.Qh.map_id, hr]
  exact IsIso.hom_inv_id _

/-- The canonical Roos comparison is a quasi-isomorphism. The isomorphisms `eP` and `eC`
identify the product and shifted cone terms; their differential equations specify the
complexes, and the kernel and comparison equations specify the canonical map.
Source: Stacks Project, derived.tex, Tag 070M (lemma-difficulty-K-injectives)
(blueprint: lem-weil-derived-limit-roos-complex).

Proof: (1) The kernel of the transition endomorphism is the inverse limit, naturally in
families (tower-transition-endomorphism and inverse-system definitions). (2) Applying
products and limits termwise preserves homotopies; on the cone use the homotopy
`(-P(h)y, P(h)x)`. (3) On split towers recursively choose a section of `1-s`
(lem-weil-tower-split-envelope), so it is split epi. (4) For complexes with split terms,
the degreewise-epi kernel/cone comparison is a quasi-isomorphism
(lem-weil-degreewise-epi-kernel-cocone-qis). (5) Embed the tower complex in its additive
split envelope and use the cokernel's shifted cone to replace it by a quasi-isomorphic
complex with split terms (lem-weil-tower-category-levelwise-abelian and
lem-weil-tower-split-envelope). (6) K-injectivity gives a homotopy retraction of this
replacement (lem-weil-pbc-kinjective-hom-derived). (7) Naturality and homotopy invariance
make the comparison a retract of the split-term comparison on every cohomology object;
thus it is a quasi-isomorphism and its derived-category image is an isomorphism. -/
theorem roosComplex_quasiIso
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasLimitsOfShape (Discrete ℕ) A] [HasExactLimitsOfShape (Discrete ℕ) A]
    [EnoughInjectives A] [HasDerivedCategory.{w} A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
    (P L C : CochainComplex A ℤ)
    (eP : ∀ p : ℤ, P.X p ≅ ∏ᶜ (fun n : ℕ ↦ (I.X p).obj (Opposite.op n)))
    (hP : ∀ p q : ℤ, P.d p q ≫ (eP q).hom =
      (eP p).hom ≫ Limits.Pi.map (fun n ↦ (I.d p q).app (Opposite.op n)))
    (oneSubS : P ⟶ P)
    (hS : ∀ p : ℤ, oneSubS.f p = (eP p).hom ≫
      towerTransitionEndomorphism
        (fun n ↦ (I.X p).map (homOfLE (Nat.le_succ n)).op) ≫ (eP p).inv)
    (iota : L ⟶ P)
    (hKernel : ∀ p : ℤ, iota.f p ≫ oneSubS.f p = 0)
    (hL : ∀ p : ℤ, IsLimit (KernelFork.ofι (iota.f p) (hKernel p)))
    (eC : ∀ p : ℤ, C.X (p + 1) ≅ P.X p ⊞ P.X (p + 1))
    (hC : ∀ p : ℤ, C.d (p + 1) (p + 1 + 1) ≫ (eC (p + 1)).hom =
      (eC p).hom ≫ biprod.lift
        (-(biprod.fst ≫ P.d p (p + 1)) - biprod.snd ≫ oneSubS.f (p + 1))
        (biprod.snd ≫ P.d (p + 1) (p + 1 + 1)))
    : ∃ eta : L ⟶ C,
      (∀ p : ℤ, eta.f (p + 1) ≫ (eC p).hom = biprod.lift 0 (iota.f (p + 1))) ∧
      QuasiIso eta ∧ IsIso ((DerivedCategory.Q).map eta) := by
  let f : ∀ p : ℤ, L.X p ⟶ C.X p :=
    Equiv.piCongrLeft (fun p ↦ L.X p ⟶ C.X p) (Equiv.addRight (1 : ℤ))
      (fun p ↦ biprod.lift 0 (iota.f (p + 1)) ≫ (eC p).inv)
  have hf (p : ℤ) : f (p + 1) = biprod.lift 0 (iota.f (p + 1)) ≫ (eC p).inv := by
    exact Equiv.piCongrLeft_apply_apply _ _ _ p
  let eta : L ⟶ C :=
    { f := f
      comm' := by
        intro p q hpq
        have hpq' : p + 1 = q := hpq
        subst q
        obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective p
        change f (p + 1) ≫ C.d (p + 1) (p + 1 + 1) =
          L.d (p + 1) (p + 1 + 1) ≫ f (p + 1 + 1)
        rw [hf, hf]
        apply (cancel_mono (eC (p + 1)).hom).1
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [hC]
        simp only [Iso.inv_hom_id_assoc]
        apply biprod.hom_ext <;>
          simp [Category.assoc, Preadditive.comp_sub, Preadditive.comp_neg, hKernel, iota.comm] }
  have heq : ∀ p : ℤ, eta.f (p + 1) ≫ (eC p).hom =
      biprod.lift 0 (iota.f (p + 1)) := by
    intro p
    change f (p + 1) ≫ (eC p).hom = _
    rw [hf]
    simp
  obtain ⟨J, u, hu, hSplit⟩ := tower_split_complex_replacement A I
  have : QuasiIso u := hu
  obtain ⟨r, ⟨hr⟩⟩ := homotopy_retraction_of_quasiIso u
  obtain ⟨PJ, LJ, CJ, ePJ, sJ, iJ, hKJ, eCJ, etaJ, hLJ,
    hPJ, hSJ, hCJ, hEtaJ, hqJ⟩ := roos_split_comparison A J hSplit
  obtain ⟨lU, cU, lR, cR, hU, hR, ⟨hLid⟩, ⟨hCid⟩⟩ :=
    roos_comparison_homotopy_retract A I J u r hr
      P L C eP hP oneSubS hS iota hKernel hL eC hC eta heq
      PJ LJ CJ ePJ hPJ sJ hSJ iJ hKJ hLJ eCJ hCJ etaJ hEtaJ
  have : QuasiIso etaJ := hqJ
  let Q := DerivedCategory.Q (C := A)
  have hU' : Q.map lU ≫ Q.map etaJ = Q.map eta ≫ Q.map cU := by
    simpa only [Functor.map_comp] using congrArg Q.map hU
  have hR' : Q.map lR ≫ Q.map eta = Q.map etaJ ≫ Q.map cR := by
    simpa only [Functor.map_comp] using congrArg Q.map hR
  have hLid' : Q.map lU ≫ Q.map lR = 𝟙 (Q.obj L) := by
    rw [← Q.map_comp]
    exact (DerivedCategory.Q_map_eq_of_homotopy A hLid).trans (Q.map_id L)
  have hCid' : Q.map cU ≫ Q.map cR = 𝟙 (Q.obj C) := by
    rw [← Q.map_comp]
    exact (DerivedCategory.Q_map_eq_of_homotopy A hCid).trans (Q.map_id C)
  let v := Q.map cU ≫ inv (Q.map etaJ) ≫ Q.map lR
  have hiso : IsIso (Q.map eta) := by
    refine ⟨⟨v, ?_, ?_⟩⟩
    · dsimp [v]
      rw [← Category.assoc, ← hU', Category.assoc]
      simp only [IsIso.hom_inv_id_assoc]
      exact hLid'
    · dsimp [v]
      simp only [Category.assoc]
      rw [hR']
      simp only [IsIso.inv_hom_id_assoc]
      exact hCid'
  exact ⟨eta, heq, (DerivedCategory.isIso_Q_map_iff_quasiIso A eta).1 hiso, hiso⟩

end CategoryTheory
