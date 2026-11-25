/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.Algebra.Homology.RoosComparisonMaps
import WeilConjectures.Algebra.Homology.RoosComparisonHomotopies

/-! # Homotopy retract diagrams for Roos comparisons

Source: Stacks Project, Derived Categories, Tag 070M, and the split-envelope
extension recorded in lem-weil-derived-limit-roos-complex.
(blueprint: lem-weil-roos-comparison-homotopy-retract).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Roos comparisons carry a homotopy retraction of towers to a homotopy retraction
of arrows. This is a naturality and homotopy-invariance statement; it assumes no
K-injectivity, split transitions or quasi-isomorphism of either comparison.

Proof: For a chain map u, define the product map degreewise by eP, the component
maps of u, and ePJ. Naturality of u implies that it commutes with the transition
endomorphisms. The kernel universal property then defines lU, and the direct sum
of the product maps in successive degrees defines cU under eC and eCJ. Checking
both projections proves the chain-map equations and the comparison square.
Perform the same construction for r to obtain lR and cR and the reverse square.
Products and kernels are additive functors applied termwise. Applying them to a
homotopy u r ~ id gives a homotopy lU lR ~ id. On the signed cone the homotopy
is H(y,x)=(-P(h)y,P(h)x). The mixed terms cancel by naturality of the transition
endomorphism: -s P(h)x + P(h)s x = 0. Thus cU cR ~ id as well. The specified
comparison equations ensure that the two squares use exactly eta and etaJ.

Source: Stacks Project, Derived Categories, Tag 070M; the explicit extension
in lem-weil-derived-limit-roos-complex.
(blueprint: lem-weil-roos-comparison-homotopy-retract). -/
theorem roos_comparison_homotopy_retract
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasLimitsOfShape (Discrete ℕ) A]
    (I J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (u : I ⟶ J) (r : J ⟶ I) (hr : Homotopy (u ≫ r) (𝟙 I))
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
    (eta : L ⟶ C)
    (hEta : ∀ p : ℤ, eta.f (p + 1) ≫ (eC p).hom =
      biprod.lift 0 (iota.f (p + 1)))
    (PJ LJ CJ : CochainComplex A ℤ)
    (ePJ : ∀ p : ℤ, PJ.X p ≅ ∏ᶜ (fun n : ℕ ↦ (J.X p).obj (Opposite.op n)))
    (hPJ : ∀ p q : ℤ, PJ.d p q ≫ (ePJ q).hom =
      (ePJ p).hom ≫ Limits.Pi.map (fun n ↦ (J.d p q).app (Opposite.op n)))
    (sJ : PJ ⟶ PJ)
    (hSJ : ∀ p : ℤ, sJ.f p = (ePJ p).hom ≫
      towerTransitionEndomorphism
        (fun n ↦ (J.X p).map (homOfLE (Nat.le_succ n)).op) ≫ (ePJ p).inv)
    (iJ : LJ ⟶ PJ)
    (hKJ : ∀ p : ℤ, iJ.f p ≫ sJ.f p = 0)
    (hLJ : ∀ p : ℤ, IsLimit (KernelFork.ofι (iJ.f p) (hKJ p)))
    (eCJ : ∀ p : ℤ, CJ.X (p + 1) ≅ PJ.X p ⊞ PJ.X (p + 1))
    (hCJ : ∀ p : ℤ, CJ.d (p + 1) (p + 1 + 1) ≫ (eCJ (p + 1)).hom =
      (eCJ p).hom ≫ biprod.lift
        (-(biprod.fst ≫ PJ.d p (p + 1)) - biprod.snd ≫ sJ.f (p + 1))
        (biprod.snd ≫ PJ.d (p + 1) (p + 1 + 1)))
    (etaJ : LJ ⟶ CJ)
    (hEtaJ : ∀ p : ℤ, etaJ.f (p + 1) ≫ (eCJ p).hom =
      biprod.lift 0 (iJ.f (p + 1)))
    : ∃ (lU : L ⟶ LJ) (cU : C ⟶ CJ) (lR : LJ ⟶ L) (cR : CJ ⟶ C),
      lU ≫ etaJ = eta ≫ cU ∧ lR ≫ eta = etaJ ≫ cR ∧
      Nonempty (Homotopy (lU ≫ lR) (𝟙 L)) ∧
      Nonempty (Homotopy (cU ≫ cR) (𝟙 C)) := by
  obtain ⟨lU, cU, hU, hlU, hcU⟩ := roos_comparison_maps A I J u
    P L C eP hP oneSubS hS iota hKernel hL eC hC eta hEta
    PJ LJ CJ ePJ hPJ sJ hSJ iJ hKJ hLJ eCJ hCJ etaJ hEtaJ
  obtain ⟨lR, cR, hR, hlR, hcR⟩ := roos_comparison_maps A J I r
    PJ LJ CJ ePJ hPJ sJ hSJ iJ hKJ hLJ eCJ hCJ etaJ hEtaJ
    P L C eP hP oneSubS hS iota hKernel hL eC hC eta hEta
  obtain ⟨hKernelRetract, hConeRetract⟩ := roos_comparison_homotopies A I J u r hr
    P L C eP hP oneSubS hS iota hKernel hL eC hC
    PJ LJ CJ ePJ hPJ sJ hSJ iJ hKJ hLJ eCJ hCJ
    lU cU lR cR hlU hcU hlR hcR
  exact ⟨lU, cU, lR, cR, hU, hR, hKernelRetract, hConeRetract⟩

end CategoryTheory
