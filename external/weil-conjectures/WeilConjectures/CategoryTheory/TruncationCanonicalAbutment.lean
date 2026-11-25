/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.TruncationCouple
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
public import WeilConjectures.CategoryTheory.ImageFiltration
import WeilConjectures.CategoryTheory.HalfPlaneSharpBounds
import WeilConjectures.CategoryTheory.HalfPlaneConvergence
import WeilConjectures.CategoryTheory.TruncationAbutmentCocone
import WeilConjectures.CategoryTheory.AbutmentImageFiltration
import WeilConjectures.CategoryTheory.AbutmentFinitePageComparison

/-! Canonical truncation-couple proof step. -/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private noncomputable def pageDInclusions
    {B : Type u₂} [Category.{v₂} B] [Abelian B] (X : BigradedExactCouple B 0) :
    ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q
  | 0, _, _ => 𝟙 _
  | r + 1, p, q => (X.pageCouple r).derivedDInclusion p q ≫ pageDInclusions X r p q

private theorem limit_subobjects_stationary
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (L : X.LimitSubobjects) (p q : ℤ) (r : ℕ)
    (h : ∀ t : ℕ, r ≤ t →
      X.cycleBoundaryTower.Z t p q = X.cycleBoundaryTower.Z r p q ∧
      X.cycleBoundaryTower.B t p q = X.cycleBoundaryTower.B r p q) :
    L.Z p q = X.cycleBoundaryTower.Z r p q ∧
      L.B p q = X.cycleBoundaryTower.B r p q := by
  have hZ : Antitone (fun t ↦ X.cycleBoundaryTower.Z t p q) :=
    antitone_nat_of_succ_le (fun t ↦ X.cycleBoundaryTower.Z_decreasing t p q)
  have hB : Monotone (fun t ↦ X.cycleBoundaryTower.B t p q) :=
    monotone_nat_of_le_succ (fun t ↦ X.cycleBoundaryTower.B_increasing t p q)
  constructor
  · apply le_antisymm
    · exact (L.Z_glb p q).1 ⟨r, rfl⟩
    · apply (L.Z_glb p q).2
      rintro _ ⟨t, rfl⟩
      by_cases ht : t ≤ r
      · exact hZ ht
      · exact le_of_eq (h t (by omega)).1.symm
  · apply le_antisymm
    · apply (L.B_lub p q).2
      rintro _ ⟨t, rfl⟩
      by_cases ht : t ≤ r
      · exact hB ht
      · exact le_of_eq (h t (by omega)).2
    · exact (L.B_lub p q).1 ⟨r, rfl⟩

private noncomputable def quotientIsoOfKernel
    {B : Type u₂} [Category.{v₂} B] [Abelian B] {V W T : B}
    (i : V ⟶ W) [Mono i] (f : W ⟶ T) [Epi f]
    (h : kernelSubobject f = Subobject.mk i) : cokernel i ≅ T := by
  let e : kernel f ≅ V := Subobject.isoOfMkEqMk (kernel.ι f) i h
  have he : e.hom ≫ i = kernel.ι f := by simp [e]
  have hif : i ≫ f = 0 := by
    apply (cancel_epi e.hom).1
    rw [← Category.assoc, he, kernel.condition, comp_zero]
  have hfg : kernel.ι f ≫ cokernel.π i = 0 := by
    rw [← he, Category.assoc, cokernel.condition, comp_zero]
  refine
    { hom := cokernel.desc i f hif
      inv := Abelian.epiDesc f (cokernel.π i) hfg
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply (cancel_epi (cokernel.π i)).1
    simp
  · apply (cancel_epi f).1
    simp

private noncomputable def quotientOfLECongr
    {B : Type u₂} [Category.{v₂} B] [Abelian B] {V : B}
    (S T S' T' : Subobject V) (h : S ≤ T) (h' : S' ≤ T')
    (hS : S = S') (hT : T = T') :
    cokernel (Subobject.ofLE S T h) ≅ cokernel (Subobject.ofLE S' T' h') := by
  subst S' T'
  exact Iso.refl _

/-- Canonical abutment maps and finite image filtration of a truncation couple.
Source: Stacks Tags 011R, 011T, 012F, 012U (3), 05TC (2);
blueprint steps 5--7 of lemma-uniform-bound-proper-direct-image--1
(blueprint: lem-sp-truncation-canonical-abutment).

Proof: Include each iterated D image recursively in D. Sharp stabilization identifies
its stable cycles and boundaries with their intersection and union, defining L.
Take H^n=H^n(RF K), and define j by the bridge followed by RF of the truncation
inclusion. Functoriality and the transition-inclusion equation identify j with the
alpha composites. The inclusion tau<=n K -> K is an isomorphism after degree-n
derived cohomology by 05TC (2), so c is an isomorphism. Filter D(0,n) by incoming
alpha images and transport this filtration along c. Negative initial E degrees
make alpha an isomorphism to the left of p=0, giving fullness for p<=0; lower D
vanishing gives zero for p>=n-a+1. Thus the filtration is finite, exhaustive,
separated, and its quotient tower is eventually H^n, proving the inverse-limit
property. At r=max(p+3,q-a+2), lambda=alpha^(-u) identifies F^p with D_r(u,v)
and F^(p+1) with its incoming alpha image. The next D is zero. Exactness therefore
makes g_r induce the quotient isomorphism psi, with the displayed commuting
equation. Transport across c on graded objects and the stabilized quotient map
to obtain Theta. For p<0 both graded objects and the infinite page vanish.
The alpha diagonal colimit is D(0,n); transport its cocone along c to H^n.
The cocone equation follows from the composite-inclusion identity. Its canonical
comparison with the stable page is exactly Theta, so these maps give convergence. -/
theorem truncation_canonical_abutment
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (a : ℤ)
    (ha : ∀ q : ℤ, q < a → IsZero (K.obj.homology q))
    (X : BigradedExactCouple B 0)
    (hD : X.D = TruncationCouple.D F K)
    (hE : X.E = TruncationCouple.E F K)
    (halpha : (∀ p q : ℤ, X.alpha p q =
        eqToHom (by rw [hD]) ≫ TruncationCouple.alpha F K p q ≫
          eqToHom (by rw [hD])))
    (hf : (∀ p q : ℤ, X.f p q =
        eqToHom (by rw [hE]) ≫ TruncationCouple.f F K p q ≫
          eqToHom (by rw [hD])))
    (hg : (∀ p q : ℤ, X.initialG p q =
        eqToHom (by rw [hD]) ≫ TruncationCouple.g F K p q ≫
          eqToHom (by rw [hE])))
    (hDzero : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (hEzero : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q)) :
    ∃ (inc : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q)
        (L : X.LimitSubobjects)
        (H : ℤ → B)
        (hH : H = fun n : ℤ ↦ (DerivedCategory.homologyFunctor B n).obj
          (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K.obj)))
        (j : ∀ n q : ℤ, X.D (n - q) q ⟶ H n)
        (c : ∀ n : ℤ, X.D 0 n ⟶ H n)
        (FA : ∀ n : ℤ, PBCDecreasingFiltration (X.D 0 n))
        (FH : ∀ n : ℤ, PBCDecreasingFiltration (H n)),
        (∀ p q : ℤ, inc 0 p q = 𝟙 _) ∧
        (∀ (r : ℕ) (p q : ℤ), inc (r + 1) p q =
          (X.pageCouple r).derivedDInclusion p q ≫ inc r p q) ∧
        (∀ p q : ℤ,
          L.Z p q = X.cycleBoundaryTower.Z
            ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q ∧
          L.B p q = X.cycleBoundaryTower.B
            ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q ∧
          Nonempty (X.pageInfinity L p q ≅
            X.page (max 2 (max (q - a + 2) (p + 1))).toNat p q)) ∧
        (∀ n q : ℤ, j n q =
          eqToHom (by rw [hD]; unfold TruncationCouple.D; congr 1; omega) ≫
          (TruncationCouple.bridgeIso F (TruncationCouple.truncation K q) n).inv ≫
          (DerivedCategory.homologyFunctor B n).map
            (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE q))) ≫
          eqToHom (by rw [hH])) ∧
        (∀ n : ℤ, c n = eqToHom (by congr 1; omega) ≫ j n n) ∧
        (∀ n : ℤ, IsIso (c n)) ∧
        (∀ n p : ℤ, 0 ≤ p → (FA n).step p =
          imageSubobject (X.incomingAlphaIter p.toNat 0 n)) ∧
        (∀ n p : ℤ, p ≤ 0 → (FA n).step p = ⊤) ∧
        (∀ n : ℤ, FH n = (FA n).image (c n)) ∧
        (∀ n p : ℤ, (FH n).step p = imageSubobject (j n (n - p))) ∧
        (∀ n p : ℤ, p ≤ 0 → (FH n).step p = ⊤) ∧
        (∀ n p : ℤ, n - a + 1 ≤ p → (FH n).step p = ⊥) ∧
        (∀ n : ℤ, (FH n).IsFinite ∧ (FH n).IsExhaustive ∧ (FH n).IsSeparated ∧
          BigradedExactCouple.IsInverseLimit (FH n)) ∧
        (∀ p q : ℤ, p < 0 → IsZero ((FH (p + q)).gradedPiece p) ∧
          IsZero (X.pageInfinity L p q)) ∧
        (∀ (p q : ℤ) (hp : 0 ≤ p),
          ∃ (lambda : X.D 0 (p + q) ⟶
              X.D (p - max (p + 3) (q - a + 2) + 2) (q + max (p + 3) (q - a + 2) - 2))
            (lift : ((FA (p + q)).step p : B) ⟶
              (X.pageCouple ((max (p + 3) (q - a + 2)).toNat - 2)).D
                (p - max (p + 3) (q - a + 2) + 2)
                (q + max (p + 3) (q - a + 2) - 2))
            (psi : (FA (p + q)).gradedPiece p ≅
              X.page (max (p + 3) (q - a + 2)).toNat p q)
            (grc : (FA (p + q)).gradedPiece p ≅ (FH (p + q)).gradedPiece p)
            (stable : X.page (max (p + 3) (q - a + 2)).toNat p q ≅
              X.pageInfinity L p q)
            (Theta : (FH (p + q)).gradedPiece p ≅ X.pageInfinity L p q)
            (cStep : ((FA (p + q)).step p : B) ⟶ ((FH (p + q)).step p : B))
            (hZ : X.cycleBoundaryTower.Z
                ((max (p + 3) (q - a + 2)).toNat - 2) p q = L.Z p q),
            IsIso lambda ∧
            lambda = X.alphaIter
              (-(p - max (p + 3) (q - a + 2) + 2)).toNat 0 (p + q) ≫
                eqToHom (by congr 1 <;> omega) ∧
            IsIso lift ∧
            lift ≫ inc ((max (p + 3) (q - a + 2)).toNat - 2)
                (p - max (p + 3) (q - a + 2) + 2)
                (q + max (p + 3) (q - a + 2) - 2) =
              ((FA (p + q)).step p).arrow ≫ lambda ∧
            cStep ≫ ((FH (p + q)).step p).arrow =
              ((FA (p + q)).step p).arrow ≫ c (p + q) ∧
            cStep ≫ cokernel.π (Subobject.ofLE ((FH (p + q)).step (p + 1))
                ((FH (p + q)).step p) ((FH (p + q)).antitone_step (by omega))) =
              cokernel.π (Subobject.ofLE ((FA (p + q)).step (p + 1))
                ((FA (p + q)).step p) ((FA (p + q)).antitone_step (by omega))) ≫ grc.hom ∧
            X.cycleBoundaryTower.projection
                ((max (p + 3) (q - a + 2)).toNat - 2) p q ≫ stable.hom =
              eqToHom (congrArg (fun S : Subobject (X.E p q) ↦ (S : B)) hZ) ≫
                cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q)
                  (X.limitBoundary_le_cycle L p q)) ∧
            cokernel.π (Subobject.ofLE ((FA (p + q)).step (p + 1))
                ((FA (p + q)).step p) ((FA (p + q)).antitone_step (by omega))) ≫
              psi.hom = lift ≫
              (X.pageCouple ((max (p + 3) (q - a + 2)).toNat - 2)).g
                (p - max (p + 3) (q - a + 2) + 2)
                (q + max (p + 3) (q - a + 2) - 2) ≫
              eqToHom (by unfold BigradedExactCouple.page; congr 1 <;> omega) ∧
            Theta = grc.symm ≪≫ psi ≪≫ stable) ∧
        ∃ (AH : ∀ n : ℤ, X.AlphaColimit n) (hAH : ∀ n : ℤ, (AH n).obj = H n),
          (∀ n p : ℤ, (AH n).ι p ≫ eqToHom (hAH n) =
            eqToHom (by congr 1; omega) ≫ j n (n - p)) ∧
          X.ConvergesTo L AH := by
  classical
  have _ := hf
  have _ := hg
  have _ := ha
  let inc := pageDInclusions X
  have hinc0 : ∀ p q : ℤ, inc 0 p q = 𝟙 _ := fun _ _ ↦ rfl
  have hinc : ∀ (r : ℕ) (p q : ℤ), inc (r + 1) p q =
      (X.pageCouple r).derivedDInclusion p q ≫ inc r p q := fun _ _ _ ↦ rfl
  obtain ⟨L, _⟩ := X.halfPlaneConvergence a hDzero hEzero
  obtain ⟨_, _, _, _, hstationary, _⟩ := halfPlane_sharp_bounds X a hDzero hEzero
  have hL : ∀ p q : ℤ,
      L.Z p q = X.cycleBoundaryTower.Z
        ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q ∧
      L.B p q = X.cycleBoundaryTower.B
        ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q := by
    intro p q
    apply limit_subobjects_stationary X L p q
    intro t ht
    have hk : 2 ≤ max 2 (max (q - a + 2) (p + 1)) := le_max_left _ _
    have hb : max 2 (max (q - a + 2) (p + 1)) ≤ ((t + 2 : ℕ) : ℤ) := by
      omega
    simpa only [Nat.add_sub_cancel] using hstationary p q (t + 2) hb
  obtain ⟨H, hH, j, c, hj, hc, hiso, hcomm, hnorm⟩ :=
    truncation_abutment_cocone F K X hD halpha
  obtain ⟨FA, FH, hFA, hFAtop, hFH, hFHj, hFHtop, hFHbot, hfinite,
      hnegative, hcolimit⟩ :=
    abutment_image_filtration X a hDzero hEzero L H j c hc hiso hcomm hnorm
  have hpage (p q : ℤ) : Nonempty (X.pageInfinity L p q ≅
      X.page (max 2 (max (q - a + 2) (p + 1))).toNat p q) := by
    let r := (max 2 (max (q - a + 2) (p + 1))).toNat - 2
    have := X.cycleBoundaryTower.projection_epi r p q
    refine ⟨quotientOfLECongr (L.B p q) (L.Z p q)
      (X.cycleBoundaryTower.B r p q) (X.cycleBoundaryTower.Z r p q)
      (X.limitBoundary_le_cycle L p q) (X.cycleBoundaryTower.B_le_Z r p q)
      (hL p q).2 (hL p q).1 ≪≫ ?_⟩
    exact quotientIsoOfKernel _ (X.cycleBoundaryTower.projection r p q)
      (X.cycleBoundaryTower.projection_kernel r p q)
  have hgraded := 
    abutment_finite_page_comparison X a hDzero hEzero inc hinc0 hinc L hL
      H c hiso FA FH hFA hFH
  refine ⟨inc, L, H, hH, j, c, FA, FH, hinc0, hinc, ?_, hj, hc, hiso,
    hFA, hFAtop, hFH, hFHj, hFHtop, hFHbot, hfinite, hnegative, hgraded, hcolimit⟩
  intro p q
  exact ⟨(hL p q).1, (hL p q).2, hpage p q⟩

end CategoryTheory
