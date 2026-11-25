/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.FilteredComplexBoundariesLECycles
import all WeilConjectures.CategoryTheory.FilteredComplexBoundariesLECycles
import WeilConjectures.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject

/-!
# Descent of one filtered differential through the cycle-boundary quotients

Source: Stacks Project, Homology, Tag 012K, displayed differential formula.
(blueprint: lem-sp-filtered-complex-single-differential-descent).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem graded_kernel (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n : ℤ) :
    kernelSubobject ((F.complexQuotientπ p (p + 1) (by omega)).f n) =
      imageSubobject ((Subobject.ofLE (F.step (p + 1)) (F.step p)
        (F.antitone_step (by omega))).f n) := by
  let l := Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))
  have h := (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk l (cokernel.π l) (cokernel.condition l))
    (cokernelIsCokernel l)).map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)
  exact ((ShortComplex.exact_iff_image_eq_kernel _).mp h).symm

/-- A representative of the zero source page class differentiates to a zero target class.
Source: Stacks Project, Tag 012K, displayed boundary and differential formulas.

Proof. Put p = i.1 and n = i.1+i.2. Factor x through the source boundary
inclusion using its cokernel. Refine along the epimorphism from boundary
representatives to their graded image. The difference between the given t and
the resulting boundary representative has zero graded projection, hence factors
through F^(p+1), the degreewise kernel of that projection. The differential
sends the ambient boundary representative sum into d(F^(p+1)): it kills the
incoming differential image by d squared = 0, and maps F^(p+1) into its image.
The difference has its differential in this same image. Their sum dt therefore
lies in d(F^(p+1)). Since dt=tprime also lies in F^(p+r), it is a target boundary,
whose incoming filtration degree is (p+r)-r+1=p+1. Project to target graded
boundaries and use monicity of the cycle inclusion to obtain a factorization
of the refined y through the boundary inclusion. Its cokernel projection is
zero, and cancellation of the refining epimorphism concludes. The argument
works for every integer r and uses no elementwise lifting. -/
private theorem filteredComplex_differential_zero_class
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ)
    (i j : ℤ × ℤ) (hij : (ComplexShape.up' (r, 1 - r)).Rel i j)
    (A : C)
    (t : A ⟶ (F.step i.1 : CochainComplex C ℤ).X (i.1 + i.2))
    (t' : A ⟶ (F.step j.1 : CochainComplex C ℤ).X (j.1 + j.2))
    (x : A ⟶ (F.complexCycles i.1 (i.1 + i.2) r : C))
    (y : A ⟶ (F.complexCycles j.1 (j.1 + j.2) r : C))
    (ht : t ≫ (F.step i.1).arrow.f (i.1 + i.2) ≫
      K.d (i.1 + i.2) (j.1 + j.2) = t' ≫ (F.step j.1).arrow.f (j.1 + j.2))
    (hx : x ≫ (F.complexCycles i.1 (i.1 + i.2) r).arrow =
      t ≫ (F.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2))
    (hy : y ≫ (F.complexCycles j.1 (j.1 + j.2) r).arrow =
      t' ≫ (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2))
    (hzero : x ≫ cokernel.π (Subobject.ofLE _ _
      (filteredComplex_boundaries_le_cycles K F i.1 (i.1 + i.2) r)) = 0) :
    y ≫ cokernel.π (Subobject.ofLE _ _
      (filteredComplex_boundaries_le_cycles K F j.1 (j.1 + j.2) r)) = 0 := by
  classical
  have hp : i.1 + r = j.1 := congrArg (fun pq : ℤ × ℤ ↦ pq.1) hij
  have hn : i.1 + i.2 + 1 = j.1 + j.2 := by
    have hq : i.2 + (1 - r) = j.2 := congrArg (fun pq : ℤ × ℤ ↦ pq.2) hij
    omega
  let f := (F.step i.1).arrow.f (i.1 + i.2)
  let g := (F.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2)
  let S := F.complexStep (i.1 + 1) (i.1 + i.2)
  let V := (F.complexStep i.1 (i.1 + i.2) ⊓
    (Subobject.«exists» (K.d (i.1 + i.2 - 1) (i.1 + i.2))).obj
      (F.complexStep (i.1 - r + 1) (i.1 + i.2 - 1))) ⊔ S
  let U := (Subobject.pullback f).obj V
  let inc := Subobject.ofLE _ _
    (filteredComplex_boundaries_le_cycles K F i.1 (i.1 + i.2) r)
  let β := Abelian.monoLift inc x hzero
  have hβ : β ≫ inc = x := Abelian.monoLift_comp inc x hzero
  obtain ⟨ε, hε, hεfac⟩ := Subobject.exists_fac g U
  have : Epi ε := hε
  change ε ≫ (F.complexBoundaries i.1 (i.1 + i.2) r).arrow = U.arrow ≫ g at hεfac
  obtain ⟨A₁, a, ha, b, hab⟩ := surjective_up_to_refinements_of_epi ε β
  have : Epi a := ha
  have hgraded : (a ≫ t) ≫ g = (b ≫ U.arrow) ≫ g := by
    calc
      (a ≫ t) ≫ g = a ≫ (x ≫ (F.complexCycles i.1 (i.1 + i.2) r).arrow) := by
        rw [hx]
        simp only [Category.assoc, g]
      _ = (a ≫ β) ≫ (F.complexBoundaries i.1 (i.1 + i.2) r).arrow := by
        rw [← hβ]
        simp only [Category.assoc, inc, Subobject.ofLE_arrow]
      _ = (b ≫ ε) ≫ (F.complexBoundaries i.1 (i.1 + i.2) r).arrow := by rw [hab]
      _ = (b ≫ U.arrow) ≫ g := by rw [Category.assoc, hεfac, Category.assoc]
  let z := a ≫ t - b ≫ U.arrow
  have hz : z ≫ g = 0 := by
    dsimp [z]
    rw [Preadditive.sub_comp, hgraded, sub_self]
  have hzker := kernelSubobject_factors g z hz
  rw [graded_kernel K F] at hzker
  rw [imageSubobject_mono] at hzker
  obtain ⟨k, hk⟩ := (Subobject.mk_factors_iff _ _).mp hzker
  let l := Subobject.ofLE (F.step (i.1 + 1)) (F.step i.1)
    (F.antitone_step (by omega))
  change k ≫ l.f (i.1 + i.2) = z at hk
  have hl : l.f (i.1 + i.2) ≫ f = (F.step (i.1 + 1)).arrow.f (i.1 + i.2) :=
    congrArg (fun φ : (F.step (i.1 + 1) : CochainComplex C ℤ) ⟶ K ↦
      φ.f (i.1 + i.2)) (Subobject.ofLE_arrow _)
  have hzS : S.Factors (z ≫ f) := by
    rw [← hk, Category.assoc, hl]
    exact imageSubobject_factors_comp_self _ _
  let d := K.d (i.1 + i.2) (j.1 + j.2)
  let T := (Subobject.«exists» d).obj S
  have hVT : V ≤ (Subobject.pullback d).obj T := by
    apply sup_le
    · apply inf_le_right.trans
      exact image_le_pullback _ _ (K.d_comp_d _ _ _) _ _
    · exact leOfHom ((Subobject.existsPullbackAdj d).unit.app S)
  have hbV : V.Factors ((b ≫ U.arrow) ≫ f) := by
    apply (pullback_factors_iff f V _).mp
    exact Subobject.factors_comp_arrow b
  have hbT : T.Factors ((b ≫ U.arrow) ≫ f ≫ d) := by
    rw [← Category.assoc]
    apply (pullback_factors_iff d T _).mp
    exact Subobject.factors_of_le _ hVT hbV
  have hzT : T.Factors (z ≫ f ≫ d) := by
    rw [← Category.assoc]
    apply (pullback_factors_iff d T _).mp
    exact Subobject.factors_of_le _ (le_sup_right.trans hVT) hzS
  have htT : T.Factors (a ≫ t ≫ f ≫ d) := by
    have hadd := Subobject.factors_add _ _ hzT hbT
    simpa only [z, Preadditive.sub_comp, Category.assoc, sub_add_cancel] using hadd
  have ht'T : T.Factors ((a ≫ t') ≫ (F.step j.1).arrow.f (j.1 + j.2)) := by
    simpa only [Category.assoc, ht, f, d] using htT
  have hT : T = (Subobject.«exists» (K.d (j.1 + j.2 - 1) (j.1 + j.2))).obj
      (F.complexStep (j.1 - r + 1) (j.1 + j.2 - 1)) := by
    have hni : i.1 + i.2 = j.1 + j.2 - 1 := by omega
    have hpi : i.1 + 1 = j.1 - r + 1 := by omega
    dsimp [T, S, d]
    rw [hni, hpi]
  rw [hT] at ht'T
  let f' := (F.step j.1).arrow.f (j.1 + j.2)
  let g' := (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2)
  let V' := (F.complexStep j.1 (j.1 + j.2) ⊓
    (Subobject.«exists» (K.d (j.1 + j.2 - 1) (j.1 + j.2))).obj
      (F.complexStep (j.1 - r + 1) (j.1 + j.2 - 1))) ⊔
    F.complexStep (j.1 + 1) (j.1 + j.2)
  let U' := (Subobject.pullback f').obj V'
  have ht'V : V'.Factors ((a ≫ t') ≫ f') := by
    apply Subobject.sup_factors_of_factors_left
    apply (Subobject.inf_factors _).mpr
    exact ⟨imageSubobject_factors_comp_self _ _, ht'T⟩
  have ht'U : U'.Factors (a ≫ t') := (pullback_factors_iff f' V' _).mpr ht'V
  have hyB : (F.complexBoundaries j.1 (j.1 + j.2) r).Factors
      ((a ≫ y) ≫ (F.complexCycles j.1 (j.1 + j.2) r).arrow) := by
    rw [Category.assoc, hy, ← Category.assoc]
    change ((Subobject.«exists» g').obj U').Factors ((a ≫ t') ≫ g')
    rw [← Subobject.factorThru_arrow U' _ ht'U, Category.assoc]
    rw [← (Subobject.imageFactorisation g' U').F.fac]
    rw [← Category.assoc, Subobject.imageFactorisation_F_m]
    exact Subobject.factors_comp_arrow _
  let inc' := Subobject.ofLE _ _
    (filteredComplex_boundaries_le_cycles K F j.1 (j.1 + j.2) r)
  have hyfac : (Subobject.factorThru _ _ hyB) ≫ inc' = a ≫ y := by
    apply (cancel_mono (F.complexCycles j.1 (j.1 + j.2) r).arrow).1
    simp only [Category.assoc, inc', Subobject.ofLE_arrow, Subobject.factorThru_arrow]
  apply (cancel_epi a).1
  rw [← Category.assoc, ← hyfac, Category.assoc, cokernel.condition, comp_zero, comp_zero]



/-- The underlying complex differential descends between the two actual cokernels
in one related pair of bidegrees. No square-zero or uniqueness assertion is included.
Source: Stacks Project, Tag 012K, displayed differential formula.
(blueprint: lem-sp-filtered-complex-single-differential-descent).

Proof. Take an epimorphic family of simultaneous representatives t,tprime,x,y
from filteredComplex_differential_representatives_cover and let e = x followed
by the source boundary cokernel projection. This composite is epic. Apply the
zero-class calculation to the kernel of e: its target representative projects
to zero. The abelian cokernel universal property therefore descends y followed
by the target projection through e to a morphism delta between the page objects.
For any other representatives, pull back e along their source page class. The
projection to their test object is epic. Subtract the two families after this
pullback; their source page class is zero by the pullback equation. The
zero-class calculation makes their target page classes equal. Use the descent
equation, then cancel the pullback epimorphism, to obtain the asserted formula
on the original test object. All constructions use finite limits and cokernels. -/
theorem filteredComplex_single_differential_descent
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (i j : ℤ × ℤ) (hij : (ComplexShape.up' (r, 1 - r)).Rel i j) :
    let Q := fun pq : ℤ × ℤ ↦ cokernel (Subobject.ofLE _ _
      (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) r))
    let π := fun pq : ℤ × ℤ ↦ cokernel.π (Subobject.ofLE _ _
      (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) r))
    ∃ δ : Q i ⟶ Q j,
      ∀ (A : C)
        (t : A ⟶ (F.step i.1 : CochainComplex C ℤ).X (i.1 + i.2))
        (t' : A ⟶ (F.step j.1 : CochainComplex C ℤ).X (j.1 + j.2))
        (x : A ⟶ (F.complexCycles i.1 (i.1 + i.2) r : C))
        (y : A ⟶ (F.complexCycles j.1 (j.1 + j.2) r : C)),
        t ≫ (F.step i.1).arrow.f (i.1 + i.2) ≫ K.d (i.1 + i.2) (j.1 + j.2) =
          t' ≫ (F.step j.1).arrow.f (j.1 + j.2) →
        x ≫ (F.complexCycles i.1 (i.1 + i.2) r).arrow =
          t ≫ (F.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2) →
        y ≫ (F.complexCycles j.1 (j.1 + j.2) r).arrow =
          t' ≫ (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2) →
        x ≫ π i ≫ δ = y ≫ π j := by
  classical
  by_cases hpos : 1 ≤ r
  swap
  · exact (hpos hr).elim
  dsimp only
  let π := fun pq : ℤ × ℤ ↦ cokernel.π (Subobject.ofLE _ _
    (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) r))
  obtain ⟨A, t, t', x, y, hx, ht, hxt, hyt⟩ :=
    filteredComplex_differential_representatives_cover K F r i j hij
  have : Epi x := hx
  let e := x ≫ π i
  have : Epi e := by dsimp [e, π]; infer_instance
  have hk : kernel.ι e ≫ (y ≫ π j) = 0 := by
    rw [← Category.assoc]
    apply filteredComplex_differential_zero_class K F r i j hij (kernel e)
      (kernel.ι e ≫ t) (kernel.ι e ≫ t') (kernel.ι e ≫ x) (kernel.ι e ≫ y)
    · simpa only [Category.assoc] using congrArg (kernel.ι e ≫ ·) ht
    · simpa only [Category.assoc] using congrArg (kernel.ι e ≫ ·) hxt
    · simpa only [Category.assoc] using congrArg (kernel.ι e ≫ ·) hyt
    · simpa only [Category.assoc] using kernel.condition e
  let δ := Abelian.epiDesc e (y ≫ π j) hk
  have hδ : e ≫ δ = y ≫ π j := Abelian.comp_epiDesc e (y ≫ π j) hk
  refine ⟨δ, ?_⟩
  intro B s s' z w hs hzs hws
  let a := pullback.fst e (z ≫ π i)
  let b := pullback.snd e (z ≫ π i)
  have hab : a ≫ e = b ≫ (z ≫ π i) := pullback.condition
  have hz : (a ≫ x - b ≫ z) ≫ π i = 0 := by
    rw [Preadditive.sub_comp]
    exact sub_eq_zero.mpr (by simpa only [e, Category.assoc] using hab)
  have hw : (a ≫ y - b ≫ w) ≫ π j = 0 := by
    apply filteredComplex_differential_zero_class K F r i j hij
      (pullback e (z ≫ π i)) (a ≫ t - b ≫ s) (a ≫ t' - b ≫ s')
      (a ≫ x - b ≫ z) (a ≫ y - b ≫ w)
    · simp only [Preadditive.sub_comp, Category.assoc, ht, hs]
    · simp only [Preadditive.sub_comp, Category.assoc, hxt, hzs]
    · simp only [Preadditive.sub_comp, Category.assoc, hyt, hws]
    · exact hz
  have hw' : a ≫ (y ≫ π j) = b ≫ (w ≫ π j) := by
    simpa only [Preadditive.sub_comp, Category.assoc, sub_eq_zero] using hw
  apply (cancel_epi b).1
  calc
    b ≫ (z ≫ π i ≫ δ) = (b ≫ (z ≫ π i)) ≫ δ := by simp only [Category.assoc]
    _ = (a ≫ e) ≫ δ := by rw [hab]
    _ = a ≫ (y ≫ π j) := by rw [Category.assoc, hδ]
    _ = b ≫ (w ≫ π j) := hw'

end CategoryTheory
