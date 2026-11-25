/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.FilteredComplexBoundariesLECycles

/-!
# Epimorphic filtered cycle representatives

Source: Stacks Project, Homology, Tag 012K, displayed cycle formula.
(blueprint: lem-sp-filtered-complex-differential-representatives-cover).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem map_pullback_of_le {A B : C} (f : A ⟶ B) [Mono f]
    (P : Subobject B) (hP : P ≤ Subobject.mk f) :
    (Subobject.map f).obj ((Subobject.pullback f).obj P) = P := by
  apply le_antisymm
  · exact leOfHom ((Subobject.mapPullbackAdj f).counit.app P)
  · obtain ⟨t, ht⟩ := (Subobject.mk_factors_iff f P.arrow).mp
      (Subobject.factors_of_le _ hP P.factors_self)
    change t ≫ f = P.arrow at ht
    have htP : ((Subobject.pullback f).obj P).Factors t :=
      (pullback_factors_iff f P t).mpr (by rw [ht]; exact P.factors_self)
    apply Subobject.le_of_factors
    rw [← Subobject.mk_arrow ((Subobject.pullback f).obj P), Subobject.map_mk]
    apply (Subobject.mk_factors_iff _ _).mpr
    exact ⟨Subobject.factorThru _ t htP, by simp [ht]⟩

private theorem graded_image_sup {A B D : C} (f : A ⟶ B) [Mono f] (g : A ⟶ D)
    (R S : Subobject B) (hR : R ≤ Subobject.mk f) (hS : S ≤ Subobject.mk f)
    (hzero : ((Subobject.pullback f).obj S).arrow ≫ g = 0) :
    (Subobject.«exists» g).obj ((Subobject.pullback f).obj (R ⊔ S)) =
      (Subobject.«exists» g).obj ((Subobject.pullback f).obj R) := by
  let T := (Subobject.«exists» g).obj ((Subobject.pullback f).obj R)
  have hR' : R ≤ (Subobject.map f).obj ((Subobject.pullback g).obj T) := by
    rw [← map_pullback_of_le f R hR]
    exact leOfHom ((Subobject.map f).map ((Subobject.existsPullbackAdj g).unit.app _))
  have hS' : S ≤ (Subobject.map f).obj ((Subobject.pullback g).obj T) := by
    rw [← map_pullback_of_le f S hS]
    apply leOfHom
    apply (Subobject.map f).map
    apply homOfLE
    apply Subobject.le_of_factors
    apply (pullback_factors_iff g T _).mpr
    rw [hzero]
    exact Subobject.factors_zero
  apply le_antisymm
  · apply leOfHom
    refine ((Subobject.existsPullbackAdj g).homEquiv _ _).symm ?_
    apply homOfLE
    have h := leOfHom ((Subobject.pullback f).map (homOfLE (sup_le hR' hS')))
    simpa only [Subobject.pullback_map_self] using h
  · exact leOfHom ((Subobject.«exists» g).map
      ((Subobject.pullback f).map (homOfLE le_sup_left)))

/-- For related bidegrees there is an epimorphic family of source graded cycles
with simultaneous representatives for the source and its differential.
Source: Stacks Project, Tag 012K, the displayed cycle and differential formulas.
(blueprint: lem-sp-filtered-complex-differential-representatives-cover).

Proof. Put p = i.1 and n = i.1+i.2, so j.1 = p+r and j.1+j.2 = n+1.
Take A to be R = F^p K^n intersect d-inverse(F^(p+r) K^(n+1)), regarded
as a subobject of F^p K^n, and take t to be its inclusion. Its composite
with d factors through F^(p+r), giving t'. The graded projection of R
has image Z_r^i: adding F^(p+1) before projection does not change this
image, since the graded projection kills F^(p+1). Thus the factorization
x through Z_r^i is epic. The equality d squared = 0 shows that t' lies
in the target cycle representatives, so its graded projection factors
through Z_r^j, giving y. These image factorizations give the three stated
equalities. No elementwise lifting through an epimorphism is used. -/
theorem filteredComplex_differential_representatives_cover
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ)
    (i j : ℤ × ℤ) (hij : (ComplexShape.up' (r, 1 - r)).Rel i j) :
    ∃ (A : C)
      (t : A ⟶ (F.step i.1 : CochainComplex C ℤ).X (i.1 + i.2))
      (t' : A ⟶ (F.step j.1 : CochainComplex C ℤ).X (j.1 + j.2))
      (x : A ⟶ (F.complexCycles i.1 (i.1 + i.2) r : C))
      (y : A ⟶ (F.complexCycles j.1 (j.1 + j.2) r : C)),
      Epi x ∧
      t ≫ (F.step i.1).arrow.f (i.1 + i.2) ≫ K.d (i.1 + i.2) (j.1 + j.2) =
        t' ≫ (F.step j.1).arrow.f (j.1 + j.2) ∧
      x ≫ (F.complexCycles i.1 (i.1 + i.2) r).arrow =
        t ≫ (F.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2) ∧
      y ≫ (F.complexCycles j.1 (j.1 + j.2) r).arrow =
        t' ≫ (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2) := by
  classical
  have hp : i.1 + r = j.1 := congrArg (fun pq : ℤ × ℤ ↦ pq.1) hij
  have hn : i.1 + i.2 + 1 = j.1 + j.2 := by
    have hq : i.2 + (1 - r) = j.2 := congrArg (fun pq : ℤ × ℤ ↦ pq.2) hij
    omega
  let f := (F.step i.1).arrow.f (i.1 + i.2)
  let g : (F.step i.1 : CochainComplex C ℤ).X (i.1 + i.2) ⟶
      (F.gradedPiece i.1).X (i.1 + i.2) :=
    (F.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2)
  let R := F.complexStep i.1 (i.1 + i.2) ⊓
    (Subobject.pullback (K.d (i.1 + i.2) (i.1 + i.2 + 1))).obj
      (F.complexStep (i.1 + r) (i.1 + i.2 + 1))
  let S := F.complexStep (i.1 + 1) (i.1 + i.2)
  let U := (Subobject.pullback f).obj R
  have hf : Mono f := by dsimp [f]; infer_instance
  let inc := Subobject.ofLE (F.step (i.1 + 1)) (F.step i.1)
    (F.antitone_step (by omega))
  have hinc : inc.f (i.1 + i.2) ≫ f = (F.step (i.1 + 1)).arrow.f (i.1 + i.2) := by
    exact congrArg (fun φ : (F.step (i.1 + 1) : CochainComplex C ℤ) ⟶ K ↦
      φ.f (i.1 + i.2)) (Subobject.ofLE_arrow _)
  have hR : R ≤ Subobject.mk f := by
    apply inf_le_left.trans
    dsimp [DecreasingFiltration.complexStep, f]
    rw [imageSubobject_mono]
  have hS : S ≤ Subobject.mk f := by
    exact imageSubobject_le_mk f _ (inc.f (i.1 + i.2)) hinc
  have hzero : ((Subobject.pullback f).obj S).arrow ≫ g = 0 := by
    have hfac := (pullback_factors_iff f S _).mp
      (((Subobject.pullback f).obj S).factors_self)
    change (imageSubobject ((F.step (i.1 + 1)).arrow.f (i.1 + i.2))).Factors _ at hfac
    rw [imageSubobject_mono] at hfac
    obtain ⟨b, hb⟩ := (Subobject.mk_factors_iff _ _).mp hfac
    change b ≫ (F.step (i.1 + 1)).arrow.f (i.1 + i.2) = _ at hb
    have ha : ((Subobject.pullback f).obj S).arrow = b ≫ inc.f (i.1 + i.2) := by
      apply (cancel_mono f).1
      simpa only [Category.assoc, hinc] using hb.symm
    rw [ha, Category.assoc]
    have hg : inc.f (i.1 + i.2) ≫ g = 0 := by
      exact congrArg (fun φ : (F.step (i.1 + 1) : CochainComplex C ℤ) ⟶
        F.gradedPiece i.1 ↦ φ.f (i.1 + i.2)) (cokernel.condition inc)
    rw [hg, comp_zero]
  have hZ : F.complexCycles i.1 (i.1 + i.2) r = (Subobject.«exists» g).obj U := by
    exact graded_image_sup f g R S hR hS hzero
  let t := U.arrow
  have htr : R.Factors (t ≫ f) :=
    (pullback_factors_iff f R t).mp U.factors_self
  have hdt : (F.complexStep j.1 (j.1 + j.2)).Factors
      (t ≫ f ≫ K.d (i.1 + i.2) (j.1 + j.2)) := by
    have hh := Subobject.factors_right_of_inf_factors htr
    have hh' := (pullback_factors_iff _ _ _).mp hh
    rw [← hn]
    simpa only [hp, Category.assoc] using hh'
  rw [DecreasingFiltration.complexStep, imageSubobject_mono] at hdt
  obtain ⟨t', ht⟩ := (Subobject.mk_factors_iff _ _).mp hdt
  change t' ≫ (F.step j.1).arrow.f (j.1 + j.2) =
    t ≫ f ≫ K.d (i.1 + i.2) (j.1 + j.2) at ht
  let e := (Subobject.existsIsoImage g U).symm ≪≫
    Subobject.isoOfEq _ _ hZ.symm
  let x := factorThruImage (t ≫ g) ≫ e.hom
  have hx : x ≫ (F.complexCycles i.1 (i.1 + i.2) r).arrow = t ≫ g := by
    dsimp [x, e]
    simp only [Category.assoc, Subobject.isoOfEq_hom, Subobject.ofLE_arrow]
    simpa only [Subobject.imageFactorisation, ImageFactorisation.copy,
      ImageFactorisation.ofIsoI, MonoFactorisation.copy, MonoFactorisation.ofIsoI,
      Image.imageFactorisation, factorThruImage, Image.monoFactorisation,
      Iso.symm_hom, Category.assoc, t] using (Subobject.imageFactorisation g U).F.fac
  let R' := F.complexStep j.1 (j.1 + j.2) ⊓
    (Subobject.pullback (K.d (j.1 + j.2) (j.1 + j.2 + 1))).obj
      (F.complexStep (j.1 + r) (j.1 + j.2 + 1))
  let f' := (F.step j.1).arrow.f (j.1 + j.2)
  let g' : (F.step j.1 : CochainComplex C ℤ).X (j.1 + j.2) ⟶
      (F.gradedPiece j.1).X (j.1 + j.2) :=
    (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2)
  have htarget : R'.Factors (t' ≫ f') := by
    apply (Subobject.inf_factors _).mpr
    constructor
    · exact imageSubobject_factors_comp_self _ _
    · apply (pullback_factors_iff _ _ _).mpr
      have hz : (t' ≫ f') ≫ K.d (j.1 + j.2) (j.1 + j.2 + 1) = 0 := by
        rw [ht]
        simp only [Category.assoc, K.d_comp_d, comp_zero]
      rw [hz]
      exact Subobject.factors_zero
  let W := (Subobject.pullback f').obj (R' ⊔ F.complexStep (j.1 + 1) (j.1 + j.2))
  have htW : W.Factors t' := (pullback_factors_iff _ _ _).mpr
    (Subobject.sup_factors_of_factors_left htarget)
  let y := (Subobject.factorThru W t' htW) ≫ (Subobject.imageFactorisation g' W).F.e
  have hy : y ≫ (F.complexCycles j.1 (j.1 + j.2) r).arrow = t' ≫ g' := by
    change y ≫ ((Subobject.«exists» g').obj W).arrow = _
    dsimp [y]
    rw [Category.assoc, ← Subobject.imageFactorisation_F_m,
      (Subobject.imageFactorisation g' W).F.fac]
    simp
  refine ⟨(U : C), t, t', x, y, ?_, ht.symm, hx, hy⟩
  dsimp [x]
  infer_instance

end CategoryTheory
