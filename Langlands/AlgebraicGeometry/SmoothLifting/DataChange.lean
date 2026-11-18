import Langlands.AlgebraicGeometry.SmoothLifting.LiftModule

/-! # Base change of the lifting data along a ring map

For a `C`-algebra `C'`, lifts on `C'` of the data `(f, I, x₀, s)` are exactly global lifts of the
base-changed data `(f, I C', x₀|, s|)`. Restriction from `C` to `C'` commutes with global affine
combinations, hence is semilinear on modules of lifts.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace Langlands.AlgebraicGeometry.SmoothLifting

variable {X S : Scheme.{u}} {f : X ⟶ S} {C : CommRingCat.{u}} {I : Ideal C}
  {x₀ : Spec (CommRingCat.of (C ⧸ I)) ⟶ X} {s : Spec C ⟶ S}

variable (C' : Type u) [CommRing C'] [Algebra C C']

/-- The base-changed ideal. -/
abbrev bcI : Ideal (CommRingCat.of C') := redIdeal I C'

variable (x₀) in
/-- The base-changed reduced point. -/
abbrev bcx₀ : Spec (CommRingCat.of (CommRingCat.of C' ⧸ bcI (I := I) C')) ⟶ X :=
  Spec.map (redStruct I C') ≫ x₀

variable (s) in
/-- The base-changed structure morphism. -/
abbrev bcs : Spec (CommRingCat.of C') ⟶ S := Spec.map (strMap (C := C) C') ≫ s

theorem isLift_iff_isGlobalLift (y : Spec (CommRingCat.of C') ⟶ X) :
    IsLift f I x₀ s C' y ↔ IsGlobalLift f (bcI (I := I) C') (bcx₀ x₀ C') (bcs s C') y := Iff.rfl

theorem IsGlobalLift.res {y : Spec C ⟶ X} (hy : IsGlobalLift f I x₀ s y) :
    IsGlobalLift f (bcI (I := I) C') (bcx₀ x₀ C') (bcs s C') (restrC C' y) :=
  hy.isLift C'

/-- Restriction of global lifts to a `C`-algebra. -/
def GLift.res (y : GLift f I x₀ s) : GLift f (bcI (I := I) C') (bcx₀ x₀ C') (bcs s C') :=
  ⟨restrC C' y.1, y.2.isLift C'⟩

/-- Transport of a chart along `C → C'`. -/
def Chart.bc (ch : Chart f I x₀ s) : Chart f (bcI (I := I) C') (bcx₀ x₀ C') (bcs s C') where
  V := ch.V
  hV := ch.hV
  U := ch.U
  hU := ch.hU
  hUV := ch.hUV
  g := algebraMap C C' ch.g
  hs p hp := by
    rw [Scheme.Hom.comp_apply]
    exact ch.hs _ hp
  hx p hp := by
    rw [Scheme.Hom.comp_apply]
    exact ch.hx _ hp

theorem affComb_congr_ideal {B R : Type*} [CommRing B] [CommRing R] {ι : Type*} [Fintype ι]
    (J₁ J₂ : Ideal R) (hJ₁ : SqZero J₁) (hJ₂ : SqZero J₂) (φ₀ : B →+* R) (φ : ι → B →+* R)
    (h₁ : ∀ k b, φ k b - φ₀ b ∈ J₁) (h₂ : ∀ k b, φ k b - φ₀ b ∈ J₂) (c : ι → R) :
    affComb J₁ hJ₁ φ₀ φ h₁ c = affComb J₂ hJ₂ φ₀ φ h₂ c :=
  RingHom.ext fun _ => rfl

theorem restrC_restrC {T : Type u} [CommRing T] [Algebra C T] [Algebra C' T]
    [IsScalarTower C C' T] (y : Spec C ⟶ X) :
    Spec.map (CommRingCat.ofHom (algebraMap C' T)) ≫ restrC C' y = restrC T y := by
  rw [restrC, restrC, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

/-- Chart representatives are unchanged by base change of the data. -/
theorem Chart.rep_bc (hI : SqZero I) (ch : Chart f I x₀ s)
    {T : Type u} [CommRing T] [Algebra C T] [Algebra C' T] [IsScalarTower C C' T]
    (hg : IsUnit (algebraMap C T ch.g)) (hg' : IsUnit (algebraMap C' T (ch.bc C').g))
    {z : Spec (CommRingCat.of T) ⟶ X} (hz : IsLift f I x₀ s T z)
    (hz' : IsLift f (bcI (I := I) C') (bcx₀ x₀ C') (bcs s C') T z) :
    (ch.bc C').rep T (hI.map _) hg' z hz' = ch.rep T hI hg z hz :=
  chartRep_eq _ _ _ (ch.rep_spec T hI hg z hz)

/-- **Restriction commutes with global affine combinations.** -/
theorem gcomb_res {ι : Type} [Fintype ι] (hI : SqZero I) {y₀ : Spec C ⟶ X}
    (hy₀ : IsGlobalLift f I x₀ s y₀) {y : ι → (Spec C ⟶ X)}
    (hy : ∀ k, IsGlobalLift f I x₀ s (y k)) (c : ι → C) :
    restrC C' (gcomb hI hy₀ hy c) =
      gcomb (hI.map (algebraMap C C')) (hy₀.res C') (fun k => (hy k).res C')
        (fun k => algebraMap C C' (c k)) := by
  classical
  obtain ⟨n, chs, hspan⟩ := exists_charts hI hy₀.h₀
  have hspan' : Ideal.span (Set.range fun i => ((chs i).bc C').g) = ⊤ := by
    change Ideal.span (Set.range fun i => algebraMap C C' (chs i).g) = ⊤
    rw [Set.range_comp' (algebraMap C C') (fun i => (chs i).g), ← Ideal.map_span, hspan,
      Ideal.map_top]
  refine IsGlobalLift.ext_of_charts (fun i => (chs i).bc C') hspan' fun i => ?_
  let T := Loc ((chs i).bc C').g
  have hg' : IsUnit (algebraMap C' T ((chs i).bc C').g) := isUnit_loc _
  have hg : IsUnit (algebraMap C T (chs i).g) := by
    rw [IsScalarTower.algebraMap_apply C C' T]; exact hg'
  change Spec.map (CommRingCat.ofHom (algebraMap C' T)) ≫ restrC C' _ =
    Spec.map (CommRingCat.ofHom (algebraMap C' T)) ≫ _
  have hL : IsLift f (bcI (I := I) C') (bcx₀ x₀ C') (bcs s C') T
      (Spec.map (CommRingCat.ofHom (algebraMap C' T)) ≫ restrC C' (gcomb hI hy₀ hy c)) :=
    ((gcomb_isGlobalLift hI hy₀ hy c).res C').isLift T
  have hR := (gcomb_isGlobalLift (hI.map (algebraMap C C')) (hy₀.res C') (fun k => (hy k).res C')
    (fun k => algebraMap C C' (c k))).isLift T
  refine ((chs i).bc C').eq_of_rep (hI.map _) hg' hL hR fun b => ?_
  have hLC : IsLift f I x₀ s T (Spec.map (CommRingCat.ofHom (algebraMap C' T)) ≫
      restrC C' (gcomb hI hy₀ hy c)) := by
    rw [restrC_restrC]; exact (gcomb_isGlobalLift hI hy₀ hy c).isLift T
  rw [(chs i).rep_bc C' hI hg hg' hLC hL]
  have e1 := (chs i).rep_congr hI hg hLC ((chs i).comb_isLift T hI hg _ _ _ _ _)
    ((restrC_restrC C' _).trans (gcomb_restr hI hy₀ hy c (chs i) T hg)) b
  refine e1.trans (((chs i).rep_comb_apply hI hg _ _ _ _ _ _ b).trans ?_)
  have e2 := ((chs i).bc C').rep_congr (hI.map _) hg' hR
    (((chs i).bc C').comb_isLift T (hI.map _) hg' _ _ _ _ _)
    (gcomb_restr _ _ _ _ ((chs i).bc C') T hg') b
  refine Eq.trans ?_ (e2.trans (((chs i).bc C').rep_comb_apply (hI.map _) hg' _ _ _ _ _ _ b)).symm
  have e3 : ∀ (w : Spec C ⟶ X) (hw : IsGlobalLift f I x₀ s w),
      (((chs i).bc C').rep T (hI.map _) hg' (restrC (C := CommRingCat.of C') T (restrC C' w))
        ((hw.res C').isLift T)).hom b = ((chs i).rep T hI hg (restrC T w) (hw.isLift T)).hom b := by
    intro w hw
    have hw' : IsLift f I x₀ s T (restrC (C := CommRingCat.of C') T (restrC C' w)) := by
      rw [show restrC (C := CommRingCat.of C') T (restrC C' w) = restrC T w from
        restrC_restrC C' w]; exact hw.isLift T
    rw [(chs i).rep_bc C' hI hg hg' hw' ((hw.res C').isLift T)]
    exact (chs i).rep_congr hI hg hw' (hw.isLift T) (restrC_restrC C' w) b
  have a0 := e3 y₀ hy₀
  refine congrArg₂ (· + ·) a0.symm (Finset.sum_congr rfl fun k _ => ?_)
  refine congrArg₂ (· * ·) (IsScalarTower.algebraMap_apply C C' T (c k)) ?_
  exact congrArg₂ (· - ·) (e3 (y k) (hy k)).symm a0.symm

end Langlands.AlgebraicGeometry.SmoothLifting
