/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RecordedPerfectHomTransport
import WeilConjectures.AlgebraicGeometry.RecordedPerfectHomNormalization
import WeilConjectures.AlgebraicGeometry.PerfectHomContinuity
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
/-! # Continuity of Hom sets for perfect complexes in a ring-colimit system.
Source: Stacks Project, perfect.tex, Tag 09RE, affine calculation and open induction.
(blueprint: lem-pc-recorded-perfect-hom-continuity).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical Hom map is surjective on every cofinal tail, and two representatives
with the same image agree on some entire later tail. These are the set-colimit
consequences of continuity of Hom; no isomorphism descent or finite collection of
relations is asserted here.
Source: Stacks Project, perfect.tex, Tag 09RE, proof of lemma-descend-homomorphisms
(blueprint: lem-pc-recorded-perfect-hom-continuity).

Proof: choose the universal change-of-counit automorphisms in
`exists_recordedPerfectHom_normalization`. Conjugate the desired limit morphism
by the inverse automorphism at P and the forward automorphism at Q. The existing
Hom continuity theorem lifts it to a finite stage on the desired tail. Conjugate
this lift by the forward stage automorphism at P and its inverse at Q. The
normalization equation and inverse cancellation give its required limit image.
For equality, the normalization equation cancels the outer limit automorphisms,
so the two stage morphisms conjugated by the inverse stage automorphisms have
equal old limit images. Apply old tail equality to them. The normalization equation
at every later stage transports this equality back to the recorded Hom maps. -/
theorem recorded_perfect_hom_continuity
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (X : Scheme.{u}) (s : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (P Q : schemeDerivedCategory X) (hP : X.IsPerfect P) (hQ : X.IsPerfect Q) :
    (∀ (j₀ : I) (hij₀ : i ≤ j₀)
      (φ : (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
        (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q),
      ∃ (j : I) (hj₀j : j₀ ≤ j)
        (f : (derivedPullback
            (pullback.fst s (Spec.map (R.map (homOfLE (hij₀.trans hj₀j)))))).obj P ⟶
          (derivedPullback
            (pullback.fst s (Spec.map (R.map (homOfLE (hij₀.trans hj₀j)))))).obj Q),
        recordedPerfectLimitMap R c s (hij₀.trans hj₀j) f = φ) ∧
    (∀ (j : I) (hij : i ≤ j)
      (a b : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
        (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q),
      recordedPerfectLimitMap R c s hij a = recordedPerfectLimitMap R c s hij b →
      ∃ (k : I) (hjk : j ≤ k), ∀ (l : I) (hkl : k ≤ l),
        recordedPerfectStageMap R s hij (hjk.trans hkl) a =
          recordedPerfectStageMap R s hij (hjk.trans hkl) b) := by
  obtain ⟨e, he⟩ := exists_recordedPerfectHom_normalization.{u, w}
  have hlimit {j : I} (hij : i ≤ j)
      (a : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
        (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q) :
      recordedPerfectLimitMap R c s hij a =
        (e (pullback.fst s (Spec.map (c.ι.app i)))).hom.app P ≫
          perfectLimitMap R c s hij
            ((e (pullback.fst s (Spec.map (R.map (homOfLE hij))))).inv.app P ≫ a ≫
              (e (pullback.fst s (Spec.map (R.map (homOfLE hij))))).hom.app Q) ≫
                (e (pullback.fst s (Spec.map (c.ι.app i)))).inv.app Q := by
    exact he s
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) P Q a
  have hstage {j k : I} (hij : i ≤ j) (hjk : j ≤ k)
      (a : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
        (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q) :
      recordedPerfectStageMap R s hij hjk a =
        (e (pullback.fst s (Spec.map (R.map (homOfLE (hij.trans hjk)))))).hom.app P ≫
          perfectStageMap R s hij hjk
            ((e (pullback.fst s (Spec.map (R.map (homOfLE hij))))).inv.app P ≫ a ≫
              (e (pullback.fst s (Spec.map (R.map (homOfLE hij))))).hom.app Q) ≫
                (e (pullback.fst s (Spec.map (R.map (homOfLE (hij.trans hjk)))))).inv.app Q := by
    exact he s
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
      (Over.homMk (Spec.map (R.map (homOfLE hjk)))
        (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) P Q a
  obtain ⟨hsurj, heq⟩ := perfect_hom_continuity R c hc i X s P Q hP hQ
  constructor
  · intro j₀ hij₀ φ
    obtain ⟨j, hj₀j, a, ha⟩ := hsurj j₀ hij₀
      ((e (pullback.fst s (Spec.map (c.ι.app i)))).inv.app P ≫ φ ≫
        (e (pullback.fst s (Spec.map (c.ι.app i)))).hom.app Q)
    refine ⟨j, hj₀j,
      (e (pullback.fst s (Spec.map (R.map (homOfLE (hij₀.trans hj₀j)))))).hom.app P ≫
        a ≫ (e (pullback.fst s (Spec.map (R.map (homOfLE (hij₀.trans hj₀j)))))).inv.app Q,
      ?_⟩
    rw [hlimit]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
      Category.comp_id]
    rw [ha]
    simp
  · intro j hij a b hab
    rw [hlimit, hlimit] at hab
    simp only [cancel_epi, cancel_mono] at hab
    obtain ⟨k, hjk, hk⟩ := heq j hij _ _ hab
    refine ⟨k, hjk, fun l hkl ↦ ?_⟩
    rw [hstage, hstage, hk l hkl]

end AlgebraicGeometry
