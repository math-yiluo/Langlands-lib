/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.LocalImmersionLocus

/-! # Gluing locally finitely presented immersion loci

Source: Stacks Project, Tag 0BDL, final proof paragraph (gluing characterized loci).
(blueprint: lem-sc-local-finitely-presented-immersion-locus).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A base-change-stable, source-local predicate represented locally by locally
finitely presented immersions is represented by such an immersion over the entire base.
Source: Stacks Project, Tag 0BDL, final proof paragraph, spelling out the gluing.
(blueprint: lem-sc-local-finitely-presented-immersion-locus).

Proof:
1. Forget local finite presentation in hlocal and apply the existing
   exists_localImmersionLocus. This supplies an immersion q:Z to S representing P,
   including empty bases and empty test schemes.
2. Choose the given local representatives j_i:W_i to U_i and form the open cover
   of S indexed by its points. For each i, the pullback of q to U_i and j_i
   represent the same predicate. The global and local representing equivalences
   give a morphism a from the pullback to W_i and a morphism b from W_i to Z.
   The pullback universal property lifts b and j_i to a reverse morphism c.
   Cancelling the monomorphisms j_i and the pullback of q shows a and c are inverse.
3. Thus the pullback of q is an isomorphism followed by j_i, so it is locally of
   finite presentation. Apply target locality on the chosen open cover. The
   immersion and representing equivalence are those already supplied in step 1. -/
theorem exists_localFinitelyPresentedImmersionLocus (S : Scheme.{u})
    (P : ∀ {T : Scheme.{u}}, (T ⟶ S) → Prop)
    (hbase : ∀ {T T' : Scheme.{u}} (g : T ⟶ S) (h : T' ⟶ T), P g → P (h ≫ g))
    (hsource : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (∀ t : T, ∃ V : T.Opens, t ∈ V ∧ P (V.ι ≫ g)) → P g)
    (hlocal : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ (W : Scheme.{u}) (j : W ⟶ U.toScheme), IsImmersion j ∧ LocallyOfFinitePresentation j ∧
        ∀ {T : Scheme.{u}} (g : T ⟶ U.toScheme),
          (∃ h : T ⟶ W, h ≫ j = g) ↔ P (g ≫ U.ι)) :
    ∃ (W : Scheme.{u}) (j : W ⟶ S),
      IsImmersion j ∧ LocallyOfFinitePresentation j ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S), (∃ h : T ⟶ W, h ≫ j = g) ↔ P g := by
  classical
  obtain ⟨Z, q, hq, hrep⟩ := exists_localImmersionLocus S P hbase hsource (by
    intro s
    obtain ⟨U, hs, W, j, hj, _, hlocalrep⟩ := hlocal s
    exact ⟨U, hs, W, j, hj, hlocalrep⟩)
  have : IsImmersion q := hq
  choose U hs W j hj hjfp hlocalrep using hlocal
  let 𝒰 : S.OpenCover := {
    I₀ := S
    X i := (U i).toScheme
    f i := (U i).ι
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      exact ⟨fun i ↦ ⟨i, by simpa using hs i⟩, fun i ↦ inferInstance⟩ }
  have hqfp : LocallyOfFinitePresentation q := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @LocallyOfFinitePresentation) 𝒰
    intro i
    change LocallyOfFinitePresentation (Limits.pullback.snd q (U i).ι)
    have : IsImmersion (j i) := hj i
    have : LocallyOfFinitePresentation (j i) := hjfp i
    obtain ⟨a, ha⟩ := (hlocalrep i (Limits.pullback.snd q (U i).ι)).mpr (by
      rw [← Limits.pullback.condition]
      exact (hrep _).mp ⟨Limits.pullback.fst q (U i).ι, rfl⟩)
    obtain ⟨b, hb⟩ := (hrep (j i ≫ (U i).ι)).mpr (by
      exact (hlocalrep i (j i)).mp ⟨𝟙 _, Category.id_comp _⟩)
    let c := Limits.pullback.lift b (j i) hb
    have hc : c ≫ Limits.pullback.snd q (U i).ι = j i := by
      exact Limits.pullback.lift_snd _ _ _
    have hac : a ≫ c = 𝟙 _ := by
      apply (cancel_mono (Limits.pullback.snd q (U i).ι)).1
      rw [Category.assoc, hc, ha, Category.id_comp]
    have hca : c ≫ a = 𝟙 _ := by
      apply (cancel_mono (j i)).1
      rw [Category.assoc, ha, hc, Category.id_comp]
    let e : Limits.pullback q (U i).ι ≅ W i := ⟨a, c, hac, hca⟩
    have : IsIso a := e.isIso_hom
    rw [← ha]
    change LocallyOfFinitePresentation (e.hom ≫ j i)
    infer_instance
  exact ⟨Z, q, hq, hqfp, hrep⟩

end AlgebraicGeometry.Scheme
