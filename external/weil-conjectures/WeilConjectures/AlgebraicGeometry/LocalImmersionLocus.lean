/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.CompatibleImmersionGluing

/-! # Gluing local immersion loci

Source: Stacks Project, Tag 0BDL, final proof paragraph (gluing characterized loci).
(blueprint: lem-sc-local-immersion-locus).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem exists_factor_of_locally_factors {S W T : Scheme.{u}}
    (j : W ⟶ S) [Mono j] (g : T ⟶ S)
    (hloc : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧
      ∃ h : V.toScheme ⟶ W, h ≫ j = V.ι ≫ g) :
    ∃ h : T ⟶ W, h ≫ j = g := by
  classical
  choose V ht h hh using hloc
  let 𝒰 : T.OpenCover := {
    I₀ := T
    X t := (V t).toScheme
    f t := (V t).ι
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      exact ⟨fun t ↦ ⟨t, by simpa using ht t⟩, fun t ↦ inferInstance⟩ }
  have hglue : ∀ t t' : T,
      Limits.pullback.fst ((V t).ι) ((V t').ι) ≫ h t =
      Limits.pullback.snd ((V t).ι) ((V t').ι) ≫ h t' := by
    intro t t'
    apply (cancel_mono j).1
    rw [Category.assoc, Category.assoc, hh t, hh t',
      ← Category.assoc, ← Category.assoc, Limits.pullback.condition]
  refine ⟨𝒰.glueMorphisms h hglue, 𝒰.hom_ext _ _ fun t ↦ ?_⟩
  rw [← Category.assoc, 𝒰.ι_glueMorphisms h hglue t]
  exact hh t

/-- A base-change-stable, source-local predicate represented locally by immersions
is represented by an immersion over the entire base.
Source: Stacks Project, Tag 0BDL, final proof paragraph, spelling out the gluing.
(blueprint: lem-sc-local-immersion-locus).

Proof:
1. Choose a neighbourhood U_s and its representing immersion for every s.
   The neighbourhoods cover S. On U_s intersect U_t, the two base-changed
   immersions represent the same predicate. Evaluate their universal properties
   on each other to obtain inverse maps; monomorphy of immersions gives uniqueness.
2. These unique isomorphisms satisfy the triple-overlap cocycle identity. The
   overlaps are open in each representative, being inverse images of open
   subschemes of S. Scheme gluing produces W and a map j:W to S. Its restriction
   over each U_s is the original immersion, so j is an immersion by target locality.
3. If g:T to S satisfies P, base-change stability gives P on the inverse-image
   cover of T. The local representing criteria give factors through W. These
   agree on overlaps by monomorphy of j and therefore glue to a global factor.
4. Conversely, given a factor through W, restrict to the inverse-image cover of
   T. On each member the local representing criterion gives P. Source locality
   then gives P globally. For empty S, glue the empty family; for empty T the
   source-locality hypothesis applied to its vacuous pointwise cover gives P. -/
theorem exists_localImmersionLocus (S : Scheme.{u})
    (P : ∀ {T : Scheme.{u}}, (T ⟶ S) → Prop)
    (hbase : ∀ {T T' : Scheme.{u}} (g : T ⟶ S) (h : T' ⟶ T), P g → P (h ≫ g))
    (hsource : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (∀ t : T, ∃ V : T.Opens, t ∈ V ∧ P (V.ι ≫ g)) → P g)
    (hlocal : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ (W : Scheme.{u}) (j : W ⟶ U.toScheme), IsImmersion j ∧
        ∀ {T : Scheme.{u}} (g : T ⟶ U.toScheme),
          (∃ h : T ⟶ W, h ≫ j = g) ↔ P (g ≫ U.ι)) :
    ∃ (W : Scheme.{u}) (j : W ⟶ S), IsImmersion j ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S), (∃ h : T ⟶ W, h ≫ j = g) ↔ P g := by
  classical
  choose U hs W j hj hrep using hlocal
  have hcompat : ∀ (i k : S) {T : Scheme.{u}}
      (a : T ⟶ (U i).toScheme) (b : T ⟶ (U k).toScheme),
      a ≫ (U i).ι = b ≫ (U k).ι →
      ((∃ h : T ⟶ W i, h ≫ j i = a) ↔ (∃ h : T ⟶ W k, h ≫ j k = b)) := by
    intro i k T a b hab
    rw [hrep i a, hrep k b, hab]
  obtain ⟨Z, q, hcharts⟩ :=
    exists_gluedCompatibleImmersionCharts S U W j hj hcompat
  choose e hp using hcharts
  let 𝒰 : S.OpenCover := {
    I₀ := S
    X i := (U i).toScheme
    f i := (U i).ι
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      exact ⟨fun i ↦ ⟨i, by simpa using hs i⟩, fun i ↦ inferInstance⟩ }
  have hq : IsImmersion q := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @IsImmersion) 𝒰
    intro i
    change IsImmersion (Limits.pullback.snd q (U i).ι)
    rw [← (hp i).flip.isoPullback_inv_snd]
    have : IsImmersion (j i) := hj i
    infer_instance
  have hqrep : ∀ (i : S) {T : Scheme.{u}} (a : T ⟶ (U i).toScheme),
      (∃ h : T ⟶ Z, h ≫ q = a ≫ (U i).ι) ↔
        (∃ h : T ⟶ W i, h ≫ j i = a) := by
    intro i T a
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨(hp i).lift a h hh.symm, (hp i).lift_fst a h hh.symm⟩
    · rintro ⟨h, hh⟩
      refine ⟨h ≫ e i, ?_⟩
      rw [Category.assoc, ← (hp i).w, ← Category.assoc, hh]
  refine ⟨Z, q, hq, ?_⟩
  intro T g
  constructor
  · rintro ⟨h, hh⟩
    apply hsource g
    intro t
    let i : S := g t
    let V : T.Opens := g ⁻¹ᵁ U i
    refine ⟨V, hs i, ?_⟩
    change P ((g ⁻¹ᵁ U i).ι ≫ g)
    rw [← morphismRestrict_ι]
    apply (hrep i (g ∣_ U i)).mp
    apply (hqrep i (g ∣_ U i)).mp
    refine ⟨V.ι ≫ h, ?_⟩
    rw [Category.assoc, hh, morphismRestrict_ι]
  · intro hg
    apply exists_factor_of_locally_factors q g
    intro t
    let i : S := g t
    let V : T.Opens := g ⁻¹ᵁ U i
    refine ⟨V, hs i, ?_⟩
    have hv : P ((g ∣_ U i) ≫ (U i).ι) := by
      rw [morphismRestrict_ι]
      exact hbase g V.ι hg
    obtain ⟨h, hh⟩ := (hqrep i (g ∣_ U i)).mpr ((hrep i (g ∣_ U i)).mpr hv)
    exact ⟨h, by simpa only [morphismRestrict_ι] using hh⟩

end AlgebraicGeometry.Scheme
