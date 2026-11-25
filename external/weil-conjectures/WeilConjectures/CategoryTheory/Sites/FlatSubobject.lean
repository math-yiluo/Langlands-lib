/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.DedekindDomain.PID

/-!
# Subsheaves of flat sheaves over a principal ideal domain

Let `R` be a principal ideal domain. A sheaf of `R`-modules all of whose modules of sections
are flat has locally trivial relations, hence is flat
(`CategoryTheory.Presheaf.hasLocallyTrivialRelations_of_flat`). The sections of a flat sheaf
are torsion free (`CategoryTheory.Sheaf.smul_eq_zero_of_flat`), so the sections of a subsheaf of
a flat sheaf are torsion free modules over a principal ideal domain, hence flat: a subsheaf of a
flat sheaf is flat (`CategoryTheory.Sheaf.flat_of_mono`). This is the sheaf form of the fact that
`R` has weak global dimension at most one.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]

omit [EssentiallySmall.{u + 1} C] [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)] in
/-- Two sections of a sheaf of modules which agree locally, on a covering sieve, are equal. -/
lemma Sheaf.eq_of_forall_map_eq {F : Sheaf J (ModuleCat.{u + 1} R)} {V : C}
    {x y : F.obj.obj (op V)} {T : Sieve V} (hT : T ∈ J V)
    (h : ∀ ⦃W : C⦄ (f : W ⟶ V), T f → F.obj.map f.op x = F.obj.map f.op y) : x = y := by
  have hF : Presheaf.IsSheaf J (F.obj ⋙ forget (ModuleCat.{u + 1} R)) :=
    ((sheafCompose J (forget (ModuleCat.{u + 1} R))).obj F).property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact (hF T hT).isSeparatedFor.ext fun W f hf ↦ h f hf

/-- The sections of a flat sheaf of modules over a noetherian domain are torsion free: a
section killed by a nonzero `r` is, locally, a combination of sections with coefficients killed
by `r` (`CategoryTheory.Sheaf.hasLocallyTrivialRelations_of_flat`), hence locally zero. -/
lemma Sheaf.smul_eq_zero_of_flat [IsNoetherianRing R] [IsDomain R]
    {F : Sheaf J (ModuleCat.{u + 1} R)} (hF : ObjectProperty.flat F) {r : R} (hr : r ≠ 0)
    {V : C} {x : F.obj.obj (op V)} (hx : r • x = 0) : x = 0 := by
  obtain ⟨T, hT, hfac⟩ := Sheaf.hasLocallyTrivialRelations_of_flat hF (V := V) (s := 1) (q := 1)
    (fun _ ↦ x) (Matrix.of fun _ _ ↦ r) (fun _ ↦ by simpa using hx)
  refine Sheaf.eq_of_forall_map_eq hT fun W f hf ↦ ?_
  obtain ⟨t, b, z, heb, hyz⟩ := hfac f hf
  have hb (m : Fin t) : b 0 m = 0 := by
    have := congrFun (congrFun heb 0) m
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton, Matrix.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hr
  rw [hyz 0, map_zero]
  simp [hb]

omit [EssentiallySmall.{u + 1} C] [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)] in
/-- A presheaf of modules whose modules of sections are all flat has (globally, hence locally)
trivial relations, by the equational criterion for flatness
(`Module.Flat.exists_factorization_of_comp_eq_zero_of_free`). -/
lemma Presheaf.hasLocallyTrivialRelations_of_flat {P : Cᵒᵖ ⥤ ModuleCat.{u + 1} R}
    (hP : ∀ V : C, Module.Flat R (P.obj (op V))) : Presheaf.HasLocallyTrivialRelations J P := by
  intro V s q y e he
  classical
  refine ⟨⊤, J.top_mem V, fun W f _ ↦ ?_⟩
  let x : (Fin s →₀ R) →ₗ[R] P.obj (op V) := Finsupp.linearCombination R y
  let g : (Fin q →₀ R) →ₗ[R] (Fin s →₀ R) :=
    Finsupp.linearCombination R fun l ↦ Finsupp.equivFunOnFinite.symm (e l)
  have hxg : x ∘ₗ g = 0 := by
    refine Finsupp.lhom_ext' fun l ↦ LinearMap.ext_ring ?_
    simp [x, g, Finsupp.linearCombination_apply, Finsupp.sum_fintype, he]
  obtain ⟨k, a, z, hxa, hag⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxg
  have ha (j : Fin s) (c : R) : a (Finsupp.single j c) = c • a (Finsupp.single j 1) := by
    rw [← map_smul, Finsupp.smul_single_one]
  refine ⟨k, Matrix.of fun j m ↦ a (Finsupp.single j 1) m,
    fun m ↦ P.map f.op (z (Finsupp.single m 1)), ?_, fun j ↦ ?_⟩
  · ext l m
    have := congrArg (fun w ↦ w m) (LinearMap.congr_fun hag (Finsupp.single l 1))
    simp only [Finsupp.equivFunOnFinite_symm_eq_sum, LinearMap.coe_comp, Function.comp_apply,
      Finsupp.linearCombination_single, one_smul, map_sum, Finsupp.coe_finsetSum,
      Finset.sum_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply, g] at this
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [ha c (e l c), Finsupp.smul_apply, smul_eq_mul]
  · have h1 : y j = z (a (Finsupp.single j 1)) := by
      rw [← LinearMap.comp_apply, ← hxa]
      simp [x]
    have h2 : a (Finsupp.single j 1) =
        ∑ m, a (Finsupp.single j 1) m • Finsupp.single m (1 : R) := by
      conv_lhs => rw [← Finsupp.univ_sum_single (a (Finsupp.single j 1))]
      simp
    rw [h1, h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [map_smul, map_smul]
    rfl

/-- Over a principal ideal domain, a subsheaf of a flat sheaf of modules is flat: its sections
are torsion free, being submodules of the torsion free sections of the flat sheaf, hence flat. -/
theorem Sheaf.flat_of_mono [IsDomain R] [IsPrincipalIdealRing R]
    {G F : Sheaf J (ModuleCat.{u + 1} R)} (i : G ⟶ F) [Mono i] (hF : ObjectProperty.flat F) :
    ObjectProperty.flat G := by
  have hi (V : C) : Function.Injective (i.hom.app (op V)) := by
    have : Mono i.hom := (sheafToPresheaf J _).map_mono i
    rw [← ModuleCat.mono_iff_injective]
    infer_instance
  have hG (V : C) : Module.Flat R (G.obj.obj (op V)) := by
    have : Module.IsTorsionFree R (G.obj.obj (op V)) := by
      refine ⟨fun r hr x y hxy ↦ ?_⟩
      have hr0 : r ≠ 0 := hr.ne_zero
      refine hi V (sub_eq_zero.1 (Sheaf.smul_eq_zero_of_flat hF hr0 ?_))
      rw [smul_sub, ← map_smul, ← map_smul, sub_eq_zero]
      exact congrArg _ hxy
    infer_instance
  rw [Sheaf.flat_iff_hasLocallyTrivialRelations]
  exact Presheaf.hasLocallyTrivialRelations_of_flat hG

end CategoryTheory
