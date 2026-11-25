/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.ProjectiveFiniteSourceCohomologySegment
import WeilConjectures.AlgebraicGeometry.AlternatingCechComputes
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Projective cohomology finiteness over an affine base

Source: Stacks Project, Tag 01YS, Lemma 30.14.1 (3).
(blueprint: lem-pc-m1-projective-affine-finite-cohomology-independent)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

private def opensSiteCech (X : Scheme.{u}) {n : Type u} (U : n → X.Opens) :
    SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)) where
  W p t := ⨅ k, U (t k)
  pr p t k := homOfLE (iInf_le _ k)
  comm _ _ _ := Subsingleton.elim _ _
  universal p t Z a _ := by
    refine ⟨homOfLE (le_iInf fun k ↦ (a k).le), ?_, ?_⟩
    · intro k
      apply Subsingleton.elim
    · intro b _
      apply Subsingleton.elim
  W_zero t := by simp
  pr_zero _ := Subsingleton.elim _ _
  indexMap t α := homOfLE (le_iInf fun k ↦ iInf_le _ (α k))
  indexMap_pr _ _ _ := Subsingleton.elim _ _

private noncomputable def opensSiteCechIso (X : Scheme.{u}) {n : Type u} (U : n → X.Opens)
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (opensSiteCech X U).complex F ≅ (TopCat.Presheaf.cechComplex U).obj F :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro p q hpq
    obtain rfl : p + 1 = q := hpq
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply AddCommGrpCat.ext
    intro s
    funext t
    rw [TopCat.Presheaf.cechComplex_d_apply]
    simp only [SiteCechComplex.complex, CochainComplex.of_d]
    rfl)

private theorem projective_cohomology_bound {T : Scheme.{u}} [IsAffine T]
    (n : Type u) [Finite n] (ℱ : (ℙ(n; T)).Modules) [ℱ.IsQuasicoherent]
    {q : ℕ} (hq : Nat.card n ≤ q) : Subsingleton (ℱ.H q) := by
  classical
  have := Fintype.ofFinite n
  let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  let U := ProjectiveSpace.standardOpen n (T)
  let P := ℱ.presheafModuleCat ⋙ forget₂ (ModuleCat Γ(ℙ(n; T), ⊤)) AddCommGrpCat
  obtain ⟨K, e, r, -, -, hr⟩ := Scheme.alternatingCechComputes
    (ℙ(n; T)) U (ProjectiveSpace.iSup_standardOpen n _) P
      (opensSiteCech _ U)
  have hempty : IsEmpty {t : Fin (q + 1) → n // StrictMono t} := by
    refine ⟨fun t ↦ ?_⟩
    have hc := Fintype.card_le_of_injective t.1 t.2.injective
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card] at hc
    omega
  have hz : Limits.IsZero (K.X q) := by
    exact ((AddCommGrpCat.isZero_iff_subsingleton).mpr inferInstance).of_iso (e q)
  have hh : Limits.IsZero (K.homology q) :=
    ShortComplex.isZero_homology_of_isZero_X₂ (K.sc q) hz
  have := hr q
  have hz' : Limits.IsZero (((opensSiteCech _ U).complex P).homology q) :=
    hh.of_iso (asIso (HomologicalComplex.homologyMap r q))
  have hcech : Limits.IsZero (((TopCat.Presheaf.cechComplex U).obj P).homology q) :=
    hz'.of_iso (HomologicalComplex.homologyMapIso (opensSiteCechIso _ U P) q).symm
  let ec := TopCat.Presheaf.cechComplexFunctorHomologyIso U ℱ.presheafModuleCat q
  have : Subsingleton (((TopCat.Presheaf.cechComplex U).obj P).homology q) :=
    (AddCommGrpCat.isZero_iff_subsingleton).mp hcech
  have : Subsingleton (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :=
    ec.addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  obtain ⟨el⟩ := Scheme.Modules.nonempty_cechComplex_linearEquiv_H_of_isSeparated
    (ℙ(n; T) ↘ T) U
    (fun i ↦ ProjectiveSpace.isAffineOpen_standardOpen n _ i)
    (ProjectiveSpace.iSup_standardOpen n _) ℱ q
  exact el.symm.toEquiv.subsingleton

private theorem finite_of_exact_segment {R M L Q : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup L] [Module R L] [AddCommGroup Q] [Module R Q]
    [Module.Finite R M] [Module.Finite R Q]
    (a : M →ₗ[R] L) (b : L →ₗ[R] Q) (h : Function.Exact a b) :
    Module.Finite R L := by
  have : Module.Finite R (LinearMap.range b) := inferInstance
  apply Module.Finite.of_exact (f := a) (g := b.rangeRestrict)
    _ b.surjective_rangeRestrict
  intro x
  constructor
  · intro hx
    exact (h x).mp (congrArg Subtype.val hx)
  · intro hx
    apply Subtype.ext
    exact (h x).mpr hx

/-- Finiteness for an explicit projective model over an arbitrary affine Noetherian scheme.

Source: Stacks Project, Tag 01YS, Lemma 30.14.1 (3), and Tag 01Y6, Lemma 30.9.9.
(blueprint: lem-pc-m1-projective-affine-finite-cohomology-independent)

Proof: identify T with Spec Gamma(T,O) by its affine canonical isomorphism, and base
change the specified embedding along this isomorphism. Closed pushforward of F is
quasi-coherent and finitely presented on the Noetherian projective space, and has the
same cohomology. On projective space, the standard coordinate affine cover bounds the
cohomological degree. Descending induction on degree, simultaneously for all coherent
modules, uses a surjection from a finite sum of twists with coherent kernel. The twists
have finite cohomology by the explicit standard-cover calculation; the long exact
sequence and Noetherian submodule finiteness give finiteness for F. All comparisons
are natural under multiplication by sections of T, hence linear for the displayed
restriction-of-scalars action. If N is empty, Y is empty and all groups are zero.
No use is made of proper coherence. -/
theorem finite_H_projective_affine_independent
    {Y T : Scheme.{u}} [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (N : Type u) [Finite N] (j : Y ⟶ ℙ(N; T)) [IsClosedImmersion j]
    (F : Y.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (q : ℕ) :
    letI : Module Γ(T, ⊤) (F.H q) :=
      Module.compHom _ (j ≫ (ℙ(N; T) ↘ T)).appTop.hom
    Module.Finite Γ(T, ⊤) (F.H q) := by
  classical
  let P := ℙ(N; T)
  let FiniteAt (r : ℕ) : Prop := ∀ (G : P.Modules)
    [G.IsQuasicoherent] [G.IsFinitePresentation],
    let : Module Γ(T, ⊤) (G.H r) := Module.compHom _ (P ↘ T).appTop.hom
    Module.Finite Γ(T, ⊤) (G.H r)
  have high (r : ℕ) (hr : Nat.card N ≤ r) : FiniteAt r := by
    intro G _ _
    let : Module Γ(T, ⊤) (G.H r) := Module.compHom _ (P ↘ T).appTop.hom
    have : Subsingleton (G.H r) := projective_cohomology_bound N G hr
    infer_instance
  have step (r : ℕ) (ih : FiniteAt (r + 1)) : FiniteAt r := by
    intro G _ _
    obtain ⟨K, hKq, hKf, V, hV, a, b, hab⟩ :=
      exists_projective_finite_source_cohomology_segment N (𝟙 P) G r
    let := hKq
    let := hKf
    let : Module Γ(T, ⊤) (G.H r) := Module.compHom _ (P ↘ T).appTop.hom
    let : Module Γ(T, ⊤) (K.H (r + 1)) := Module.compHom _ (P ↘ T).appTop.hom
    let := hV
    have : Module.Finite Γ(T, ⊤) (K.H (r + 1)) := ih K
    exact finite_of_exact_segment a b hab
  have all (r : ℕ) : FiniteAt r := by
    by_cases hr : Nat.card N ≤ r
    · exact high r hr
    · exact Nat.decreasingInduction' (fun k _ _ ih ↦ step k ih)
        (Nat.le_of_lt (Nat.lt_of_not_ge hr)) (high (Nat.card N) le_rfl)
  obtain ⟨K, hKq, hKf, V, hV, a, b, hab⟩ :=
    exists_projective_finite_source_cohomology_segment N j F q
  let := hKq
  let := hKf
  let : Module Γ(T, ⊤) (F.H q) :=
    Module.compHom _ (j ≫ (P ↘ T)).appTop.hom
  let : Module Γ(T, ⊤) (K.H (q + 1)) := Module.compHom _ (P ↘ T).appTop.hom
  let := hV
  have : Module.Finite Γ(T, ⊤) (K.H (q + 1)) := all (q + 1) K
  exact finite_of_exact_segment a b hab

end AlgebraicGeometry.Scheme.Modules
