/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import WeilConjectures.AlgebraicGeometry.TruncatedDirectImageAffineFiniteSupport
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # The uniformly lower-truncated coproduct comparison

Source: Stacks Project, Tags 08DZ and 015J
(blueprint: lem-pc-derived-direct-image-truncated-coproduct).
-/

@[expose] public section

universe u₁ w₁ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open Classical in
private theorem module_sum_mono {R : Type u₁} [Ring R] (I : Type u₁)
    (M : I → ModuleCat.{u₁} R) (N : ModuleCat.{u₁} R)
    (u : ∀ i, M i ⟶ N) (r : ∀ i, N ⟶ M i)
    (h : ∀ i j, u j ≫ r i = if e : j = i then eqToHom (congrArg M e) else 0) :
    Mono (Sigma.desc u) := by
  classical
  let φ := DirectSum.toModule R I N (fun i ↦ (u i).hom)
  have hcomp (i : I) : (r i).hom.comp φ =
      DirectSum.component R I (fun i ↦ ↥(M i)) i := by
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, φ, DirectSum.toModule_lof]
    change (u j ≫ r i).hom x = _
    rw [h]
    by_cases e : j = i
    · subst j
      simp
    · simp [e, DirectSum.component.of]
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply DirectSum.ext_component R
    intro i
    rw [← hcomp i]
    exact congrArg (r i).hom hxy
  have : Mono (ModuleCat.ofHom φ) := (ModuleCat.mono_iff_injective _).2 hφ
  have heq : Sigma.desc u = (ModuleCat.coprodIsoDirectSum M).hom ≫
      ModuleCat.ofHom φ := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc, ← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom]
    ext x
    simp [φ]
  rw [heq]
  infer_instance

open Classical in
private theorem presheaf_sum_mono {C : Type u₁} [Category.{u₁} C]
    (R : Cᵒᵖ ⥤ RingCat.{u₁}) (I : Type u₁)
    (M : I → PresheafOfModules.{u₁} R) (N : PresheafOfModules.{u₁} R)
    (u : ∀ i, M i ⟶ N) (r : ∀ i, N ⟶ M i)
    (h : ∀ i j, u j ≫ r i = if e : j = i then eqToHom (congrArg M e) else 0) :
    Mono (Sigma.desc u) := by
  apply PresheafOfModules.mono_of_injective
  intro V
  let F := PresheafOfModules.evaluation R V
  have hh (i j : I) : F.map (u j) ≫ F.map (r i) =
      if e : j = i then eqToHom (congrArg (fun j ↦ F.obj (M j)) e) else 0 := by
    rw [← F.map_comp, h]
    by_cases e : j = i
    · subst j
      simp
    · simp [e]
  have hm : Mono (Sigma.desc (fun i ↦ F.map (u i))) :=
    module_sum_mono I (fun i ↦ F.obj (M i)) (F.obj N)
      (fun i ↦ F.map (u i)) (fun i ↦ F.map (r i)) hh
  have heq : F.map (Sigma.desc u) = inv (sigmaComparison F M) ≫
      Sigma.desc (fun i ↦ F.map (u i)) := by
    rw [← sigmaComparison_map_desc, IsIso.inv_hom_id_assoc]
  have : Mono (F.map (Sigma.desc u)) := by
    rw [heq]
    infer_instance
  exact (ModuleCat.mono_iff_injective _).1 this

open Classical in
private theorem sheaf_sum_mono (Y : Scheme.{u₁}) (I : Type u₁)
    (M : I → SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))
    (N : SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))
    (u : ∀ i, M i ⟶ N) (r : ∀ i, N ⟶ M i)
    (h : ∀ i j, u j ≫ r i = if e : j = i then eqToHom (congrArg M e) else 0) :
    Mono (Sigma.desc u) := by
  let R := moduleRings Y.toRingedSpace
  let L := PresheafOfModules.sheafification.{u₁} (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u₁} (𝟙 R.obj)
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let P := fun i ↦ G.obj (M i)
  have hh (i j : I) : G.map (u j) ≫ G.map (r i) =
      if e : j = i then eqToHom (congrArg P e) else 0 := by
    rw [← G.map_comp, h]
    by_cases e : j = i
    · subst j
      simp [P]
    · simp only [dite_eq_right e]
      ext V x
      rfl
  have hm : Mono (Sigma.desc (fun i ↦ G.map (u i))) :=
    presheaf_sum_mono R.obj I P (G.obj N)
      (fun i ↦ G.map (u i)) (fun i ↦ G.map (r i)) hh
  let b := Sigma.desc (fun i ↦ inv (adj.counit.app (M i)) ≫ L.map (Sigma.ι P i))
  have hb : IsIso b := by
    have heq : b = Limits.Sigma.map (fun i ↦ inv (adj.counit.app (M i))) ≫
        sigmaComparison L P := by
      apply Sigma.hom_ext
      intro i
      dsimp only [b]
      rw [Sigma.ι_comp_desc, Sigma.ι_map_assoc]
      change inv (adj.counit.app (M i)) ≫ L.map (Sigma.ι P i) =
        inv (adj.counit.app (M i)) ≫ Sigma.ι (fun i ↦ L.obj (P i)) i ≫ _
      rw [ι_comp_sigmaComparison]
    rw [heq]
    infer_instance
  let d := L.map (Sigma.desc (fun i ↦ G.map (u i))) ≫ adj.counit.app N
  have hd : Mono d := by
    dsimp [d]
    infer_instance
  have heq : Sigma.desc u = b ≫ d := by
    apply Sigma.hom_ext
    intro i
    simp only [b, d, Sigma.ι_comp_desc_assoc, Category.assoc]
    rw [← L.map_comp_assoc]
    rw [show Sigma.ι P i ≫ Sigma.desc (fun i ↦ G.map (u i)) = G.map (u i) from
      Sigma.ι_comp_desc _ _]
    have hnat : L.map (G.map (u i)) ≫ adj.counit.app N =
        adj.counit.app (M i) ≫ u i := adj.counit.naturality (u i)
    rw [hnat, IsIso.inv_hom_id_assoc, Sigma.ι_comp_desc]
  rw [heq]
  infer_instance

/-- After a single common lower truncation, derived direct-image cohomology commutes
with an ambient coproduct of objects with quasi-coherent cohomology.
Source: Stacks Project, Tag 08DZ, bounded-below comparison, and Tag 015J
(blueprint: lem-pc-derived-direct-image-truncated-coproduct).

Proof. Exact sums in module sheaves identify the cohomology of the ambient coproduct
with the sums of the summands' cohomology. Quasi-coherence is preserved by sums:
write the sum as the directed colimit of finite sums, including the empty finite sum,
and use the affine-section colimit theorem. Exact sums also commute with the canonical
lower truncation. Hence the truncated cofan is a coproduct with quasi-coherent cohomology
and common lower bound a. Apply the natural truncation hypercohomology spectral sequence
for direct image to this cofan. Its E₂ terms are R^p f_* H^r. On affine opens of Y,
their presheaf descriptions are cohomology on qcqs inverse images. Qcqs cohomology
commutes with sums; sheafification of module presheaves preserves sums. Thus the E₂
comparison is an isomorphism. Exact sums commute with the kernels and images defining
successive pages, so all page comparisons are isomorphisms. In degree q the range
0 ≤ p ≤ q-a is finite. The convergent filtrations therefore have isomorphic graded
pieces; induction on their short exact sequences makes the abutment comparison an
isomorphism. Naturality identifies it with the displayed map. For q<a the abutments
vanish, and the empty family is covered by exactness and the zero coproduct. -/
theorem derivedDirectImage_truncated_cohomology_coproduct
    {X Y : Scheme.{u₁}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (I : Type u₁) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (a q : ℤ) :
    IsIso (Sigma.desc (fun i ↦ (schemeHigherDirectImage f q).map
      ((DerivedCategory.TStructure.t.truncGE a).map (ι i)))) := by
  classical
  let H := DerivedCategory.TStructure.t.truncGE a ⋙ schemeHigherDirectImage f q
  have : H.Additive := by
    dsimp [H, schemeHigherDirectImage, schemeDerivedDirectImage]
    infer_instance
  let A := fun i ↦ (E i).obj
  let π (i : I) : S ⟶ A i := Cofan.IsColimit.desc hc
    (fun j ↦ if e : j = i then eqToHom (congrArg A e) else 0)
  have hπ (i j : I) : ι j ≫ π i =
      if e : j = i then eqToHom (congrArg A e) else 0 :=
    Cofan.IsColimit.fac hc _ j
  have hh (i j : I) : H.map (ι j) ≫ H.map (π i) =
      if e : j = i then eqToHom (congrArg (fun j ↦ H.obj (A j)) e) else 0 := by
    rw [← H.map_comp, hπ]
    by_cases e : j = i
    · subst j
      simp only [eqToHom_refl]
      exact H.map_id _
    · simp [e]
  have hm : Mono (Sigma.desc (fun i ↦ H.map (ι i))) :=
    sheaf_sum_mono Y I (fun i ↦ H.obj (A i)) (H.obj S)
      (fun i ↦ H.map (ι i)) (fun i ↦ H.map (π i)) hh
  let c := Sigma.desc (fun i ↦ H.map (ι i))
  have hlocal (U : Y.Opens) (hU : IsAffineOpen U) :
      IsIso ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op U)).map c) := by
    let ev := SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op U)
    let R := (moduleRings Y.toRingedSpace).obj.obj (op U)
    let M := fun i ↦ ev.obj (H.obj (A i))
    let φ := DirectSum.toModule R I (ev.obj (H.obj S))
      (fun i ↦ (ev.map (H.map (ι i))).hom)
    have hs : Function.Surjective φ :=
      truncated_directImage_affine_finiteSupport f I E S ι hc a q U hU
    let l := DirectSum.toModule R I (ev.obj (∐ (fun i ↦ H.obj (A i))))
      (fun i ↦ (ev.map (Sigma.ι (fun i ↦ H.obj (A i)) i)).hom)
    have heq : (ev.map c).hom.comp l = φ := by
      apply DirectSum.linearMap_ext
      intro i
      ext x
      dsimp only [l, φ, R, M, LinearMap.comp_apply]
      rw [DirectSum.toModule_lof, DirectSum.toModule_lof]
      change (ev.map (Sigma.ι (fun i ↦ H.obj (A i)) i) ≫ ev.map c).hom x = _
      rw [← ev.map_comp]
      rw [show Sigma.ι (fun i ↦ H.obj (A i)) i ≫ c = H.map (ι i) from
        Sigma.ι_comp_desc _ _]
    have he : Epi (ev.map c) := (ModuleCat.epi_iff_surjective _).2 (by
      intro x
      obtain ⟨y, hy⟩ := hs x
      exact ⟨l y, (LinearMap.congr_fun heq y).trans hy⟩)
    have : Mono (ev.map c) := inferInstance
    exact isIso_of_mono_of_epi _
  have hB : TopologicalSpace.Opens.IsBasis
      (Set.range (fun U : Y.affineOpens ↦ (U : Y.Opens))) := by
    rw [Subtype.range_coe]
    exact Y.isBasis_affineOpens
  have hforget : IsIso ((SheafOfModules.toSheaf
      (moduleRings Y.toRingedSpace)).map c) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis hB
    intro U
    have : IsIso ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace)
        (op (U : Y.Opens))).map c) := hlocal U U.2
    exact inferInstanceAs (IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map
      ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace)
        (op (U : Y.Opens))).map c)))
  exact isIso_of_reflects_iso c (SheafOfModules.toSheaf (moduleRings Y.toRingedSpace))

end AlgebraicGeometry
