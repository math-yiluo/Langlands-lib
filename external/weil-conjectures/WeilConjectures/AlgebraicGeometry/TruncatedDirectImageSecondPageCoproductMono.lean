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
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Classical in
private theorem td_module_sum_mono {R : Type u} [Ring R] (I : Type u)
    (M : I → ModuleCat.{u} R) (N : ModuleCat.{u} R)
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
private theorem td_presheaf_sum_mono {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) (I : Type u)
    (M : I → PresheafOfModules.{u} R) (N : PresheafOfModules.{u} R)
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
    td_module_sum_mono I (fun i ↦ F.obj (M i)) (F.obj N)
      (fun i ↦ F.map (u i)) (fun i ↦ F.map (r i)) hh
  have heq : F.map (Sigma.desc u) = inv (sigmaComparison F M) ≫
      Sigma.desc (fun i ↦ F.map (u i)) := by
    rw [← sigmaComparison_map_desc, IsIso.inv_hom_id_assoc]
  have : Mono (F.map (Sigma.desc u)) := by
    rw [heq]
    infer_instance
  exact (ModuleCat.mono_iff_injective _).1 this

open Classical in
private theorem td_sheaf_sum_mono (Y : Scheme.{u}) (I : Type u)
    (M : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (N : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (u : ∀ i, M i ⟶ N) (r : ∀ i, N ⟶ M i)
    (h : ∀ i j, u j ≫ r i = if e : j = i then eqToHom (congrArg M e) else 0) :
    Mono (Sigma.desc u) := by
  let R := moduleRings Y.toRingedSpace
  let L := PresheafOfModules.sheafification.{u} (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
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
    td_presheaf_sum_mono R.obj I P (G.obj N)
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

/-- The second-page coproduct comparison is a monomorphism.
Source: Stacks Project, Tag 08DZ, second-page direct-sum reduction; Tag 009E (5),
identification of stalks of direct sums. This is the injectivity half only.
(blueprint: lem-pc-truncated-direct-image-second-page-coproduct-mono).

Proof: Let F be the composite of lower truncation at a, cohomology in degree r,
and the higher-direct-image functor in degree p. These functors are additive:
truncation and cohomology are additive, as are singleFunctor, derived direct image,
and its cohomology. For each i the universal property hc defines a projection
pi_i : S -> E_i which is identity on the i-th summand and zero on all other
summands. Thus F(pi_i) composed with the comparison phi is the i-th projection
from the sheaf coproduct of the F(E_j), by functoriality and preservation of zero.
At every point y of Y, the stalk of that coproduct is the algebraic direct sum
of the stalk modules, with its canonical injections. If phi_y sends a vector
to zero, applying the stalk map of every F(pi_i) makes each component of that
vector zero. A direct-sum vector is determined by its components, so phi_y is
injective. A morphism of module sheaves whose maps on all stalks are injective
is monic: two sections with the same image have equal germs everywhere, hence
are equal by the sheaf separation axiom. Therefore phi is monic. This argument
needs neither quasi-coherence nor the qcqs hypotheses. For the empty family
the source is the zero sheaf, so its map to F(S) is automatically monic; for a
singleton it is the image under F of an isomorphism. It also applies when r < a,
when all cohomology sheaves in question are zero. -/
theorem truncated_directImage_secondPage_coproduct_mono
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (I : Type u) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (a : ℤ) (p : ℕ) (r : ℤ) :
    Mono (Sigma.desc (fun i ↦ (schemeModuleHigherDirectImage f (p : ℤ)).map
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).map
          ((DerivedCategory.TStructure.t.truncGE a).map (ι i))))) := by
  classical
  let H := DerivedCategory.TStructure.t.truncGE a ⋙
    DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r ⋙
    schemeModuleHigherDirectImage f (p : ℤ)
  let _ : H.Additive := by
    dsimp [H, schemeModuleHigherDirectImage, schemeHigherDirectImage, schemeDerivedDirectImage]
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
  exact td_sheaf_sum_mono Y I (fun i ↦ H.obj (A i)) (H.obj S)
    (fun i ↦ H.map (ι i)) (fun i ↦ H.map (π i)) hh

end AlgebraicGeometry
