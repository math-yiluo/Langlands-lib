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

public import Mathlib.Algebra.DirectSum.Module

import WeilConjectures.AlgebraicGeometry.TruncatedDirectImageSheafCoproductEpi
import WeilConjectures.AlgebraicGeometry.TruncatedHigherImagesAffineCoproduct
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Finite-support representatives of truncated direct-image cohomology

Source: Stacks Project, Tags 08DZ and 015J
(blueprint: lem-pc-truncated-direct-image-affine-finite-support).
-/

@[expose] public section

universe u₁ w₁ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

-- The concrete projection argument elaborates sheafification and both evaluation functors.
open Classical in
/-- On an affine open, every section of truncated direct-image cohomology of an
ambient coproduct comes from finitely many summands.
Source: Stacks Project, Tag 08DZ, bounded-below spectral-sequence argument, and Tag 015J
(blueprint: lem-pc-truncated-direct-image-affine-finite-support).

Proof. Choose termwise representatives of the ambient coproduct. Exact sums compute
its cohomology as the sum of the summands' cohomology, and these sums are quasi-coherent.
Exact sums commute with lower truncation, so the truncated family and its coproduct
have the common lower bound a. Over an affine open U of Y, the inverse image is qcqs.
The natural bounded-below hypercohomology spectral sequences have second pages
H^p(f⁻¹U,H^r(τ≥a E)). Cohomology of module sheaves on this qcqs inverse image commutes
with sums. Thus the second-page comparison is bijective. Exact sums commute with the
kernels and images of differentials, so all page comparisons are bijective. In total
degree q there are only the finitely many indices 0 ≤ p ≤ q-a. The finite convergent
filtrations therefore give surjectivity on the abutment: lift a section of the top
nonzero graded piece, subtract its image, and repeat in the next filtration step.
Each lift has finite support; the union of the finitely many supports is finite.
To justify quasi-coherence of the second-page terms, on an affine open V of Y
localize at a section t of O_Y(V). Cohomology of a quasi-coherent module on the qcqs
preimage of V commutes with localization at f*t: prove this from affine acyclicity
and localization of sections, then glue finite affine covers by Mayer--Vietoris,
using quasi-separatedness for quasi-compact overlaps. The resulting identifications
are compatible with restriction to principal opens of V. The higher-direct-image
presheaf description therefore gives quasi-coherent second-page sheaves.
Kernel and cokernel closure propagate quasi-coherence to all later pages. The finite
convergent filtration expresses the abutment as successive extensions of these
quasi-coherent stable page terms, starting at zero, so its cohomology is quasi-coherent.
Consequently, exact sections on the affine open U identify the sheaf abutments with
the displayed section modules. Naturality identifies the map with the displayed
linear map. If q<a the target is zero. If I is empty the ambient coproduct and its
lower truncation are zero, so the target is zero as well. -/
theorem truncated_directImage_affine_finiteSupport
    {X Y : Scheme.{u₁}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (I : Type u₁) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (a q : ℤ) (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Surjective
      (DirectSum.toModule ((moduleRings Y.toRingedSpace).obj.obj (op U)) I
        (((SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op U)).obj
          ((schemeHigherDirectImage f q).obj
            ((DerivedCategory.TStructure.t.truncGE a).obj S))))
        (fun i ↦ ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op U)).map
          ((schemeHigherDirectImage f q).map
            ((DerivedCategory.TStructure.t.truncGE a).map (ι i)))).hom)) := by
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
  have hm : Mono (Sigma.desc (fun i ↦ H.map (ι i))) := by
    let M := fun i ↦ H.obj (A i)
    let N := H.obj S
    let u (i : I) : M i ⟶ N := H.map (ι i)
    let r (i : I) : N ⟶ M i := H.map (π i)
    let R := moduleRings Y.toRingedSpace
    let L := PresheafOfModules.sheafification.{u₁} (𝟙 R.obj)
    let adj := PresheafOfModules.sheafificationAdjunction.{u₁} (𝟙 R.obj)
    let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
    let P := fun i ↦ G.obj (M i)
    have hh (i j : I) : G.map (u j) ≫ G.map (r i) =
        if e : j = i then eqToHom (congrArg P e) else 0 := by
      rw [← G.map_comp, hh]
      by_cases e : j = i
      · subst j
        simp [P, M]
      · simp only [dite_eq_right e]
        ext V x
        rfl
    have hm : Mono (Sigma.desc (fun i ↦ G.map (u i))) := by
      let M' := P
      let N' := G.obj N
      let u' (i : I) : M' i ⟶ N' := G.map (u i)
      let r' (i : I) : N' ⟶ M' i := G.map (r i)
      apply PresheafOfModules.mono_of_injective
      intro V
      let F := PresheafOfModules.evaluation R.obj V
      have hh (i j : I) : F.map (u' j) ≫ F.map (r' i) =
          if e : j = i then eqToHom (congrArg (fun j ↦ F.obj (M' j)) e) else 0 := by
        rw [← F.map_comp, hh]
        by_cases e : j = i
        · subst j
          simp [M', P]
        · simp [e]
      have hm : Mono (Sigma.desc (fun i ↦ F.map (u' i))) := by
        let M'' := fun i ↦ F.obj (M' i)
        let N'' := F.obj N'
        let u'' (i : I) : M'' i ⟶ N'' := F.map (u' i)
        let r'' (i : I) : N'' ⟶ M'' i := F.map (r' i)
        classical
        let φ := DirectSum.toModule (R.obj.obj V) I N'' (fun i ↦ (u'' i).hom)
        have hcomp (i : I) : (r'' i).hom.comp φ =
            DirectSum.component (R.obj.obj V) I (fun i ↦ ↥(M'' i)) i := by
          apply DirectSum.linearMap_ext
          intro j
          apply LinearMap.ext
          intro x
          simp only [LinearMap.comp_apply, φ, DirectSum.toModule_lof]
          change (u'' j ≫ r'' i).hom x = _
          rw [hh]
          by_cases e : j = i
          · subst j
            simp only [eqToHom_refl, DirectSum.component.of]
            change (ModuleCat.Hom.hom (𝟙 (M'' i))) x = x
            rfl
          · simp [e, DirectSum.component.of]
        have hφ : Function.Injective φ := by
          intro x y hxy
          apply DirectSum.ext_component (R.obj.obj V)
          intro i
          rw [← hcomp i]
          exact congrArg (r'' i).hom hxy
        have : Mono (ModuleCat.ofHom φ) := (ModuleCat.mono_iff_injective _).2 hφ
        have heq : Sigma.desc u'' = (ModuleCat.coprodIsoDirectSum M'').hom ≫
            ModuleCat.ofHom φ := by
          apply Sigma.hom_ext
          intro i
          rw [Sigma.ι_comp_desc, ← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom]
          ext x
          simp [φ]
        rw [heq]
        infer_instance
      have heq : F.map (Sigma.desc u') = inv (sigmaComparison F M') ≫
          Sigma.desc (fun i ↦ F.map (u' i)) := by
        rw [← sigmaComparison_map_desc F M' N' u', IsIso.inv_hom_id_assoc]
      have : Mono (F.map (Sigma.desc u')) := by
        rw [heq]
        infer_instance
      exact (ModuleCat.mono_iff_injective _).1 this
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
  let c := Sigma.desc (fun i ↦ H.map (ι i))
  have he : Epi (Sigma.desc (fun i ↦ H.map (ι i))) :=
    truncated_directImage_sheaf_coproduct_epi f I E S ι hc a q
  have hi : IsIso (Sigma.desc (fun i ↦ H.map (ι i))) := isIso_of_mono_of_epi _
  let ev := SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op U)
  let M := fun i ↦ H.obj (A i)
  obtain ⟨hev⟩ := truncated_higherImages_affine_coproduct f I E a q U hU
  let hev' := (isColimitMapCoconeCofanMkEquiv ev M (Sigma.ι M)) hev
  let d := Cofan.IsColimit.desc hev' (fun i ↦ Sigma.ι (fun i ↦ ev.obj (M i)) i)
  have hd (i : I) : ev.map (Sigma.ι M i) ≫ d =
      Sigma.ι (fun i ↦ ev.obj (M i)) i := Cofan.IsColimit.fac hev' _ i
  let R := (moduleRings Y.toRingedSpace).obj.obj (op U)
  let l := DirectSum.toModule R I (ev.obj (∐ M))
    (fun i ↦ (ev.map (Sigma.ι M i)).hom)
  have hl : Function.Surjective l := by
    let e := ModuleCat.coprodIsoDirectSum (fun i ↦ ev.obj (M i))
    let k := e.hom ≫ ModuleCat.ofHom l
    have hk : k ≫ d = 𝟙 _ := by
      apply Sigma.hom_ext
      intro i
      dsimp only [k, e]
      simp only [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom]
      rw [Category.assoc]
      change ModuleCat.ofHom (DirectSum.lof R I (fun i ↦ ↥(ev.obj (M i))) i) ≫
        ModuleCat.ofHom l ≫ d = _
      have hleg : ModuleCat.ofHom (DirectSum.lof R I (fun i ↦ ↥(ev.obj (M i))) i) ≫
          ModuleCat.ofHom l = ev.map (Sigma.ι M i) := by
        ext x
        change l (DirectSum.lof R I (fun i ↦ ↥(ev.obj (M i))) i x) = _
        exact DirectSum.toModule_lof R (M := fun i ↦ ↥(ev.obj (M i)))
          (φ := fun i ↦ (ev.map (Sigma.ι M i)).hom) i x
      rw [← Category.assoc, hleg, hd, Category.comp_id]
    have hdk : d ≫ k = 𝟙 _ := by
      apply Cofan.IsColimit.hom_ext hev'
      intro i
      change ev.map (Sigma.ι M i) ≫ (d ≫ k) = ev.map (Sigma.ι M i) ≫ 𝟙 _
      rw [← Category.assoc, hd]
      rw [show Sigma.ι (fun i ↦ ev.obj (M i)) i ≫ k = ev.map (Sigma.ι M i) from
        by
          dsimp [k]
          rw [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom]
          ext x
          change l (DirectSum.lof R I (fun i ↦ ↥(ev.obj (M i))) i x) = _
          exact DirectSum.toModule_lof R (M := fun i ↦ ↥(ev.obj (M i)))
            (φ := fun i ↦ (ev.map (Sigma.ι M i)).hom) i x]
      simp
    have : IsIso k := ⟨⟨d, hk, hdk⟩⟩
    have : IsIso (ModuleCat.ofHom l) := by
      dsimp [k] at *
      exact IsIso.of_isIso_comp_left e.hom _
    exact (ModuleCat.epi_iff_surjective (ModuleCat.ofHom l)).1 inferInstance
  let φ := DirectSum.toModule R I (ev.obj (H.obj S))
    (fun i ↦ (ev.map (H.map (ι i))).hom)
  have hcomp : (ev.map c).hom.comp l = φ := by
    apply DirectSum.linearMap_ext
    intro i
    ext x
    dsimp only [LinearMap.comp_apply, l, φ]
    rw [DirectSum.toModule_lof, DirectSum.toModule_lof]
    change (ev.map (Sigma.ι M i) ≫ ev.map c).hom x = _
    rw [← ev.map_comp]
    rw [show Sigma.ι M i ≫ c = H.map (ι i) from Sigma.ι_comp_desc _ _]
  have hsurj : Function.Surjective (ev.map c).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  change Function.Surjective φ
  rw [← hcomp]
  exact hsurj.comp hl


end AlgebraicGeometry
