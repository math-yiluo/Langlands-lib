/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.PerfectSupportedMapLift
import WeilConjectures.AlgebraicGeometry.SupportedPerfectGenerator
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.LocallySmall
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Detecting open support by global perfect tests

Source: Stacks Project, Tags 09IS and 09IM; Tag 0E4G, first paragraph of the proof.
(blueprint: lem-sc-perfect-open-support-detection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem open_scheme_localization (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    Nonempty (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))) := by
  let B := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  let := HasDerivedCategory.standard B
  let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌ B :=
    Scheme.Modules.overEquiv U
  let E := e.inverse
  let R := e.functor
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  have : R.Additive := Functor.additive_of_preserves_binary_products R
  have : (E ⋙ R).Additive := inferInstance
  let d : E.mapDerivedCategory ⋙ R.mapDerivedCategory ≅ 𝟭 (DerivedCategory B) :=
    Functor.mapDerivedCategoryCompIso E R ≪≫
      Functor.mapDerivedCategoryNatIso e.counitIso ≪≫ Functor.mapDerivedCategoryIdIso B
  let : E.mapDerivedCategory.Faithful := Functor.Faithful.of_comp_iso d
  let : LocallySmall.{w} (DerivedCategory B) :=
    locallySmall_of_faithful E.mapDerivedCategory
  exact ⟨MorphismProperty.hasLocalizationOfLocallySmall.{w}
    (HomologicalComplex.quasiIso B (.up ℤ)) DerivedCategory.Q⟩

private theorem perfect_shift (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    {P : schemeDerivedCategory X} (hP : Scheme.IsPerfect X P) (n : ℤ) :
    Scheme.IsPerfect X (P⟦n⟧) := by
  intro x
  obtain ⟨W, hx, K, ⟨⟨a, b, hb⟩, hf⟩, ⟨e⟩⟩ := hP x
  refine ⟨W, hx, K⟦n⟧, ⟨?_, ?_⟩, ?_⟩
  · exact ⟨a - n, b - n, fun i hi ↦ hb (i + n) (by omega)⟩
  · exact fun i ↦ hf (i + n)
  · let L := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    exact ⟨(L.commShiftIso n).app P ≪≫ (shiftFunctor _ n).mapIso e ≪≫
      ((DerivedCategory.Q.commShiftIso n).app K).symm⟩

-- Transport a zero map through a comparison without unfolding its construction.
private theorem map_eq_zero_of_comp_iso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (F : C ⥤ D) (G : D ⥤ E) [G.PreservesZeroMorphisms]
    (L : C ⥤ E) (e : F ⋙ G ≅ L) {A B : C} (f : A ⟶ B)
    (hf : F.map f = 0) : L.map f = 0 := by
  apply (cancel_mono (e.inv.app B)).mp
  rw [zero_comp, e.inv.naturality]
  change e.inv.app A ≫ G.map (F.map f) = 0
  rw [hf, Functor.map_zero, comp_zero]

/-- If every map from a global perfect complex into K vanishes after restriction to a
quasi-compact open U, every cohomology stalk of K on U is zero.
Source: Stacks Project, Tags 09IS, 09IM, and the proof of Tag 0E4G.
(blueprint: lem-sc-perfect-open-support-detection).

Proof: U is qcqs. Exact restriction preserves quasi-coherent cohomology. If K restricts
nontrivially, perfect generation on U detects it by a nonzero map from a perfect object
on U (absorb a shift into that perfect object). Apply the perfect supported map lifting
lemma with closed subset X: it supplies a global perfect P and beta : P -> K, and a
split inclusion of the original test into P restricted to U compatible with the maps.
Perfection implies quasi-coherent cohomology, so P is an object of D_QCoh(X). The assumed
vanishing of beta restricted to U forces the original map to vanish, a contradiction.
Thus the restriction of K is zero. Restriction commutes with homology and its stalks at
points of U equal the ambient stalks, giving the conclusion. For the open subscheme,
start with its standard derived model. The inverse over-site equivalence induces a
faithful derived functor into the supplied slice-site model, so Mathlib's locally-small
localization construction supplies a model in the same Hom universe. The existing
open-localization theorem supplies its open models. For empty U the conclusion is
vacuous; for U = X this
is the perfect generation criterion itself. -/
theorem perfect_open_support_detection
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (U : X.Opens) (hU : IsCompact (U : Set X)) (K : schemeDerivedQCohCategory X)
    (htest : ∀ (P : schemeDerivedQCohCategory X), Scheme.IsPerfect X P.obj →
      ∀ β : P ⟶ K,
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
          U).mapDerivedCategory.map β.hom = 0) :
    ∀ (n : ℤ) (x : X), x ∈ U →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj).val.presheaf x)) :=
  by
    classical
    let : HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
      (open_scheme_localization X U).some
    let : ∀ W : U.toScheme.Opens,
        HasDerivedCategory.{w} (SheafOfModules.{u}
          ((moduleRings U.toScheme.toRingedSpace).over W)) :=
      (nonempty_derivedOpenLocalization U.toScheme).some
    have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
    have : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
    let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
        SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv U
    let O := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
    have : O.Additive := Functor.additive_of_preserves_binary_products O
    have : e.functor.Additive := Functor.additive_of_preserves_binary_products e.functor
    let F := O ⋙ e.functor
    have : F.Additive := inferInstance
    have : PreservesFiniteLimits F := comp_preservesFiniteLimits O e.functor
    have : PreservesFiniteColimits F := comp_preservesFiniteColimits O e.functor
    let L := F.mapDerivedCategory
    have hqc : schemeDerivedQCohProperty U.toScheme (L.obj K.obj) := by
      apply (schemeDerivedQCoh_openRestriction_iff X U K.obj).mpr
      intro n
      have := K.property n
      exact SheafOfModules.isQuasicoherent_over _ U
    obtain ⟨_, E, hE, _, hgen⟩ :=
      supported_perfect_generator U.toScheme Set.univ isClosed_univ (by simp)
    have hzero : IsZero (L.obj K.obj) := by
      apply (hgen ⟨L.obj K.obj, hqc⟩ (by simp)).mpr
      intro n
      have hmaps (α : E.obj⟦n⟧ ⟶ L.obj K.obj) : α = 0 := by
        have hshift := perfect_shift U.toScheme hE n
        obtain ⟨R, β, hR, _, ι, π, _, hα⟩ :=
          Scheme.exists_perfect_supported_map_lift X U hU Set.univ isClosed_univ
            (by simp) K (E.obj⟦n⟧) hshift (by simp) α
        let P : schemeDerivedQCohCategory X :=
          ⟨R, schemeDerivedQCohProperty_of_isPerfect X R hR⟩
        have hβ := htest P hR (ObjectProperty.homMk β)
        change O.mapDerivedCategory.map β = 0 at hβ
        have hLβ : L.map β = 0 :=
          map_eq_zero_of_comp_iso O.mapDerivedCategory e.functor.mapDerivedCategory L
            (Functor.mapDerivedCategoryCompIso O e.functor) β hβ
        rw [← hα]
        change ι ≫ L.map β = 0
        rw [hLβ, comp_zero]
      exact ⟨fun α α' ↦ (hmaps α).trans (hmaps α').symm⟩
    intro n x hx
    let H := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj
    have hFH : IsZero (F.obj H) := by
      exact ((DerivedCategory.homologyFunctor _ n).map_isZero hzero).of_iso
        ((F.mapDerivedCategoryHomologyFunctorIso n).app K.obj)
    let c : F.obj H ≅ (Scheme.Modules.restrictFunctor U.ι).obj H :=
      (Scheme.Modules.overFunctorEquiv U).app H
    have hRH := hFH.of_iso c.symm
    let S := Scheme.Modules.toPresheaf U.toScheme ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨x, hx⟩ : U)
    have : (Scheme.Modules.toPresheaf U.toScheme).Additive := ⟨by intros; rfl⟩
    have : S.Additive := by dsimp [S]; infer_instance
    have hz := S.map_isZero hRH
    let eStalk := (Scheme.Modules.restrictStalkNatIso U.ι (⟨x, hx⟩ : U)).app H
    exact AddCommGrpCat.subsingleton_of_isZero (hz.of_iso eStalk.symm)

end AlgebraicGeometry
