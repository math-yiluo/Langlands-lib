/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimit


public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.AlgebraicGeometry.ConstructibleSubobjectPresentation
import WeilConjectures.AlgebraicGeometry.ConstantModuleSheavesForgetColimits
import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimitExtension
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Constructible approximation for the eight assertions

Source: Stacks Project, Theorem 59.83.10 (03SC), first proof paragraph,
and Lemma 59.73.2 (03SA).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

open Etale


private theorem sheafH_colimit
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    {D : A ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cocone D} (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit ((Sheaf.functorH X.smallEtaleTopology q).mapCocone c)) := by
  obtain ⟨I, horder, hdirected, hnonempty, T, hfinal⟩ := IsFiltered.exists_directed A
  let := horder
  let := hdirected
  let := hnonempty
  let := hfinal
  have hT : IsColimit (c.whisker T) :=
    (Functor.Final.isColimitWhiskerEquiv T c).symm hc
  obtain ⟨hR⟩ := Scheme.etaleCohomology_isColimit_of_isDirected X hT q
  obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso X q
  have hE : IsColimit ((Sheaf.functorH X.smallEtaleTopology q).mapCocone (c.whisker T)) :=
    IsColimit.mapCoconeEquiv e.symm hR
  exact ⟨(Functor.Final.isColimitWhiskerEquiv T _) hE⟩

private theorem subsingleton_of_filtered_cohomology
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    {D : A ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cocone D} (hc : IsColimit c) (q : ℕ)
    (hD : ∀ a, Subsingleton (Sheaf.H (D.obj a) q)) :
    Subsingleton (Sheaf.H c.pt q) := by
  let E := Sheaf.functorH X.smallEtaleTopology q
  have hE := (sheafH_colimit hc q).some
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (forget AddCommGrpCat.{u + 1}) := inferInstance
  have hz : ∀ x : Sheaf.H c.pt q, x = 0 := by
    intro x
    obtain ⟨a, y, hy⟩ := Concrete.isColimit_exists_rep (D ⋙ E) hE x
    have : Subsingleton (Sheaf.H (D.obj a) q) := hD a
    change Sheaf.H (D.obj a) q at y
    have hy0 : y = 0 := Subsingleton.elim _ _
    simpa only [hy0, map_zero] using hy.symm
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

private theorem bijective_of_filtered_cohomology
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (a : Y ⟶ X)
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    {D : A ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cocone D} (hc : IsColimit c) (q : ℕ)
    (hD : ∀ j, Function.Bijective (Etale.cohomologyMap a (D.obj j) q)) :
    Function.Bijective (Etale.cohomologyMap a c.pt q) := by
  let L := Sheaf.functorH X.smallEtaleTopology q
  let L' := (a)^*[AddCommGrpCat.{u + 1}] ⋙ Sheaf.functorH Y.smallEtaleTopology q
  have : PreservesColimit D L := preservesColimit_of_preserves_colimit_cocone
    hc (sheafH_colimit hc q).some
  have hc' : IsColimit (((a)^*[AddCommGrpCat.{u + 1}]).mapCocone c) :=
    isColimitOfPreserves _ hc
  have : PreservesColimit D L' := preservesColimit_of_preserves_colimit_cocone
    hc (sheafH_colimit hc' q).some
  let α : L ⟶ L' :=
    { app := fun K ↦ AddCommGrpCat.ofHom (Etale.cohomologyMap a K q)
      naturality := by
        intro K K' φ
        ext x
        exact Etale.cohomologyMap_map a q φ x }
  have : ∀ j, IsIso ((Functor.whiskerLeft D α).app j) := by
    intro j
    exact (ConcreteCategory.isIso_iff_bijective _).2 (hD j)
  have : IsIso (Functor.whiskerLeft D α) := NatIso.isIso_of_isIso_app _
  have : IsIso (α.app c.pt) := isIso_app_coconePt_of_preservesColimit D α c hc
  exact ConcreteCategory.bijective_of_isIso (α.app c.pt)

private theorem surjective_of_filtered_cohomology
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (a : Y ⟶ X)
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    {D : A ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cocone D} (hc : IsColimit c) (q : ℕ)
    (hD : ∀ j, Function.Surjective (Etale.cohomologyMap a (D.obj j) q)) :
    Function.Surjective (Etale.cohomologyMap a c.pt q) := by
  let E := Sheaf.functorH Y.smallEtaleTopology q
  let D' := D ⋙ (a)^*[AddCommGrpCat.{u + 1}]
  have hc' : IsColimit (((a)^*[AddCommGrpCat.{u + 1}]).mapCocone c) :=
    isColimitOfPreserves _ hc
  have hE := (sheafH_colimit hc' q).some
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (forget AddCommGrpCat.{u + 1}) := inferInstance
  intro x
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep (D' ⋙ E) hE x
  obtain ⟨z, hz⟩ := hD j y
  refine ⟨Sheaf.H.map (c.ι.app j) q z, ?_⟩
  calc
    _ = Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map (c.ι.app j)) q
        (Etale.cohomologyMap a (D.obj j) q z) :=
      Etale.cohomologyMap_map a q (c.ι.app j) z
    _ = x := by rw [hz]; exact hy

private theorem primary_of_mono
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    {G F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : G ⟶ F) [Mono ι] (p : ℕ) (hF : Scheme.IsPrimaryTorsionSheaf Λ F p) :
    Scheme.IsPrimaryTorsionSheaf Λ G p := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} (ModuleCat.{u + 1} Λ)
  intro Ω _ _ s x
  let E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
    (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have : PreservesFiniteLimits E := inferInstance
  have : E.PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape E
  have hm : Mono (E.map ι) := Functor.map_mono E ι
  have hi : Function.Injective (E.map ι).hom :=
    (ModuleCat.mono_iff_injective.{u + 1, u + 1} (E.map ι)).mp hm
  obtain ⟨n, hn⟩ := hF Ω s (E.map ι x)
  use n
  apply hi
  change (E.map ι).hom (p ^ n • x) = (E.map ι).hom 0
  simpa only [map_nsmul, map_zero] using hn

private theorem invertible_order_of_mono
    (Λ : Type (u + 1)) [CommRing Λ] {X B : Scheme.{u}}
    {G F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : G ⟶ F) [Mono ι] [Scheme.IsTorsionSheafOfInvertibleOrder B F] :
    Scheme.IsTorsionSheafOfInvertibleOrder B G := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} (ModuleCat.{u + 1} Λ)
  constructor
  intro Ω _ _ s x
  let E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
    (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have : PreservesFiniteLimits E := inferInstance
  have : E.PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape E
  have hm : Mono (E.map ι) := Functor.map_mono E ι
  have hi : Function.Injective (E.map ι).hom :=
    (ModuleCat.mono_iff_injective.{u + 1, u + 1} (E.map ι)).mp hm
  obtain ⟨n, hn, hu, hx⟩ :=
    Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
      (S := B) Ω s (E.map ι x)
  refine ⟨n, hn, hu, ?_⟩
  apply hi
  change (E.map ι).hom (n • x) = (E.map ι).hom 0
  simpa only [map_nsmul, map_zero] using hx

/-- On a fixed curve, assertions for all constructible Λ-module sheaves imply assertions
for every torsion Λ-module sheaf, provided Λ is finite.
Source: Stacks Project, Theorem 59.83.10 (03SC), first proof paragraph; Lemma 03SA.
(blueprint: lem-weil-pbc-constructible-approximation-assertions)

Proof: By 03SA(3), write F as a filtered colimit of constructible Λ-module sheaves.
Replace each stage by its image in F. The kernel of its map to F is a subsheaf of
a constructible sheaf on the Noetherian curve, hence constructible over the finite
(and thus Noetherian) ring Λ. Its cokernel, the image, is therefore constructible.
These images form a filtered union equal to F: every local section of F locally
comes from a stage. Thus we may use constructible Λ-submodule sheaves of F.
Forgetting scalars preserves this filtered colimit, as does inverse image.
Cohomology on the curve and its field extensions commutes with these filtered colimits
(03Q5; equivalently the Ext-to-derived comparison followed by derived continuity).
Vanishing C1,C2 is inherited from the constructible stages. If F is p-primary,
its subsheaves are p-primary, giving C3. If F has invertible torsion orders, so do
its subsheaves; naturality identifies its comparison map with the colimit of the
bijective stagewise maps, giving C6. The same argument without the order condition
and with properness gives C7. For C8, each class on the open comes from a stage;
lift it there by C8 and map the lift into H2(X,F). For C4,C5 the conclusion is
conditional on F itself being constructible, so use H on F directly: finiteness
is not inferred from a filtered colimit of finite groups. The filtered system
includes the zero subsheaf, so the empty scheme and zero sheaf cause no exception. -/
theorem IsCurve.assertions_of_constructible_approximation
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (H : ∀ (G : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [Scheme.IsConstructibleSheaf G], IsCurve.Assertions Λ f G)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionModuleSheaf F] :
    IsCurve.Assertions Λ f F := by
  have : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨A, hA, hfiltered, D, ι, hD, hmono, ⟨hc⟩⟩ :=
    Scheme.exists_filtered_colimit_constructible_subobjects F
  let := hA
  let := hfiltered
  let U := sheafCompose C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let c := U.mapCocone (Cocone.mk F ι)
  have : PreservesColimitsOfSize.{u + 1, u + 1} U :=
    Etale.constantModuleSheaves_forget_preservesColimits C Λ
  have hcU : IsColimit c := isColimitOfPreserves U hc
  have hstage (a : A) : IsCurve.Assertions Λ f (D.obj a) := by
    have : Scheme.IsConstructibleSheaf (D.obj a) := hD a
    exact H (D.obj a)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact subsingleton_of_filtered_cohomology hcU q
      (fun a ↦ (hstage a).subsingleton_of_two_lt q hq)
  · intro _ q hq
    exact subsingleton_of_filtered_cohomology hcU q
      (fun a ↦ (hstage a).subsingleton_of_one_lt_of_isAffine q hq)
  · intro p _ _ hF q hq
    apply subsingleton_of_filtered_cohomology hcU q
    intro a
    have : Mono (ι.app a) := hmono a
    exact (hstage a).subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p
      (primary_of_mono Λ (ι.app a) p hF) q hq
  · intro _ _ q
    exact (H F).finite_of_isTorsionSheafOfInvertibleOrder q
  · intro _ _ q
    exact (H F).finite_of_isProper q
  · intro _ k' _ _ C' ι' f' a h q
    have : IsSeparated f' := MorphismProperty.of_isPullback h inferInstance
    have : QuasiCompact f' := MorphismProperty.of_isPullback h inferInstance
    have : CompactSpace C' := (quasiCompact_iff_compactSpace f').mp inferInstance
    have : QuasiSeparatedSpace C' := quasiSeparatedSpace_of_quasiSeparated f'
    apply bijective_of_filtered_cohomology a hcU q
    intro j
    have : Mono (ι.app j) := hmono j
    have : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) (D.obj j) :=
      invertible_order_of_mono Λ (F := F) (ι.app j)
    exact (hstage j).bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' h q
  · intro _ k' _ _ C' ι' f' a h q
    have : IsSeparated f' := MorphismProperty.of_isPullback h inferInstance
    have : QuasiCompact f' := MorphismProperty.of_isPullback h inferInstance
    have : CompactSpace C' := (quasiCompact_iff_compactSpace f').mp inferInstance
    have : QuasiSeparatedSpace C' := quasiSeparatedSpace_of_quasiSeparated f'
    exact bijective_of_filtered_cohomology a hcU q
      (fun j ↦ (hstage j).bijective_cohomologyMap_of_isProper k' h q)
  · intro W a _
    have : IsNoetherian W := isNoetherian_of_locallyOfFiniteType a
    exact surjective_of_filtered_cohomology a hcU 2
      (fun j ↦ (hstage j).surjective_cohomologyMap_of_isOpenImmersion a)

end AlgebraicGeometry
