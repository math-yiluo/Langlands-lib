/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

/-! # Left derived values commute with shifts

Source: Stacks Project, Derived Categories, Lemma 05SU(2)
(blueprint: lem-pur-derived-functor-shift-05su).
-/

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Apply a functor to the cone, its retraction, and each factorization equation.
Source: Stacks Project, Categories, Definition 05PU(2)
(blueprint: def-pc-essentially-constant-pro-diagram). -/
private theorem pro_map
    {J : Type*} {A B : Type*} [Category J] [Category A] [Category B]
    (G : J ⥤ A) (H : A ⥤ B) (Y : A) (h : IsEssentiallyConstantProDiagram G Y) :
    IsEssentiallyConstantProDiagram (G ⋙ H) (H.obj Y) := by
  obtain ⟨hc, u, j₀, r, hr, hf⟩ := h
  refine ⟨hc, (H.mapCone (Cone.mk Y u)).π, j₀, H.map r, ?_, ?_⟩
  · change H.map (u.app j₀) ≫ H.map r = 𝟙 _
    rw [← H.map_comp, hr]
    exact H.map_id Y
  · intro j
    obtain ⟨k, a, b, hab⟩ := hf j
    refine ⟨k, a, b, ?_⟩
    change H.map (G.map b) = H.map (G.map a) ≫ H.map r ≫ H.map (u.app j)
    rw [hab, H.map_comp, H.map_comp]

/-- Compose the cone with the diagram isomorphism and the retraction with its inverse.
Naturality transports the common-stage factorization equation.
Source: Stacks Project, Categories, Definition 05PU(2)
(blueprint: def-pc-essentially-constant-pro-diagram). -/
private theorem pro_iso
    {J : Type*} {A : Type*} [Category J] [Category A]
    {G G' : J ⥤ A} (e : G ≅ G') (Y : A)
    (h : IsEssentiallyConstantProDiagram G Y) :
    IsEssentiallyConstantProDiagram G' Y := by
  obtain ⟨hc, u, j₀, r, hr, hf⟩ := h
  refine ⟨hc, u ≫ e.hom, j₀, e.inv.app j₀ ≫ r, ?_, ?_⟩
  · simpa using hr
  · intro j
    obtain ⟨k, a, b, hab⟩ := hf j
    refine ⟨k, a, b, ?_⟩
    dsimp
    apply (cancel_epi (e.hom.app k)).mp
    rw [← e.hom.naturality b, hab]
    simp only [Category.assoc, ← e.hom.naturality_assoc a,
      Iso.hom_inv_id_app_assoc]

/-- Pull a cone back along an equivalence. Use the inverse image of the retraction
stage, and compose its retraction with the counit. For each common earlier stage,
apply the inverse functor to its two maps, using the inverse unit to reach the given
stage. Counit naturality and the triangle identity give the factorization equation.
Source: Stacks Project, Categories, Definition 05PU(2)
(blueprint: def-pc-essentially-constant-pro-diagram). -/
private theorem pro_reindex
    {J K : Type*} {A : Type*} [Category J] [Category K] [Category A]
    (e : K ≌ J) (G : J ⥤ A) (Y : A) (h : IsEssentiallyConstantProDiagram G Y) :
    IsEssentiallyConstantProDiagram (e.functor ⋙ G) Y := by
  obtain ⟨hc, u, j₀, r, hr, hf⟩ := h
  have : IsCofiltered J := hc
  refine ⟨IsCofiltered.of_equivalence e.symm, ?_, e.inverse.obj j₀,
    G.map (e.counitIso.hom.app j₀) ≫ r, ?_, ?_⟩
  · exact { app := fun k ↦ u.app (e.functor.obj k)
            naturality := fun k l f ↦ by simpa using u.naturality (e.functor.map f) }
  · change u.app _ ≫ G.map (e.counitIso.hom.app j₀) ≫ r = 𝟙 Y
    rw [← Category.assoc, ← u.naturality]
    simpa using hr
  · intro j
    obtain ⟨k, a, b, hab⟩ := hf (e.functor.obj j)
    refine ⟨e.inverse.obj k, e.inverse.map a,
      e.inverse.map b ≫ e.unitIso.inv.app j, ?_⟩
    change G.map (e.functor.map (e.inverse.map b ≫ e.unitIso.inv.app j)) =
      G.map (e.functor.map (e.inverse.map a)) ≫
        (G.map (e.counitIso.hom.app j₀) ≫ r) ≫ u.app (e.functor.obj j)
    rw [e.functor.map_comp, ← e.counit_app_functor,
      e.counit_naturality b, G.map_comp, hab]
    simp only [Category.assoc]
    rw [← G.map_comp_assoc, ← e.counit_naturality a, G.map_comp]
    simp only [Category.assoc]

/-- Apply reindexing in both directions and cancel the inverse-functor composite.
Source: Stacks Project, Categories, Definition 05PU(2)
(blueprint: def-pc-essentially-constant-pro-diagram). -/
private theorem pro_reindex_iff
    {J K : Type*} {A : Type*} [Category J] [Category K] [Category A]
    (e : J ≌ K) (G : K ⥤ A) (Y : A) :
    IsEssentiallyConstantProDiagram (e.functor ⋙ G) Y ↔
      IsEssentiallyConstantProDiagram G Y := by
  constructor
  · intro h
    exact pro_iso (e.invFunIdAssoc G) Y (pro_reindex e.symm _ Y h)
  · exact pro_reindex e G Y

/-- Shift each denominator and each commuting triangle, using MS5 for membership in S.
Source: Stacks Project, Derived Categories, Lemma 05SU(2), Situation 05S8
(blueprint: lem-pur-derived-functor-shift-05su). -/
private def shiftOver
    {C : Type u} [Category.{v} C] [HasShift C ℤ]
    (S : MorphismProperty C) [S.IsCompatibleWithShift ℤ] (X : C) (n : ℤ) :
    S.Over ⊤ X ⥤ S.Over ⊤ ((shiftFunctor C n).obj X) where
  obj s := MorphismProperty.Over.mk ⊤ ((shiftFunctor C n).map s.hom)
    (S.shift s.prop n)
  map f := MorphismProperty.Over.homMk ((shiftFunctor C n).map f.left) (by
    change (shiftFunctor C n).map f.left ≫ (shiftFunctor C n).map _ = _
    rw [← Functor.map_comp, MorphismProperty.Over.w]
    rfl)
  map_id s := by ext; change (shiftFunctor C n).map (𝟙 _) = 𝟙 _; simp
  map_comp f g := by ext; simp

/-- The shift on denominators is fully faithful because the shift on C is. To lift an
object, choose a preimage of its source under the shift and lift its structural map
using fullness. MS5 and invariance under isomorphisms show this map belongs to S.
Source: Stacks Project, Derived Categories, Lemma 05SU(2), Situation 05S8
(blueprint: lem-pur-derived-functor-shift-05su). -/
private theorem shiftOver_equivalence
    {C : Type u} [Category.{v} C] [HasShift C ℤ]
    (S : MorphismProperty C) [S.IsCompatibleWithShift ℤ] [S.RespectsIso]
    (X : C) (n : ℤ) : (shiftOver S X n).IsEquivalence := by
  let T := shiftFunctor C n
  have : (shiftOver S X n).Faithful :=
    ⟨fun h ↦ MorphismProperty.Over.Hom.ext (T.map_injective
      (congrArg (fun f ↦ f.left) h))⟩
  have : (shiftOver S X n).Full := ⟨fun {s t} f ↦ by
    obtain ⟨g, hg⟩ := T.map_surjective f.left
    refine ⟨MorphismProperty.Over.homMk g ?_, ?_⟩
    · apply T.map_injective
      simpa only [Functor.map_comp, hg] using (show
        f.left ≫ T.map t.hom = T.map s.hom from MorphismProperty.Over.w f)
    · apply MorphismProperty.Over.Hom.ext
      exact hg⟩
  have : (shiftOver S X n).EssSurj := ⟨fun t ↦ by
    obtain ⟨A, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := T) t.left
    obtain ⟨s, hs⟩ := T.map_surjective (e.hom ≫ t.hom)
    have h : S s := (MorphismProperty.IsCompatibleWithShift.iff S s n).mp (by
      rw [hs]
      exact (S.cancel_left_of_respectsIso e.hom t.hom).mpr t.prop)
    exact ⟨MorphismProperty.Over.mk ⊤ s h,
      ⟨MorphismProperty.Over.isoMk e (by
        change e.hom ≫ t.hom = T.map s
        exact hs.symm)⟩⟩⟩
  exact {}

/-- In Situation 05S8, left-derived definedness is invariant under shifts, and shifted
values are canonically isomorphic, compatibly with any supplied value cones.
The cone legs specify the values as pro-objects, rather than only their underlying
objects. Their limit property follows from the retraction and common-stage
factorization in `IsEssentiallyConstantProDiagram`. The leg equation uniquely
characterizes the shift comparison; MS5 guarantees the shifted denominator belongs
to `S`, so its proof argument does not restrict the denominators being tested.
Source: Stacks Project, Derived Categories, Lemma 05SU(2)
(blueprint: lem-pur-derived-functor-shift-05su).
The proof shifts the denominator category by the equivalence induced by `[n]`, using
MS5 and its inverse. Exactness transports the essentially constant pro-diagram and
its value through the shift isomorphisms, preserving the cone, retraction, and
factorization conditions. The inverse shift gives the reverse implication. Finally,
the supplied limit cones are shifted, reindexed, and postcomposed with the commutation
isomorphism. Mathlib limit uniqueness gives the comparison isomorphism, and the
limit hom-extensionality lemma proves its uniqueness from the specified leg equation. -/
theorem isTriangulatedLeftDerivedDefinedAt_shift_iff
    {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty C)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    (X : C) (n : ℤ) :
    (F.IsTriangulatedLeftDerivedDefinedAt S hS X ↔
      F.IsTriangulatedLeftDerivedDefinedAt S hS ((shiftFunctor C n).obj X)) ∧
      (F.IsTriangulatedLeftDerivedDefinedAt S hS X →
        ∀ (Y Y' : D), F.IsTriangulatedLeftDerivedValue S hS X Y →
          F.IsTriangulatedLeftDerivedValue S hS ((shiftFunctor C n).obj X) Y' →
            let G := MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F
            let Gn := MorphismProperty.Over.forget S ⊤ ((shiftFunctor C n).obj X) ⋙
              Over.forget ((shiftFunctor C n).obj X) ⋙ F
            ∀ (u : (Functor.const (S.Over ⊤ X)).obj Y ⟶ G)
              (u' : (Functor.const (S.Over ⊤ ((shiftFunctor C n).obj X))).obj Y' ⟶ Gn),
              Nonempty (IsLimit (Cone.mk Y u)) → Nonempty (IsLimit (Cone.mk Y' u')) →
                ∃! e : (shiftFunctor D n).obj Y ≅ Y',
                  ∀ (s : S.Over ⊤ X) (hs : S ((shiftFunctor C n).map s.hom)),
                    e.hom ≫ u'.app (MorphismProperty.Over.mk ⊤
                        ((shiftFunctor C n).map s.hom) hs) =
                      (shiftFunctor D n).map (u.app s) ≫
                        (F.commShiftIso n).inv.app s.left) := by
  have : S.HasLeftCalculusOfFractions := hS.1.1.1
  have : S.IsCompatibleWithTriangulation := hS.2
  have : S.RespectsIso := MorphismProperty.respectsIso_of_isStableUnderComposition (by
    intro A B f hf
    have : IsIso f := hf
    apply hS.1.2 B A B A (CategoryTheory.inv f) f (CategoryTheory.inv f)
    · simpa using S.id_mem A
    · simpa using S.id_mem B)
  have := shiftOver_equivalence S X n
  let E := (shiftOver S X n).asEquivalence
  let G := MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F
  let Gn := MorphismProperty.Over.forget S ⊤ ((shiftFunctor C n).obj X) ⋙
    Over.forget ((shiftFunctor C n).obj X) ⋙ F
  let T := shiftEquiv D n
  let w : E.functor ⋙ Gn ≅ G ⋙ T.functor := NatIso.ofComponents
    (fun s ↦ (F.commShiftIso n).app s.left) (by
      intro s t f
      change F.map ((shiftFunctor C n).map f.left) ≫
        (F.commShiftIso n).hom.app t.left =
          (F.commShiftIso n).hom.app s.left ≫ (shiftFunctor D n).map (F.map f.left)
      exact (F.commShiftIso n).hom.naturality f.left)
  constructor
  · constructor
    · rintro ⟨Y, hY⟩
      refine ⟨T.functor.obj Y, ?_⟩
      apply (pro_reindex_iff E Gn _).mp
      exact pro_iso w.symm _ (pro_map G T.functor Y hY)
    · rintro ⟨Y, hY⟩
      refine ⟨T.inverse.obj Y, ?_⟩
      have h := pro_iso w Y (pro_reindex E Gn Y hY)
      exact pro_iso
        (Functor.associator G T.functor T.inverse ≪≫
          isoWhiskerLeft G T.unitIso.symm ≪≫ Functor.rightUnitor G)
        _ (pro_map (G ⋙ T.functor) T.inverse Y h)
  · intro _ Y Y' _ _
    dsimp only
    intro u u' hu hu'
    obtain ⟨hu⟩ := hu
    obtain ⟨hu'⟩ := hu'
    let c := T.functor.mapCone (Cone.mk Y u)
    have hc : IsLimit c := isLimitOfPreserves T.functor hu
    let c' := (Cone.postcompose w.hom).obj ((Cone.mk Y' u').whisker E.functor)
    have hc' : IsLimit c' :=
      (IsLimit.postcomposeHomEquiv w _).symm (hu'.whiskerEquivalence E)
    let e := hc.conePointUniqueUpToIso hc'
    refine ⟨e, ?_, ?_⟩
    · intro s hs
      change e.hom ≫ u'.app (E.functor.obj s) =
        T.functor.map (u.app s) ≫ w.inv.app s
      apply (Iso.eq_comp_inv (w.app s)).mpr
      rw [Category.assoc]
      exact hc.conePointUniqueUpToIso_hom_comp hc' s
    · intro e' he'
      apply Iso.ext
      apply hc'.hom_ext
      intro s
      change e'.hom ≫ (u'.app (E.functor.obj s) ≫ w.hom.app s) =
        e.hom ≫ (u'.app (E.functor.obj s) ≫ w.hom.app s)
      have h : e'.hom ≫ u'.app (E.functor.obj s) =
          T.functor.map (u.app s) ≫ w.inv.app s := he' s (S.shift s.prop n)
      rw [← Category.assoc, h]
      exact ((Iso.eq_comp_inv (w.app s)).mp rfl).trans
        (hc.conePointUniqueUpToIso_hom_comp hc' s).symm

end CategoryTheory.Functor
