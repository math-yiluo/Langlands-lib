/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteFinitePresentationInternalHomColimit
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Finite-presentation section calculus on the qcqs pro-etale site

Source: Stacks Project, Tags 0738 (4), 0GMZ, 0GN0 and 098D
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem finite_affine_cover
    {S : Scheme.{u}} {W : S.ProEt} [CompactSpace W.left]
    [QuasiSeparatedSpace W.left] {R : Sieve W}
    (hR : R ∈ Scheme.ProEt.topology S W) :
    ∃ (n : ℕ) (U : Fin n → S.ProEt) (g : ∀ a, U a ⟶ W),
      (∀ a, R (g a)) ∧ (∀ a, IsAffine (U a).left) ∧
      Sieve.ofArrows U g ∈ Scheme.ProEt.topology S W := by
  classical
  obtain ⟨P, hP, hPR⟩ := Scheme.ProEt.mem_topology_iff.mp hR
  obtain ⟨κ, Z, f, rfl⟩ := P.exists_eq_ofArrows
  let E : PreZeroHypercover W.left := ⟨κ, fun i ↦ (Z i).left, fun i ↦ (f i).left⟩
  have hP' := (Scheme.ProEt.mem_precoverage_iff.mp hP).1
  rw [Presieve.map_ofArrows] at hP'
  have : QuasiCompactCover E := Scheme.presieve₀_mem_qcPrecoverage_iff.mp hP'
  obtain ⟨n, a, O, hO, hcov⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact E
    (U := ⊤) isCompact_univ
  let U (i : Fin n) := Scheme.ProEt.ofOpenImmersion (Z (a i)) (O i).ι
  let g (i : Fin n) : U i ⟶ W :=
    Scheme.ProEt.ofOpenImmersionHom (Z (a i)) (O i).ι ≫ f (a i)
  have hU (i : Fin n) : IsAffine (U i).left := hO i
  have hg (i : Fin n) : WeaklyEtale (g i).left := by
    have hw : (g i).left ≫ W.hom = (U i).hom := MorphismProperty.Over.w (g i)
    have : WeaklyEtale ((g i).left ≫ W.hom) := hw ▸ inferInstance
    exact WeaklyEtale.of_comp (g i).left W.hom
  have hsurj : ∀ x : W.left, ∃ i, x ∈ Set.range (g i).left := by
    intro x
    have hx : x ∈ ⋃ i, E.f (a i) '' O i := by rw [hcov]; trivial
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, ⟨y, hy⟩, rfl⟩
  refine ⟨n, U, g, fun i ↦ R.downward_closed (hPR _ _ ⟨a i⟩) _, hU, ?_⟩
  apply Precoverage.generate_mem_toGrothendieck
  rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
  have hwe : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (g i).left) ∈
      Scheme.precoverage @WeaklyEtale W.left :=
    (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hsurj, hg⟩
  let C : W.left.Cover (Scheme.precoverage @WeaklyEtale) :=
    ⟨⟨Fin n, fun i ↦ (U i).left, fun i ↦ (g i).left⟩, hwe⟩
  have (i : Fin n) : CompactSpace (U i).left := by have := hU i; infer_instance
  have (i : Fin n) : QuasiCompact (g i).left := inferInstance
  have : QuasiCompactCover C.toPreZeroHypercover := QuasiCompactCover.of_finite
  exact ⟨(Scheme.presieve₀_mem_qcPrecoverage_iff (E := C.toPreZeroHypercover)).mpr
    (inferInstanceAs (QuasiCompactCover C.toPreZeroHypercover)), hwe⟩

private theorem abelian_isSheafFor
    {S : Scheme.{u}} (F : Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
    {W : S.ProEt} {κ : Type*} {U : κ → S.ProEt} (g : ∀ i, U i ⟶ W)
    (hg : Sieve.ofArrows U g ∈ Scheme.ProEt.topology S W) :
    Presieve.IsSheafFor (F.obj ⋙ forget _) (Presieve.ofArrows U g) := by
  rw [Presieve.isSheafFor_iff_generate]
  exact ((isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (forget _) F.property)) _ hg

private theorem abelian_presheaf_colimit
    {S : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
    (c : Cocone F) (hc : IsColimit c) :
    ∃ (E : Cocone (F ⋙ sheafToPresheaf _ _)) (_ : IsColimit E) (φ : E.pt ⟶ c.pt.obj),
      Presheaf.IsLocallySurjective (Scheme.ProEt.topology S) φ ∧
      Presheaf.IsLocallyInjective (Scheme.ProEt.topology S) φ ∧
      ∀ i, E.ι.app i ≫ φ = (c.ι.app i).hom := by
  let E := colimit.cocone (F ⋙ sheafToPresheaf _ _)
  let hE := colimit.isColimit (F ⋙ sheafToPresheaf _ _)
  let e := (Sheaf.isColimitSheafifyCocone E hE).coconePointUniqueUpToIso hc
  refine ⟨E, hE, toSheafify _ E.pt ≫ e.hom.hom, inferInstance, inferInstance, ?_⟩
  intro i
  rw [← Category.assoc, ← Sheaf.sheafifyCocone_ι_app_val,
    ← ObjectProperty.FullSubcategory.comp_hom,
    IsColimit.comp_coconePointUniqueUpToIso_hom]

private theorem abelian_local_lift
    {S : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
    (c : Cocone F) (hc : IsColimit c) {W : S.ProEt}
    (s : c.pt.obj.obj (op W)) :
    ∃ R ∈ Scheme.ProEt.topology S W, ∀ ⦃U : S.ProEt⦄ (f : U ⟶ W), R f →
      ∃ (i : I) (t : (F.obj i).obj.obj (op U)),
        (c.ι.app i).hom.app (op U) t = c.pt.obj.map f.op s := by
  obtain ⟨E, hE, φ, hs, _, hφ⟩ := abelian_presheaf_colimit F c hc
  refine ⟨_, Presheaf.imageSieve_mem _ φ s, fun U f ⟨p, hp⟩ ↦ ?_⟩
  have hEU := isColimitOfPreserves ((evaluation _ _).obj (op U)) hE
  obtain ⟨i, t, rfl⟩ := Concrete.isColimit_exists_rep _ hEU p
  refine ⟨i, t, Eq.trans ?_ hp⟩
  rw [← hφ i]
  rfl

private theorem abelian_local_equality
    {S : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
    (c : Cocone F) (hc : IsColimit c) {W : S.ProEt} {i : I}
    (s t : (F.obj i).obj.obj (op W))
    (h : (c.ι.app i).hom.app (op W) s = (c.ι.app i).hom.app (op W) t) :
    ∃ R ∈ Scheme.ProEt.topology S W, ∀ ⦃U : S.ProEt⦄ (f : U ⟶ W), R f →
      ∃ (j : I) (a : i ⟶ j),
        (F.map a).hom.app (op U) ((F.obj i).obj.map f.op s) =
          (F.map a).hom.app (op U) ((F.obj i).obj.map f.op t) := by
  obtain ⟨E, hE, φ, _, hi, hφ⟩ := abelian_presheaf_colimit F c hc
  have h' : φ.app (op W) ((E.ι.app i).app (op W) s) =
      φ.app (op W) ((E.ι.app i).app (op W) t) := by
    change (E.ι.app i ≫ φ).app _ s = (E.ι.app i ≫ φ).app _ t
    rw [hφ]
    exact h
  refine ⟨_, Presheaf.equalizerSieve_mem _ φ _ _ h', fun U f hf ↦ ?_⟩
  have hEU := isColimitOfPreserves ((evaluation _ _).obj (op U)) hE
  have hf' : (E.ι.app i).app (op U) ((F.obj i).obj.map f.op s) =
      (E.ι.app i).app (op U) ((F.obj i).obj.map f.op t) := by
    have hn := (E.ι.app i).naturality f.op
    have e1 := ConcreteCategory.congr_hom hn s
    have e2 := ConcreteCategory.congr_hom hn t
    simp only [ConcreteCategory.comp_apply] at e1 e2
    erw [e1, e2]
    exact hf
  obtain ⟨j, a, b, hab⟩ := Concrete.isColimit_exists_of_rep_eq _ hEU _ _ hf'
  refine ⟨_, a ≫ IsFiltered.coeqHom a b, ?_⟩
  let q := IsFiltered.coeqHom a b
  calc (F.map (a ≫ q)).hom.app (op U) ((F.obj i).obj.map f.op s)
      = (F.map q).hom.app (op U) ((F.map a).hom.app (op U)
          ((F.obj i).obj.map f.op s)) := by rw [F.map_comp]; rfl
    _ = (F.map q).hom.app (op U) ((F.map b).hom.app (op U)
          ((F.obj i).obj.map f.op t)) := congrArg _ hab
    _ = (F.map (b ≫ q)).hom.app (op U) ((F.obj i).obj.map f.op t) := by
      rw [F.map_comp]; rfl
    _ = _ := by rw [← IsFiltered.coeq_condition a b]

private theorem abelian_eventual_equality
    {S : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
    (c : Cocone F) (hc : IsColimit c) {W : S.ProEt}
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] {i : I}
    (s t : (F.obj i).obj.obj (op W))
    (h : (c.ι.app i).hom.app (op W) s = (c.ι.app i).hom.app (op W) t) :
    ∃ (j : I) (a : i ⟶ j),
      (F.map a).hom.app (op W) s = (F.map a).hom.app (op W) t := by
  obtain ⟨R, hR, hlocal⟩ := abelian_local_equality F c hc s t h
  obtain ⟨n, U, g, hRg, _, hcover⟩ := finite_affine_cover hR
  choose j a ha using fun k ↦ hlocal (g k) (hRg k)
  obtain ⟨k, A, b, hb⟩ := IsFiltered.wideSpan a
  refine ⟨k, A, (abelian_isSheafFor (F.obj k) g hcover).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨l⟩
  change (F.obj k).obj.map (g l).op _ = (F.obj k).obj.map (g l).op _
  have hnat (z : (F.obj i).obj.obj (op W)) :
      (F.obj k).obj.map (g l).op ((F.map A).hom.app _ z) =
        (F.map (b l)).hom.app _ ((F.map (a l)).hom.app _
          ((F.obj i).obj.map (g l).op z)) := by
    rw [← hb l, F.map_comp]
    exact (NatTrans.naturality_apply (F.map (a l) ≫ F.map (b l)).hom (g l).op z).symm
  rw [hnat, hnat, ha l]

private theorem qcqs_pullback
    {S : Scheme.{u}} {W U V : S.ProEt} (f : U ⟶ W) (g : V ⟶ W)
    [QuasiSeparatedSpace W.left] [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    [CompactSpace V.left] [QuasiSeparatedSpace V.left] :
    CompactSpace (pullback f g).left ∧ QuasiSeparatedSpace (pullback f g).left := by
  let e := PreservesPullback.iso (Scheme.ProEt.forget S ⋙ Over.forget S) f g
  have : QuasiCompact f.left := inferInstance
  have : CompactSpace ↥(pullback (C := Scheme.{u}) f.left g.left) := inferInstance
  have : QuasiSeparatedSpace ↥(pullback (C := Scheme.{u}) f.left g.left) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f.left g.left)
  let h := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e).symm
  exact ⟨@Homeomorph.compactSpace _ _ _ _ ‹_› h,
    (quasiSeparatedSpace_congr h).mp ‹_›⟩

private theorem finite_common_target
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I] {κ : Type*} [Finite κ]
    (j : κ → I) : ∃ i, Nonempty (∀ k, j k ⟶ i) := by
  classical
  have := Fintype.ofFinite κ
  let O : Finset I := Finset.univ.image j
  exact ⟨IsFiltered.sup O ∅, ⟨fun k ↦ IsFiltered.toSup O ∅
    (Finset.mem_image_of_mem _ (Finset.mem_univ k))⟩⟩

private theorem abelian_section_lift
    {S : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
    (c : Cocone F) (hc : IsColimit c) {W : S.ProEt}
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] (s : c.pt.obj.obj (op W)) :
    ∃ (i : I) (t : (F.obj i).obj.obj (op W)), (c.ι.app i).hom.app (op W) t = s := by
  classical
  obtain ⟨R, hR, hlocal⟩ := abelian_local_lift F c hc s
  obtain ⟨n, U, g, hRg, hU, hcover⟩ := finite_affine_cover hR
  choose j t ht using fun k ↦ hlocal (g k) (hRg k)
  obtain ⟨i, ⟨b⟩⟩ := finite_common_target j
  let t' (k : Fin n) : (F.obj i).obj.obj (op (U k)) := (F.map (b k)).hom.app _ (t k)
  have ht' (k : Fin n) : (c.ι.app i).hom.app _ (t' k) =
      c.pt.obj.map (g k).op s := by
    rw [← ht k, ← c.w (b k)]
    rfl
  have hpair (kl : Fin n × Fin n) : ∃ (j : I) (a : i ⟶ j),
      (F.map a).hom.app _ ((F.obj i).obj.map (pullback.fst (g kl.1) (g kl.2)).op
        (t' kl.1)) =
      (F.map a).hom.app _ ((F.obj i).obj.map (pullback.snd (g kl.1) (g kl.2)).op
        (t' kl.2)) := by
    have := hU kl.1
    have := hU kl.2
    obtain ⟨_, _⟩ := qcqs_pullback (g kl.1) (g kl.2)
    refine abelian_eventual_equality F c hc _ _ ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ht', ht']
    change c.pt.obj.map _ (c.pt.obj.map _ s) = c.pt.obj.map _ (c.pt.obj.map _ s)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, pullback.condition]
  choose j' a' ha' using hpair
  obtain ⟨k, A, b', hb'⟩ := IsFiltered.wideSpan a'
  let z (l : Fin n) : (F.obj k).obj.obj (op (U l)) := (F.map A).hom.app _ (t' l)
  have hz (l : Fin n) : (c.ι.app k).hom.app _ (z l) =
      c.pt.obj.map (g l).op s := by
    rw [← ht' l, ← c.w A]
    rfl
  have hA (kl : Fin n × Fin n) :
      (F.obj k).obj.map (pullback.fst (g kl.1) (g kl.2)).op (z kl.1) =
        (F.obj k).obj.map (pullback.snd (g kl.1) (g kl.2)).op (z kl.2) := by
    have e (l : Fin n) (r : pullback (g kl.1) (g kl.2) ⟶ U l) :
        (F.obj k).obj.map r.op (z l) =
          (F.map (b' kl)).hom.app _ ((F.map (a' kl)).hom.app _
            ((F.obj i).obj.map r.op (t' l))) := by
      change (F.obj k).obj.map r.op ((F.map A).hom.app _ (t' l)) = _
      rw [← hb' kl, F.map_comp]
      exact (NatTrans.naturality_apply (F.map (a' kl) ≫ F.map (b' kl)).hom r.op (t' l)).symm
    rw [e, e, ha' kl]
  obtain ⟨y, hy, _⟩ := ((Presieve.isSheafFor_arrows_iff_pullbacks _ g).mp
    (abelian_isSheafFor (F.obj k) g hcover)) z fun i j ↦ hA (i, j)
  refine ⟨k, y, (abelian_isSheafFor c.pt g hcover).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨l⟩
  change c.pt.obj.map _ _ = c.pt.obj.map _ _
  rw [← hz l]
  erw [← hy l]
  exact (NatTrans.naturality_apply (c.ι.app k).hom (g l).op y).symm

private noncomputable def abelian_sections_isColimit
    {S : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
    (c : Cocone F) (hc : IsColimit c) (W : S.ProEt)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    IsColimit (((sheafSections (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}).obj
      (op W)).mapCocone c) := by
  have : ReflectsColimit
      (F ⋙ (sheafSections (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}).obj (op W))
      (forget AddCommGrpCat.{u + 1}) := reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget AddCommGrpCat.{u + 1})
  apply Types.FilteredColimit.isColimitOf'
  · intro s
    obtain ⟨i, t, ht⟩ := abelian_section_lift F c hc s
    exact ⟨i, t, ht.symm⟩
  · intro i s t h
    exact abelian_eventual_equality F c hc s t h

private noncomputable def hom_section_equiv
    {S : Scheme.{u}} (A : Sheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1})
    (P Q : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) :
    (P ⟶ Q) ≃ (SheafOfModules.homObj P Q).val.obj (op (Scheme.ProEt.mk (𝟙 S))) where
  toFun f := (PresheafOfModules.restrictOver A.obj (Scheme.ProEt.mk (𝟙 S))).map f.val
  invFun f := ⟨{
    app W := f.app (op (Over.mk (MorphismProperty.Over.homMk W.unop.hom
      (Category.comp_id _) : W.unop ⟶ Scheme.ProEt.mk (𝟙 S))))
    naturality {W Z} a := by
      let w : W.unop ⟶ Scheme.ProEt.mk (𝟙 S) :=
        MorphismProperty.Over.homMk W.unop.hom (Category.comp_id _)
      let z : Z.unop ⟶ Scheme.ProEt.mk (𝟙 S) :=
        MorphismProperty.Over.homMk Z.unop.hom (Category.comp_id _)
      let b : Over.mk z ⟶ Over.mk w := Over.homMk a.unop (by
        apply MorphismProperty.Over.Hom.ext
        exact MorphismProperty.Over.w a.unop)
      exact f.naturality b.op }⟩
  left_inv _ := rfl
  right_inv f := by
    apply PresheafOfModules.hom_ext
    intro W
    have h : (MorphismProperty.Over.homMk W.unop.left.hom (Category.comp_id _) :
        W.unop.left ⟶ Scheme.ProEt.mk (𝟙 S)) = W.unop.hom := by
      apply (MorphismProperty.Over.mkIdTerminal @WeaklyEtale S).hom_ext
    exact congrArg (fun g : W.unop.left ⟶ Scheme.ProEt.mk (𝟙 S) ↦
      (show P.val.obj (op W.unop.left) ⟶ Q.val.obj (op W.unop.left) from
        f.app (op (Over.mk g)))) h

set_option backward.isDefEq.respectTransparency false in
private noncomputable def hom_section_iso
    {S : Scheme.{u}} (A : Sheaf (Scheme.ProEt.topology S) CommRingCat.{u + 1})
    (P : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) :
    coyoneda.obj (op P) ≅ (SheafOfModules.homFunctor A).obj (op P) ⋙
      SheafOfModules.toSheaf _ ⋙
      (sheafSections (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}).obj
        (op (Scheme.ProEt.mk (𝟙 S))) ⋙ forget AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents (fun Q ↦ (hom_section_equiv A P Q).toIso) (by
    intro Q Q' f
    ext g
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    rfl)

/-- Source: Stacks Project, Tags 0738 (4), 0GMZ, 0GN0 and 098D
(auxiliary; not a blueprint node).
Sections over a qcqs scheme and Hom from a locally finitely presented module commute
with filtered sheaf colimits. Both comparisons use the chosen colimit coprojections;
equality of representatives is witnessed at a common stage.

Proof: A covering of a qcqs object has a finite affine refinement. Mathlib supplies
pullbacks in the pro-etale site, and their scheme pullbacks are qcqs. A sheaf colimit
is the sheafification of the presheaf colimit, so its sections locally have stage
representatives, and equal images are locally eventually equal. Finite covering
refinements and filtered cocones make the latter equalities hold at one stage;
sheaf separation proves global eventual equality. Move finitely many local section
lifts to one stage, impose equality on the finitely many qcqs overlaps, and glue.
This proves that section evaluation preserves the colimit, including for empty covers.

For modules, internal Hom from a locally finitely presented sheaf preserves filtered
colimits by the site-level finite-presentation theorem. Forgetting to abelian sheaves
preserves colimits. Applying the section result at the terminal object therefore
proves preservation for global Hom, which is naturally the sections of internal Hom.
Mathlib's filtered-colimit representative theorem gives the two eventual-equality
assertions with the specified coprojections. -/
theorem proetale_qcqs_fp_section_calculus
    (X : Scheme.{u}) (V : X.ProEt)
    [CompactSpace V.left] [QuasiSeparatedSpace V.left]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    (∀ F : I ⥤ Sheaf (Scheme.ProEt.topology V.left) AddCommGrpCat.{u + 1},
      Function.Bijective (colimit.post F
        ((sheafSections (Scheme.ProEt.topology V.left) AddCommGrpCat.{u + 1}).obj
          (op (Scheme.ProEt.mk (𝟙 V.left))))) ∧
      (∀ (i j : I)
        (s : (F.obj i).obj.obj (op (Scheme.ProEt.mk (𝟙 V.left))))
        (t : (F.obj j).obj.obj (op (Scheme.ProEt.mk (𝟙 V.left)))),
        ((colimit.ι F i).hom.app (op (Scheme.ProEt.mk (𝟙 V.left)))) s =
            ((colimit.ι F j).hom.app (op (Scheme.ProEt.mk (𝟙 V.left)))) t ↔
          ∃ (k : I) (a : i ⟶ k) (b : j ⟶ k),
            ((F.map a).hom.app (op (Scheme.ProEt.mk (𝟙 V.left)))) s =
              ((F.map b).hom.app (op (Scheme.ProEt.mk (𝟙 V.left)))) t)) ∧
    (∀ (A : Sheaf (Scheme.ProEt.topology V.left) CommRingCat.{u + 1})
      (P : ringedSiteModules.{u + 1}
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))
      [SheafOfModules.IsFinitePresentation.{u + 1, u, u + 1} P]
      (N : I ⥤ ringedSiteModules.{u + 1}
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)),
      Function.Bijective (colimit.post N (coyoneda.obj (op P))) ∧
        (∀ (i j : I) (f : P ⟶ N.obj i) (g : P ⟶ N.obj j),
          f ≫ colimit.ι N i = g ≫ colimit.ι N j ↔
            ∃ (k : I) (a : i ⟶ k) (b : j ⟶ k), f ≫ N.map a = g ≫ N.map b)) := by
  constructor
  · intro F
    let E := (sheafSections (Scheme.ProEt.topology V.left) AddCommGrpCat.{u + 1}).obj
      (op (Scheme.ProEt.mk (𝟙 V.left)))
    have : CompactSpace (Scheme.ProEt.mk (𝟙 V.left)).left :=
      inferInstanceAs (CompactSpace V.left)
    have : QuasiSeparatedSpace (Scheme.ProEt.mk (𝟙 V.left)).left :=
      inferInstanceAs (QuasiSeparatedSpace V.left)
    have h := abelian_sections_isColimit F (colimit.cocone F) (colimit.isColimit F)
      (Scheme.ProEt.mk (𝟙 V.left))
    have hi : IsIso (colimit.post F E) :=
      (colimit.isColimit (F ⋙ E)).nonempty_isColimit_iff_isIso_desc.mp ⟨h⟩
    exact ⟨(ConcreteCategory.isIso_iff_bijective _).mp hi, fun i j s t ↦ h.eq_iff _⟩
  · intro A P _ N
    let H := (SheafOfModules.homFunctor A).obj (op P)
    have : PreservesColimit N H :=
      SheafOfModules.internalHom_preserves_filteredColimit_of_isFinitePresentation A P I N
    let R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A
    have : PreservesColimitsOfShape I (SheafOfModules.toSheaf R) :=
      ((moduleSheaves_colimits_forgetful.{u + 1, u, u + 1, u + 1} R).2.2.2.2.2 I).2.1
    let T := Scheme.ProEt.mk (𝟙 V.left)
    have : CompactSpace T.left := inferInstanceAs (CompactSpace V.left)
    have : QuasiSeparatedSpace T.left := inferInstanceAs (QuasiSeparatedSpace V.left)
    let E := (sheafSections (Scheme.ProEt.topology V.left) AddCommGrpCat.{u + 1}).obj (op T)
    let D := (N ⋙ H) ⋙ SheafOfModules.toSheaf R
    have : PreservesColimit D E := preservesColimit_of_preserves_colimit_cocone
      (colimit.isColimit D)
      (abelian_sections_isColimit D (colimit.cocone D) (colimit.isColimit D) T)
    have : PreservesColimit (N ⋙ H) (SheafOfModules.toSheaf R) := inferInstance
    have : PreservesColimit ((N ⋙ H) ⋙ SheafOfModules.toSheaf R) E :=
      inferInstanceAs (PreservesColimit D E)
    have : PreservesColimit (N ⋙ H) (SheafOfModules.toSheaf R ⋙ E) := inferInstance
    have : PreservesColimit N (H ⋙ SheafOfModules.toSheaf R ⋙ E) := inferInstance
    have : PreservesColimit (N ⋙ H ⋙ SheafOfModules.toSheaf R) E := by
      rw [← Functor.assoc]
      infer_instance
    have : PreservesColimit N (H ⋙ SheafOfModules.toSheaf R ⋙ E ⋙
        forget AddCommGrpCat.{u + 1}) := inferInstance
    have : PreservesColimit N (coyoneda.obj (op P)) :=
      preservesColimit_of_natIso N (hom_section_iso A P).symm
    refine ⟨(ConcreteCategory.isIso_iff_bijective (colimit.post N (coyoneda.obj (op P)))).mp
      inferInstance, ?_⟩
    intro i j f g
    exact Types.FilteredColimit.isColimit_eq_iff _
      (isColimitOfPreserves (coyoneda.obj (op P)) (colimit.isColimit N))

end AlgebraicGeometry
