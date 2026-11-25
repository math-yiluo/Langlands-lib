/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.Mathlib.CategoryTheory.Filtered.Basic

/-!
# Sections over quasi-compact objects commute with filtered colimits

Let `X` be a scheme and `c` a colimit of a filtered diagram `F : K ⥤ Sh(X_ét, Λ-Mod)` of étale
sheaves of `Λ`-modules. For an étale `X`-scheme `W` with quasi-compact underlying space, two
sections of some `F k` over `W` with the same image in `c.pt` agree in a later `F k'`
(`AlgebraicGeometry.Scheme.exists_map_eq_of_isColimit`). If `W` is moreover quasi-separated,
every section of `c.pt` over `W` comes from some `F k`
(`AlgebraicGeometry.Scheme.exists_app_eq_of_isColimit`). Together: sections over a
quasi-compact quasi-separated `W` commute with filtered colimits (Stacks 0738).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] {K : Type u} [SmallCategory K]
  [IsFiltered K] {F : K ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {c : Cocone F}

/-- The forgetful functor of `ModuleCat.{u + 1} Λ` preserves colimits of `u`-small filtered
diagrams. -/
instance (L : K ⥤ ModuleCat.{u + 1} Λ) : PreservesColimit L (CategoryTheory.forget _) :=
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  inferInstance

/-- A jointly surjective family of morphisms of étale `X`-schemes is a covering family for
every étale sheaf of `Λ`-modules. -/
lemma isSheafFor_ofArrows_moduleCat (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {W : X.Etale} {κ : Type*} {U : κ → X.Etale} (g : ∀ a, U a ⟶ W)
    (hg : ⋃ a, Set.range (g a).left = Set.univ) :
    Presieve.IsSheafFor (G.obj ⋙ CategoryTheory.forget _) (Presieve.ofArrows U g) := by
  have := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ G.obj (CategoryTheory.forget (ModuleCat.{u + 1} Λ))
      G.property)
  rw [Presieve.isSheafFor_iff_generate]
  exact this _ ((ofArrows_mem_smallEtaleTopology_iff g).2 hg)

omit [IsFiltered K] in
/-- The presheaf colimit of a diagram of sheaves, with its comparison map to the sheaf colimit:
the comparison is locally surjective and locally injective, being the sheafification map. -/
lemma exists_presheafColimit (hc : IsColimit c) :
    ∃ (E : Cocone (F ⋙ sheafToPresheaf _ _)) (_ : IsColimit E) (φ : E.pt ⟶ c.pt.obj),
      Presheaf.IsLocallySurjective X.smallEtaleTopology φ ∧
      Presheaf.IsLocallyInjective X.smallEtaleTopology φ ∧
      ∀ k, E.ι.app k ≫ φ = (c.ι.app k).hom := by
  let E := colimit.cocone (F ⋙ sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let hE : IsColimit E := colimit.isColimit _
  let e := (Sheaf.isColimitSheafifyCocone E hE).coconePointUniqueUpToIso hc
  refine ⟨E, hE, toSheafify _ E.pt ≫ e.hom.hom, ?_, ?_, fun k ↦ ?_⟩
  · infer_instance
  · infer_instance
  · rw [← Category.assoc, ← Sheaf.sheafifyCocone_ι_app_val,
      ← ObjectProperty.FullSubcategory.comp_hom,
      IsColimit.comp_coconePointUniqueUpToIso_hom]

/-- **Sections of a filtered colimit are locally lifted.** Every section of `c.pt` over `W` is,
on the members of a covering sieve of `W`, the image of a section of some `F k`. -/
lemma exists_mem_forall_exists_app_eq (hc : IsColimit c) {W : X.Etale}
    (s : c.pt.obj.obj (op W)) :
    ∃ R ∈ X.smallEtaleTopology W, ∀ ⦃V : X.Etale⦄ (f : V ⟶ W), R f →
      ∃ (k : K) (t : (F.obj k).obj.obj (op V)),
        (c.ι.app k).hom.app (op V) t = c.pt.obj.map f.op s := by
  obtain ⟨E, hE, φ, hs, -, hφ⟩ := exists_presheafColimit hc
  refine ⟨_, Presheaf.imageSieve_mem _ φ s, fun V f ⟨p, hp⟩ ↦ ?_⟩
  have hEV := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj (op V)) hE
  obtain ⟨k, t, rfl⟩ := Concrete.isColimit_exists_rep _ hEV p
  refine ⟨k, t, Eq.trans ?_ hp⟩
  rw [← hφ k]
  rfl

/-- **Sections of a filtered colimit are locally separated.** Two sections of `F k` over `W`
with the same image in `c.pt` agree, on the members of a covering sieve of `W`, in some later
`F k'`. -/
lemma exists_mem_forall_exists_map_eq (hc : IsColimit c) {W : X.Etale} {k : K}
    (t t' : (F.obj k).obj.obj (op W))
    (h : (c.ι.app k).hom.app (op W) t = (c.ι.app k).hom.app (op W) t') :
    ∃ R ∈ X.smallEtaleTopology W, ∀ ⦃V : X.Etale⦄ (f : V ⟶ W), R f →
      ∃ (k' : K) (a : k ⟶ k'),
        (F.map a).hom.app (op V) ((F.obj k).obj.map f.op t) =
          (F.map a).hom.app (op V) ((F.obj k).obj.map f.op t') := by
  obtain ⟨E, hE, φ, -, hi, hφ⟩ := exists_presheafColimit hc
  have h' : φ.app (op W) ((E.ι.app k).app (op W) t) =
      φ.app (op W) ((E.ι.app k).app (op W) t') := by
    change (E.ι.app k ≫ φ).app _ t = (E.ι.app k ≫ φ).app _ t'
    rw [hφ]
    exact h
  refine ⟨_, Presheaf.equalizerSieve_mem _ φ _ _ h', fun V f hf ↦ ?_⟩
  have hEV := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj (op V)) hE
  have hf' : (E.ι.app k).app (op V) ((F.obj k).obj.map f.op t) =
      (E.ι.app k).app (op V) ((F.obj k).obj.map f.op t') := by
    have hn := (E.ι.app k).naturality f.op
    have e1 := ConcreteCategory.congr_hom hn t
    have e2 := ConcreteCategory.congr_hom hn t'
    simp only [ConcreteCategory.comp_apply] at e1 e2
    erw [e1, e2]
    exact hf
  obtain ⟨k', a, b, hab⟩ := Concrete.isColimit_exists_of_rep_eq _ hEV _ _ hf'
  refine ⟨_, a ≫ IsFiltered.coeqHom a b, ?_⟩
  let q := IsFiltered.coeqHom a b
  calc (F.map (a ≫ q)).hom.app (op V) ((F.obj k).obj.map f.op t)
      = (F.map q).hom.app (op V) ((F.map a).hom.app (op V) ((F.obj k).obj.map f.op t)) := by
        rw [F.map_comp]; rfl
    _ = (F.map q).hom.app (op V) ((F.map b).hom.app (op V) ((F.obj k).obj.map f.op t')) :=
        congrArg _ hab
    _ = (F.map (b ≫ q)).hom.app (op V) ((F.obj k).obj.map f.op t') := by
        rw [F.map_comp]; rfl
    _ = _ := by rw [← IsFiltered.coeq_condition a b]

/-- **Sections over a quasi-compact `W` of a filtered colimit are separated at a finite stage.**
Two sections of `F k` over `W` with the same image in `c.pt` agree in some later `F k'`. -/
theorem exists_map_eq_of_isColimit (hc : IsColimit c) {W : X.Etale} [CompactSpace W.left]
    {k : K} (t t' : (F.obj k).obj.obj (op W))
    (h : (c.ι.app k).hom.app (op W) t = (c.ι.app k).hom.app (op W) t') :
    ∃ (k' : K) (a : k ⟶ k'), (F.map a).hom.app (op W) t = (F.map a).hom.app (op W) t' := by
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_map_eq hc t t' h
  obtain ⟨n, U, g, hRg, -, hcov⟩ := (AlgebraicGeometry.Etale.exists_affine_refinement _) hR
  choose k₁ a₁ ha₁ using fun i ↦ hloc (g i) (hRg i)
  obtain ⟨k', A, b, hb⟩ := IsFiltered.exists_comp_eq_of_finite a₁
  refine ⟨k', A, (isSheafFor_ofArrows_moduleCat (F.obj k') g hcov).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨i⟩
  change (F.obj k').obj.map (g i).op _ = (F.obj k').obj.map (g i).op _
  have hnat (z : (F.obj k).obj.obj (op W)) : (F.obj k').obj.map (g i).op ((F.map A).hom.app _ z) =
      (F.map (b i)).hom.app _ ((F.map (a₁ i)).hom.app _ ((F.obj k).obj.map (g i).op z)) := by
    rw [← hb i, F.map_comp]
    exact (NatTrans.naturality_apply (F.map (a₁ i) ≫ F.map (b i)).hom (g i).op z).symm
  rw [hnat, hnat, ha₁ i]

/-- **Sections over a quasi-compact quasi-separated `W` of a filtered colimit come from a finite
stage.** Every section of `c.pt` over `W` is the image of a section of some `F k` (Stacks 0738).
-/
theorem exists_app_eq_of_isColimit (hc : IsColimit c) {W : X.Etale} [CompactSpace W.left]
    [QuasiSeparatedSpace W.left] (s : c.pt.obj.obj (op W)) :
    ∃ (k : K) (t : (F.obj k).obj.obj (op W)), (c.ι.app k).hom.app (op W) t = s := by
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_app_eq hc s
  obtain ⟨n, U, g, hRg, hU, hcov⟩ := (AlgebraicGeometry.Etale.exists_affine_refinement _) hR
  choose k₁ t₁ ht₁ using fun i ↦ hloc (g i) (hRg i)
  obtain ⟨k, ⟨b⟩⟩ := IsFiltered.exists_cocone_of_finite k₁
  let t₂ (i : Fin n) : (F.obj k).obj.obj (op (U i)) := (F.map (b i)).hom.app _ (t₁ i)
  have ht₂ (i : Fin n) : (c.ι.app k).hom.app _ (t₂ i) = c.pt.obj.map (g i).op s := by
    rw [← ht₁ i, ← c.w (b i)]
    rfl
  -- on the overlaps the local lifts agree at a later stage
  have hpair (ij : Fin n × Fin n) : ∃ (k' : K) (a : k ⟶ k'),
      (F.map a).hom.app _ ((F.obj k).obj.map (pullback.fst (g ij.1) (g ij.2)).op (t₂ ij.1)) =
        (F.map a).hom.app _ ((F.obj k).obj.map (pullback.snd (g ij.1) (g ij.2)).op
          (t₂ ij.2)) := by
    have := hU ij.1
    have := hU ij.2
    obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_pullback (g ij.1) (g ij.2)
    refine exists_map_eq_of_isColimit hc _ _ ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ht₂, ht₂]
    change c.pt.obj.map _ (c.pt.obj.map _ s) = c.pt.obj.map _ (c.pt.obj.map _ s)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, pullback.condition]
  choose k₂ a₂ ha₂ using hpair
  obtain ⟨k', A, b', hb'⟩ := IsFiltered.exists_comp_eq_of_finite a₂
  let z (i : Fin n) : (F.obj k').obj.obj (op (U i)) := (F.map A).hom.app _ (t₂ i)
  have hz (i : Fin n) : (c.ι.app k').hom.app _ (z i) = c.pt.obj.map (g i).op s := by
    rw [← ht₂ i, ← c.w A]
    rfl
  have hA (ij : Fin n × Fin n) :
      (F.obj k').obj.map (pullback.fst (g ij.1) (g ij.2)).op (z ij.1) =
        (F.obj k').obj.map (pullback.snd (g ij.1) (g ij.2)).op (z ij.2) := by
    have e (j : Fin n) (r : pullback (g ij.1) (g ij.2) ⟶ U j) :
        (F.obj k').obj.map r.op (z j) =
          (F.map (b' ij)).hom.app _
            ((F.map (a₂ ij)).hom.app _ ((F.obj k).obj.map r.op (t₂ j))) := by
      change (F.obj k').obj.map r.op ((F.map A).hom.app _ (t₂ j)) = _
      rw [← hb' ij, F.map_comp]
      exact (NatTrans.naturality_apply (F.map (a₂ ij) ≫ F.map (b' ij)).hom r.op (t₂ j)).symm
    rw [e, e, ha₂ ij]
  obtain ⟨y, hy, -⟩ := ((Presieve.isSheafFor_arrows_iff_pullbacks _ g).1
    (isSheafFor_ofArrows_moduleCat (F.obj k') g hcov)) z fun i j ↦ hA (i, j)
  refine ⟨k', y, (isSheafFor_ofArrows_moduleCat c.pt g hcov).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨i⟩
  change c.pt.obj.map _ _ = c.pt.obj.map _ _
  rw [← hz i]
  erw [← hy i]
  exact (NatTrans.naturality_apply (c.ι.app k').hom (g i).op y).symm

/-- **Sections over a quasi-compact quasi-separated `W` commute with filtered colimits** (Stacks
0738): the image of a colimit cocone of a `u`-small filtered diagram of étale sheaves of
`Λ`-modules under the sections functor over `W` is a colimit cocone. -/
noncomputable def isColimitSheafSectionsMapCocone (hc : IsColimit c) (W : X.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    IsColimit (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op W)).mapCocone
      c) := by
  have : ReflectsColimit (F ⋙ (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op W))
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) := reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun s ↦ ?_) (fun k t t' h ↦ ?_)
  · obtain ⟨k, t, ht⟩ := exists_app_eq_of_isColimit hc s
    exact ⟨k, t, ht.symm⟩
  · exact exists_map_eq_of_isColimit hc t t' h

/-- The sections functor over a quasi-compact quasi-separated étale `X`-scheme preserves
colimits of `u`-small filtered diagrams. -/
instance preservesFilteredColimitsOfSize_sheafSections (W : X.Etale) [CompactSpace W.left]
    [QuasiSeparatedSpace W.left] :
    PreservesFilteredColimitsOfSize.{u, u}
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op W)) where
  preserves_filtered_colimits _ _ _ :=
    ⟨fun {_} ↦ ⟨fun {_} hc ↦ ⟨isColimitSheafSectionsMapCocone hc W⟩⟩⟩

end AlgebraicGeometry.Scheme
