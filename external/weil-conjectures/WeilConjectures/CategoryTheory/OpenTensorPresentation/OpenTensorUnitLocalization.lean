/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorPresentation
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement

/-! # Localization of the open tensor unit equation

The two representative squares transport the unit equation from complexes to
K-flat derived inputs. Source: Stacks 015F and 0GL1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.OpenTensorPresentation

private theorem exact_unit
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    {E : A ⥤ B} {R : B ⥤ A} [E.Additive] [R.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (adj : E ⊣ R)
    (P : CochainComplex A ℤ) :
    adj.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj P) ≫
        R.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app P) ≫
        R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  unfold Adjunction.mapExactDerivedCategory
  rw [Adjunction.localization_unit_app]
  simp only [Iso.symm_hom, CatCommSq.iso, Category.assoc]
  rw [← R.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  simp

attribute [local instance] OpenTensorPresentation.e_add OpenTensorPresentation.r_add
  OpenTensorPresentation.e_lim OpenTensorPresentation.e_colim
  OpenTensorPresentation.r_lim OpenTensorPresentation.r_colim

variable {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
  (c : OpenTensorPresentation A B) (adj : c.E ⊣ c.R)

/-- The representative squares preserve the unit equation on K-flat inputs.
Source: Stacks 015F and 0GL1 (blueprint: lem-sf-open-tensor-unit-localization).
Proof: postcompose the derived unit equation with the exact-functor factors
and the open tensor model. The representative square replaces gamma by the
localized total map; the restriction square replaces rho by the localized
restriction map. Naturality of the model and the localized adjunction unit
reduce the result to the given equation on complexes. All postcomposed maps
are isomorphisms, so cancellation gives the desired equality. -/
private theorem unit_on_models
    (P : CochainComplex A ℤ) (T : CochainComplex B ℤ)
    (hP : c.flatA P) (hT : c.flatB T)
    (htotal :
      (c.TA.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)).app
          ((c.R.mapHomologicalComplex (.up ℤ)).obj T) ≫
        (c.totalRestriction ((c.E.mapHomologicalComplex (.up ℤ)).obj P) T).inv ≫
        (c.R.mapHomologicalComplex (.up ℤ)).map (c.totalGamma P T).hom =
      (adj.mapHomologicalComplex (.up ℤ)).unit.app
        ((c.TA.obj P).obj ((c.R.mapHomologicalComplex (.up ℤ)).obj T)))
    (hnat :
      c.DA.map (Prod.mkHom
          (DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P))
          (𝟙 (DerivedCategory.Q.obj ((c.R.mapHomologicalComplex (.up ℤ)).obj T)))) ≫
        (c.modelA _ _ (c.hR _ (c.hE P hP)) (c.hR T hT)).hom =
      (c.modelA P _ hP (c.hR T hT)).hom ≫ DerivedCategory.Q.map
        ((c.TA.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)).app
          ((c.R.mapHomologicalComplex (.up ℤ)).obj T))) :
    adj.mapExactDerivedCategory.homEquiv _ _
        (c.gamma.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) =
      c.DA.map (Prod.mkHom
          (adj.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj P)) (𝟙 _)) ≫
        c.restriction.inv.app (c.E.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
          DerivedCategory.Q.obj T) := by
  let E := c.E.mapDerivedCategory
  let R := c.R.mapDerivedCategory
  let EP := (c.E.mapHomologicalComplex (.up ℤ)).obj P
  let RT := (c.R.mapHomologicalComplex (.up ℤ)).obj T
  let C := (c.TA.obj P).obj RT
  let D := (c.TB.obj EP).obj T
  let a := adj.mapExactDerivedCategory
  let e : E.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj EP :=
    c.E.mapDerivedCategoryFactors.app P
  let r : R.obj (DerivedCategory.Q.obj T) ≅ DerivedCategory.Q.obj RT :=
    c.R.mapDerivedCategoryFactors.app T
  let er : R.obj (DerivedCategory.Q.obj EP) ≅
      DerivedCategory.Q.obj ((c.R.mapHomologicalComplex (.up ℤ)).obj EP) :=
    c.R.mapDerivedCategoryFactors.app EP
  let α := c.DA.mapIso ((Iso.refl (DerivedCategory.Q.obj P)).prod r) ≪≫
    c.modelA P RT hP (c.hR T hT)
  let β := c.DB.mapIso (e.prod (Iso.refl (DerivedCategory.Q.obj T))) ≪≫
    c.modelB EP T (c.hE P hP) hT
  let δ := c.DA.mapIso (((R.mapIso e) ≪≫ er).prod r) ≪≫
    c.modelA ((c.R.mapHomologicalComplex (.up ℤ)).obj EP) RT
      (c.hR EP (c.hE P hP)) (c.hR T hT)
  have hg : c.gamma.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≫
      E.map α.hom ≫ c.E.mapDerivedCategoryFactors.hom.app C =
    β.hom ≫ DerivedCategory.Q.map (c.totalGamma P T).hom := by
    simpa only [E, α, β, e, r, EP, RT, C, Iso.trans_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Iso.app_hom, Functor.map_comp, Category.assoc,
      Functor.id_obj]
      using c.model P T hP hT
  have hr : c.restriction.hom.app (E.obj (DerivedCategory.Q.obj P),
        DerivedCategory.Q.obj T) ≫ δ.hom =
      R.map β.hom ≫ c.R.mapDerivedCategoryFactors.hom.app D ≫
        DerivedCategory.Q.map (c.totalRestriction EP T).hom := by
    have hn := c.restriction.hom.naturality
      (Prod.mkHom e.hom (𝟙 (DerivedCategory.Q.obj T)))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.comp_obj] at hn
    have hm := c.restriction_model EP T (c.hE P hP) hT
    dsimp only [OpenTensorRestrictionNormalization] at hm
    simp only [δ, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom]
    simp only [Functor.map_id] at hn
    have heq : Prod.mkHom (R.map e.hom ≫ er.hom) r.hom =
        Prod.mkHom (R.map e.hom) (𝟙 _) ≫ Prod.mkHom er.hom r.hom := by
      ext <;> simp
    rw [heq, c.DA.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc _ _ (c.DA.map (Prod.mkHom er.hom r.hom) ≫ _), ← hn]
    simp only [Category.assoc]
    dsimp only [er, r, RT]
    simp only [Iso.app_hom]
    rw [hm]
    simp only [β, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.refl_hom, Functor.map_comp, Category.assoc, e, R, D, Iso.app_hom]
  have hu : c.DA.map (Prod.mkHom (a.unit.app (DerivedCategory.Q.obj P))
        (𝟙 (R.obj (DerivedCategory.Q.obj T)))) ≫ δ.hom =
      α.hom ≫ DerivedCategory.Q.map
        ((c.TA.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)).app RT) := by
    simp only [δ, α, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
    rw [← c.DA.map_comp_assoc]
    have heq : Prod.mkHom (a.unit.app (DerivedCategory.Q.obj P)) (𝟙 _) ≫
        Prod.mkHom (R.map e.hom ≫ er.hom) r.hom =
      Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) r.hom ≫
        Prod.mkHom
          (DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P))
          (𝟙 (DerivedCategory.Q.obj RT)) := by
      ext
      · change a.unit.app (DerivedCategory.Q.obj P) ≫
            (R.map e.hom ≫ er.hom) =
          𝟙 (DerivedCategory.Q.obj P) ≫
            DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)
        simpa only [Category.id_comp, a, R, e, er, Iso.app_hom, Category.assoc]
          using exact_unit adj P
      · change 𝟙 _ ≫ r.hom = r.hom ≫ 𝟙 _
        simp
    rw [heq, c.DA.map_comp, Category.assoc, hnat]
    simp only [RT, Category.assoc]
  rw [Adjunction.homEquiv_unit]
  change a.unit.app (c.DA.obj (DerivedCategory.Q.obj P, R.obj (DerivedCategory.Q.obj T))) ≫
      R.map (c.gamma.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) =
    c.DA.map (Prod.mkHom (a.unit.app (DerivedCategory.Q.obj P))
        (𝟙 (R.obj (DerivedCategory.Q.obj T)))) ≫
      c.restriction.inv.app (E.obj (DerivedCategory.Q.obj P), DerivedCategory.Q.obj T)
  apply (cancel_mono (R.map (c.gamma.hom.app
    (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)))).1
  simp only [Category.assoc, ← R.map_comp, Iso.inv_hom_id_app]
  erw [R.map_id, Category.comp_id]
  apply (cancel_mono (R.map (E.map α.hom ≫
    c.E.mapDerivedCategoryFactors.hom.app C) ≫
      c.R.mapDerivedCategoryFactors.hom.app
        ((c.E.mapHomologicalComplex (.up ℤ)).obj C))).1
  simp only [Category.assoc]
  have hη := a.unit.naturality α.hom
  dsimp only [Functor.id_map, Functor.comp_map] at hη
  change α.hom ≫ a.unit.app (DerivedCategory.Q.obj C) =
    a.unit.app (c.DA.obj (DerivedCategory.Q.obj P, R.obj (DerivedCategory.Q.obj T))) ≫
      R.map (E.map α.hom) at hη
  have huC := exact_unit adj C
  have hri : c.restriction.inv.app (E.obj (DerivedCategory.Q.obj P),
        DerivedCategory.Q.obj T) ≫ R.map β.hom ≫
          c.R.mapDerivedCategoryFactors.hom.app D =
      δ.hom ≫ DerivedCategory.Q.map (c.totalRestriction EP T).inv := by
    apply (cancel_mono (DerivedCategory.Q.map (c.totalRestriction EP T).hom)).1
    simp only [Category.assoc, ← DerivedCategory.Q.map_comp, Iso.inv_hom_id,
      DerivedCategory.Q.map_id, Category.comp_id]
    rw [← hr, Iso.inv_hom_id_app_assoc]
  calc
    a.unit.app _ ≫ (R.map (E.map α.hom ≫
        c.E.mapDerivedCategoryFactors.hom.app C) ≫
          c.R.mapDerivedCategoryFactors.hom.app
            ((c.E.mapHomologicalComplex (.up ℤ)).obj C)) =
        α.hom ≫ DerivedCategory.Q.map
          ((adj.mapHomologicalComplex (.up ℤ)).unit.app C) := by
      rw [R.map_comp]
      simp only [Category.assoc]
      rw [← Category.assoc _ _ (R.map (c.E.mapDerivedCategoryFactors.hom.app C) ≫ _),
        ← hη]
      simpa only [Category.assoc] using congrArg (α.hom ≫ ·) huC
    _ = α.hom ≫ DerivedCategory.Q.map
        ((c.TA.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)).app RT) ≫
        DerivedCategory.Q.map (c.totalRestriction EP T).inv ≫
        DerivedCategory.Q.map ((c.R.mapHomologicalComplex (.up ℤ)).map
          (c.totalGamma P T).hom) := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun f ↦ α.hom ≫ DerivedCategory.Q.map f) htotal.symm
    _ = c.DA.map (Prod.mkHom (a.unit.app (DerivedCategory.Q.obj P)) (𝟙 _)) ≫
        c.restriction.inv.app (E.obj (DerivedCategory.Q.obj P),
          DerivedCategory.Q.obj T) ≫
        R.map (c.gamma.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
        (R.map (E.map α.hom ≫ c.E.mapDerivedCategoryFactors.hom.app C) ≫
          c.R.mapDerivedCategoryFactors.hom.app
            ((c.E.mapHomologicalComplex (.up ℤ)).obj C)) := by
      rw [← Category.assoc α.hom, ← hu]
      simp only [Category.assoc, R.map_comp]
      rw [← R.map_comp_assoc, ← R.map_comp_assoc]
      simp only [Category.assoc]
      rw [hg, R.map_comp]
      have hn := c.R.mapDerivedCategoryFactors.hom.naturality (c.totalGamma P T).hom
      dsimp only [Functor.comp_map] at hn
      simp only [Category.assoc]
      erw [hn]
      simpa only [Category.assoc] using
        congrArg (fun f ↦
          c.DA.map (Prod.mkHom (a.unit.app (DerivedCategory.Q.obj P))
            (𝟙 (R.obj (DerivedCategory.Q.obj T)))) ≫ f ≫
              DerivedCategory.Q.map ((c.R.mapHomologicalComplex (.up ℤ)).map
                (c.totalGamma P T).hom)) hri.symm

private theorem normalization_of_dense_inputs
    {A' B' : Type a} [Category.{b} A'] [Category.{b} B']
    (E : A' ⥤ B') (R : B' ⥤ A') (TA : A' × A' ⥤ A') (TB : B' × B' ⥤ B')
    (a : E ⊣ R) (rho : TB ⋙ R ≅ R.prod R ⋙ TA)
    (gamma : E.prod (𝟭 B') ⋙ TB ≅ (𝟭 A').prod R ⋙ TA ⋙ E)
    (P : A' → Prop) (T : B' → Prop)
    (hP : ∀ M, ∃ M', P M' ∧ Nonempty (M' ≅ M))
    (hT : ∀ N, ∃ N', T N' ∧ Nonempty (N' ≅ N))
    (h : ∀ M N, P M → T N → a.homEquiv _ _ (gamma.inv.app (M, N)) =
      TA.map (Prod.mkHom (a.unit.app M) (𝟙 _)) ≫ rho.inv.app (E.obj M, N)) :
    OpenTensorUnitNormalization E R TA TB a rho gamma := by
  let V := (𝟭 A').prod R ⋙ TA
  let W := E.prod (𝟭 B') ⋙ TB ⋙ R
  let L : V ⟶ W := Functor.whiskerLeft V a.unit ≫ Functor.whiskerRight gamma.inv R
  let eta : V ⟶ E.prod (𝟭 B') ⋙ R.prod R ⋙ TA :=
    { app X := TA.map (Prod.mkHom (a.unit.app X.1) (𝟙 _))
      naturality := by
        intro X Y f
        dsimp only [V, Functor.comp_map, Functor.prod_map, Functor.id_map]
        rw [← TA.map_comp, ← TA.map_comp]
        congr 1
        ext
        · exact a.unit.naturality f.1
        · simp }
  let H : V ⟶ W := eta ≫ Functor.whiskerLeft (E.prod (𝟭 B')) rho.inv
  intro M N
  obtain ⟨M', hM', ⟨e⟩⟩ := hP M
  obtain ⟨N', hN', ⟨f⟩⟩ := hT N
  have hm : L.app (M', N') = H.app (M', N') := h M' N' hM' hN'
  have heq : L.app (M, N) = H.app (M, N) := by
    apply (cancel_epi (V.map (e.prod f).hom)).1
    rw [L.naturality, H.naturality, hm]
  exact heq

/-- If K-flat representatives cover both derived categories, the localized unit
identity on representatives holds on all inputs.
Source: Stacks 015F, 06YS and 0GL1
(blueprint: lem-sf-open-tensor-unit-localization).
Proof: use `unit_on_models` on the prescribed K-flat representatives. Both sides
of the unit equation are natural transformations of the two inputs. Transport
the equality along the isomorphisms from the representatives to arbitrary
derived objects, cancelling the image of those isomorphisms. -/
theorem unit_normalization
    (htotal : ∀ P T, c.flatA P → c.flatB T →
      (c.TA.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)).app
          ((c.R.mapHomologicalComplex (.up ℤ)).obj T) ≫
        (c.totalRestriction ((c.E.mapHomologicalComplex (.up ℤ)).obj P) T).inv ≫
        (c.R.mapHomologicalComplex (.up ℤ)).map (c.totalGamma P T).hom =
      (adj.mapHomologicalComplex (.up ℤ)).unit.app
        ((c.TA.obj P).obj ((c.R.mapHomologicalComplex (.up ℤ)).obj T)))
    (hnat : ∀ P T (hP : c.flatA P) (hT : c.flatB T),
      c.DA.map (Prod.mkHom
          (DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P))
          (𝟙 (DerivedCategory.Q.obj ((c.R.mapHomologicalComplex (.up ℤ)).obj T)))) ≫
        (c.modelA _ _ (c.hR _ (c.hE P hP)) (c.hR T hT)).hom =
      (c.modelA P _ hP (c.hR T hT)).hom ≫ DerivedCategory.Q.map
        ((c.TA.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)).app
          ((c.R.mapHomologicalComplex (.up ℤ)).obj T)))
    (hA : ∀ M : DerivedCategory A,
      ∃ P : CochainComplex A ℤ, c.flatA P ∧ Nonempty (DerivedCategory.Q.obj P ≅ M))
    (hB : ∀ N : DerivedCategory B,
      ∃ T : CochainComplex B ℤ, c.flatB T ∧ Nonempty (DerivedCategory.Q.obj T ≅ N)) :
    OpenTensorUnitNormalization c.E.mapDerivedCategory c.R.mapDerivedCategory
      c.DA c.DB adj.mapExactDerivedCategory c.restriction c.gamma := by
  apply normalization_of_dense_inputs c.E.mapDerivedCategory c.R.mapDerivedCategory
    c.DA c.DB adj.mapExactDerivedCategory c.restriction c.gamma
    (fun M ↦ ∃ P : CochainComplex A ℤ, c.flatA P ∧ DerivedCategory.Q.obj P = M)
    (fun N ↦ ∃ T : CochainComplex B ℤ, c.flatB T ∧ DerivedCategory.Q.obj T = N)
  · intro M
    obtain ⟨P, hP, e⟩ := hA M
    exact ⟨_, ⟨P, hP, rfl⟩, e⟩
  · intro N
    obtain ⟨T, hT, e⟩ := hB N
    exact ⟨_, ⟨T, hT, rfl⟩, e⟩
  · rintro M N ⟨P, hP, rfl⟩ ⟨T, hT, rfl⟩
    exact c.unit_on_models adj P T hP hT (htotal P T hP hT) (hnat P T hP hT)

end CategoryTheory.OpenTensorPresentation
