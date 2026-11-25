/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import WeilConjectures.CategoryTheory.Sites.FiniteDisjointCover
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit

/-!
# Morphisms from the monoidal unit of a category of sheaves of modules

Let `J` be a Grothendieck topology on `C` and `R` a commutative ring, and equip the category of
sheaves of `R`-modules with the monoidal structure `CategoryTheory.Sheaf.monoidalCategory`
(sheafification of the objectwise tensor product). Let `W` be a terminal object of `C`.

* Morphisms `𝟙_ ⟶ F` correspond to sections of `F` over `W`, via evaluation at the *unit
  section* `CategoryTheory.Sheaf.unitSection J W`, the image of `1 ∈ R`
  (`CategoryTheory.Sheaf.hom_ext_of_unitSection`, `CategoryTheory.Sheaf.exists_unitHom_eq`).
* Under this correspondence, `(λ_ 𝟙_).inv ≫ (s ⊗ₘ t)` corresponds to the image of
  `s(1) ⊗ t(1)` under the canonical map `F(W) ⊗ G(W) ⟶ (F ⊗ G)(W)`
  (`CategoryTheory.Sheaf.leftUnitor_inv_comp_tensorHom_app`).

If moreover `W` has finite disjoint refinements
(`CategoryTheory.GrothendieckTopology.HasFiniteDisjointRefinements`), then taking sections over
`W` is exact and commutes with coproducts and tensor products up to finite sums. We deduce that
the unit is projective (`CategoryTheory.Sheaf.projective_unit`), that morphisms from the unit to
a coproduct factor through a finite subcoproduct
(`CategoryTheory.Sheaf.unitFactorsThroughFiniteCoproducts`) and that morphisms from the unit to
a tensor product are finite sums of tensor products (`CategoryTheory.Sheaf.unitTensorFinite`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite MonoidalCategory
open scoped TensorProduct

namespace ModuleCat

variable {R : Type*} [Ring R] {D : Type*} [Category* D] {K : D ⥤ ModuleCat.{w} R}

/-- The images of the components of a colimit cocone of modules span the colimit. -/
lemma iSup_range_ι_app_eq_top {c : Cocone K} (hc : IsColimit c) :
    ⨆ d, LinearMap.range (show K.obj d →ₗ[R] c.pt from (c.ι.app d).hom) = ⊤ := by
  set N := ⨆ d, LinearMap.range (show K.obj d →ₗ[R] c.pt from (c.ι.app d).hom)
  have h : ModuleCat.ofHom N.mkQ = 0 := hc.hom_ext fun d ↦ by
    ext x
    simpa using Submodule.mem_iSup_of_mem d (LinearMap.mem_range_self _ x)
  rw [eq_top_iff]
  intro x _
  rw [← Submodule.Quotient.mk_eq_zero]
  exact congr($h x)

end ModuleCat

namespace CategoryTheory

namespace GrothendieckTopology.IsDisjointCover

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type w} [CommRing R]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]
  {W : C} {ι : Type*} [Finite ι] {Y : ι → C} {f : ∀ i, Y i ⟶ W}

/-- Sections of the objectwise tensor product of two sheaves of modules over the members of a
finite disjoint cover glue. -/
lemma exists_map_tensorObj_eq (hf : J.IsDisjointCover f) (F G : Sheaf J (ModuleCat.{w} R))
    (t : ∀ i, (F.obj ⊗ G.obj).obj (op (Y i))) :
    ∃ x : (F.obj ⊗ G.obj).obj (op W), ∀ i, (F.obj ⊗ G.obj).map (f i).op x = t i := by
  classical
  have := Fintype.ofFinite ι
  refine Presheaf.exists_map_eq_of_exists_map_eq_single f
    (fun i ↦ {z | ∃ (a : F.obj.obj (op (Y i))) (b : G.obj.obj (op (Y i))), a ⊗ₜ b = z})
    (fun i ↦ TensorProduct.span_tmul_eq_top _ _ _) ?_ t
  rintro i _ ⟨a, b, rfl⟩
  obtain ⟨a', ha'⟩ := hf.exists_map_eq F (Pi.single i a)
  obtain ⟨b', hb'⟩ := hf.exists_map_eq G (Pi.single i b)
  refine ⟨(a' ⊗ₜ b' : F.obj.obj (op W) ⊗[R] G.obj.obj (op W)), fun k ↦ ?_⟩
  erw [Monoidal.tensorObj_map, ModuleCat.MonoidalCategory.tensorHom_tmul, ha', hb']
  by_cases hk : k = i
  · subst hk
    simp
  · simp [Pi.single_eq_of_ne hk]

/-- Sections of a coproduct of presheaves underlying sheaves of modules over the members of a
finite disjoint cover glue. -/
lemma exists_map_sigma_eq (hf : J.IsDisjointCover f) {K : Type*}
    (X : K → Sheaf J (ModuleCat.{w} R)) [HasCoproduct fun k ↦ (X k).obj]
    [HasColimitsOfShape (Discrete K) (ModuleCat.{w} R)]
    (t : ∀ i, (∐ fun k ↦ (X k).obj).obj (op (Y i))) :
    ∃ x : (∐ fun k ↦ (X k).obj).obj (op W), ∀ i, (∐ fun k ↦ (X k).obj).map (f i).op x = t i := by
  classical
  have := Fintype.ofFinite ι
  refine Presheaf.exists_map_eq_of_exists_map_eq_single f
    (fun i ↦ ⋃ k, Set.range ((Sigma.ι (fun k ↦ (X k).obj) k).app (op (Y i))))
    (fun i ↦ ?_) ?_ t
  · rw [Submodule.span_iUnion]
    refine _root_.eq_top_iff.2 ((ModuleCat.iSup_range_ι_app_eq_top
      (isColimitOfPreserves ((evaluation _ _).obj (op (Y i)))
        (colimit.isColimit (Discrete.functor fun k ↦ (X k).obj)))).symm.le.trans
      (iSup_le fun ⟨k⟩ ↦ le_iSup_of_le k ?_))
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨a, rfl⟩
  · rintro i _ ⟨_, ⟨k, rfl⟩, a, rfl⟩
    obtain ⟨a', ha'⟩ := hf.exists_map_eq (X k) (Pi.single i a)
    refine ⟨(Sigma.ι (fun k ↦ (X k).obj) k).app (op W) a', fun l ↦ ?_⟩
    rw [← NatTrans.naturality_apply, ha']
    by_cases hl : l = i
    · subst hl
      simp
    · simp [Pi.single_eq_of_ne hl]

end GrothendieckTopology.IsDisjointCover

namespace Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {R : Type (max u v)}
  [CommRing R] [HasWeakSheafify J (ModuleCat.{max u v} R)]
  [(J.W (A := ModuleCat.{max u v} R)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

/-- The canonical map from the constant presheaf `R`, the monoidal unit of presheaves, to the
presheaf underlying the monoidal unit of sheaves. -/
noncomputable def unitHom :
    𝟙_ (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ⟶ (𝟙_ (Sheaf J (ModuleCat.{max u v} R))).obj :=
  (sheafificationAdjunction J _).homEquiv _ _
    (Functor.OplaxMonoidal.η (presheafToSheaf J (ModuleCat.{max u v} R)))

/-- The unit section of the monoidal unit of sheaves of modules over an object `W`: the image
of `1 ∈ R` under the canonical map from the constant presheaf `R` to the unit. -/
noncomputable def unitSection (W : C) : (𝟙_ (Sheaf J (ModuleCat.{max u v} R))).obj.obj (op W) :=
  (unitHom J).app (op W) (1 : R)

/-- The canonical morphism from the objectwise tensor product of the presheaves underlying two
sheaves of modules to the presheaf underlying their tensor product. -/
noncomputable def tensorObjComparison (F G : Sheaf J (ModuleCat.{max u v} R)) :
    F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  (sheafificationAdjunction J _).homEquiv _ _
    (Functor.OplaxMonoidal.δ (presheafToSheaf J (ModuleCat.{max u v} R)) _ _ ≫
      ((sheafificationAdjunction J _).counit.app F ⊗ₘ (sheafificationAdjunction J _).counit.app G))

variable {J}

/-- The comparison `F(-) ⊗ G(-) ⟶ (F ⊗ G)(-)` is natural. -/
@[reassoc]
lemma tensorObjComparison_naturality {F F' G G' : Sheaf J (ModuleCat.{max u v} R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    tensorObjComparison J F G ≫ (f ⊗ₘ g).hom =
      (f.hom ⊗ₘ g.hom) ≫ tensorObjComparison J F' G' := by
  have h (F G : Sheaf J (ModuleCat.{max u v} R)) :
      ((sheafificationAdjunction J _).homEquiv _ _).symm (tensorObjComparison J F G) =
        Functor.OplaxMonoidal.δ (presheafToSheaf J (ModuleCat.{max u v} R)) _ _ ≫
          ((sheafificationAdjunction J _).counit.app F ⊗ₘ
            (sheafificationAdjunction J _).counit.app G) :=
    Equiv.symm_apply_apply _ _
  have h₂ : ((sheafificationAdjunction J _).homEquiv _ _).symm
      (tensorObjComparison J F G ≫ (f ⊗ₘ g).hom) =
      ((sheafificationAdjunction J _).homEquiv _ _).symm (tensorObjComparison J F G) ≫
        (f ⊗ₘ g) :=
    Adjunction.homEquiv_naturality_right_symm _ _ _
  have h₃ : ((sheafificationAdjunction J _).homEquiv _ _).symm
      ((f.hom ⊗ₘ g.hom) ≫ tensorObjComparison J F' G') =
      (presheafToSheaf J _).map (f.hom ⊗ₘ g.hom) ≫
        ((sheafificationAdjunction J _).homEquiv _ _).symm (tensorObjComparison J F' G') :=
    Adjunction.homEquiv_naturality_left_symm _ _ _
  apply ((sheafificationAdjunction J _).homEquiv _ _).symm.injective
  rw [h₂, h₃, h, h, Category.assoc, tensorHom_comp_tensorHom]
  erw [← Functor.OplaxMonoidal.δ_natural_assoc]
  rw [tensorHom_comp_tensorHom]
  congr 2
  · exact ((sheafificationAdjunction J _).counit.naturality f).symm
  · exact ((sheafificationAdjunction J _).counit.naturality g).symm

/-- The inverse of the left unitor of sheaves, on underlying presheaves. -/
lemma leftUnitor_inv_hom_eq_tensorObjComparison (F : Sheaf J (ModuleCat.{max u v} R)) :
    (λ_ F).inv.hom = (λ_ F.obj).inv ≫ unitHom J ▷ F.obj ≫ tensorObjComparison J (𝟙_ _) F := by
  have hθ : ((sheafificationAdjunction J _).homEquiv _ _).symm (tensorObjComparison J (𝟙_ _) F) =
      Functor.OplaxMonoidal.δ (presheafToSheaf J (ModuleCat.{max u v} R)) _ _ ≫
        ((sheafificationAdjunction J _).counit.app (𝟙_ _) ⊗ₘ
          (sheafificationAdjunction J _).counit.app F) :=
    Equiv.symm_apply_apply _ _
  have hu : (presheafToSheaf J _).map (unitHom J) ≫ (sheafificationAdjunction J _).counit.app _ =
      Functor.OplaxMonoidal.η (presheafToSheaf J (ModuleCat.{max u v} R)) :=
    (Adjunction.homEquiv_counit _ _ _ _).symm.trans (Equiv.symm_apply_apply _ _)
  have h₁ : ((sheafificationAdjunction J _).homEquiv _ _).symm ((λ_ F).inv.hom) =
      (sheafificationAdjunction J _).counit.app F ≫ (λ_ F).inv :=
    (Adjunction.homEquiv_counit _ _ _ _).trans
      ((sheafificationAdjunction J _).counit.naturality (λ_ F).inv)
  have h₃ : ((sheafificationAdjunction J _).homEquiv _ _).symm
      ((λ_ F.obj).inv ≫ unitHom J ▷ F.obj ≫ tensorObjComparison J (𝟙_ _) F) =
      (presheafToSheaf J _).map ((λ_ F.obj).inv ≫ unitHom J ▷ F.obj) ≫
        ((sheafificationAdjunction J _).homEquiv _ _).symm (tensorObjComparison J (𝟙_ _) F) := by
    rw [← Adjunction.homEquiv_naturality_left_symm, Category.assoc]
  apply ((sheafificationAdjunction J _).homEquiv _ _).symm.injective
  rw [h₁, h₃, hθ, Functor.map_comp, Category.assoc]
  erw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  rw [tensorHom_def]
  erw [← comp_whiskerRight_assoc]
  rw [hu, ← Functor.OplaxMonoidal.left_unitality_assoc]
  exact leftUnitor_inv_naturality ((sheafificationAdjunction J _).counit.app F)

section Terminal

variable {W : C} (hW : Limits.IsTerminal W)

omit [(J.W (A := ModuleCat.{max u v} R)).IsMonoidal] in
include hW in
lemma unitHom_app_one [(J.W (A := ModuleCat.{max u v} R)).IsMonoidal] (V : C) :
    (unitHom J).app (op V) (1 : R) =
      (𝟙_ (Sheaf J (ModuleCat.{max u v} R))).obj.map (hW.from V).op (unitSection J W) :=
  NatTrans.naturality_apply (unitHom J) (hW.from V).op (1 : R)

/-- `η ≫ x` transposes to `unitHom ≫ x`. -/
lemma homEquiv_η_comp {F : Sheaf J (ModuleCat.{max u v} R)}
    (x : 𝟙_ (Sheaf J (ModuleCat.{max u v} R)) ⟶ F) :
    (sheafificationAdjunction J _).homEquiv _ _
      (Functor.OplaxMonoidal.η (presheafToSheaf J (ModuleCat.{max u v} R)) ≫ x) =
      unitHom J ≫ x.hom :=
  Adjunction.homEquiv_naturality_right _ _ _

include hW in
/-- Morphisms out of the unit of sheaves of modules are determined by the image of the unit
section over the terminal object. -/
lemma hom_ext_of_unitSection {F : Sheaf J (ModuleCat.{max u v} R)}
    {x y : 𝟙_ (Sheaf J (ModuleCat.{max u v} R)) ⟶ F}
    (h : x.hom.app (op W) (unitSection J W) = y.hom.app (op W) (unitSection J W)) : x = y := by
  rw [← cancel_epi (Functor.OplaxMonoidal.η (presheafToSheaf J (ModuleCat.{max u v} R)))]
  apply ((sheafificationAdjunction J _).homEquiv _ _).injective
  rw [homEquiv_η_comp, homEquiv_η_comp]
  refine NatTrans.ext (funext fun V ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_))
  change x.hom.app V ((unitHom J).app V (1 : R)) = y.hom.app V ((unitHom J).app V (1 : R))
  rw [unitHom_app_one hW, NatTrans.naturality_apply, NatTrans.naturality_apply, h]

include hW in
/-- Every section of a sheaf of modules over the terminal object is the image of the unit
section under a morphism from the unit. -/
lemma exists_unitHom_eq (F : Sheaf J (ModuleCat.{max u v} R)) (s : F.obj.obj (op W)) :
    ∃ x : 𝟙_ (Sheaf J (ModuleCat.{max u v} R)) ⟶ F, x.hom.app (op W) (unitSection J W) = s := by
  let p : 𝟙_ (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ⟶ F.obj :=
    { app V := ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (F.obj.map (hW.from V.unop).op s))
      naturality V V' f := by
        refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
        have e : (hW.from V.unop).op ≫ f = (hW.from V'.unop).op :=
          Quiver.Hom.unop_inj (hW.hom_ext _ _)
        refine Eq.trans (b := (1 : R) • F.obj.map (hW.from V'.unop).op s) rfl ?_
        rw [one_smul, ← e, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
          ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]
        rfl }
  refine ⟨inv (Functor.OplaxMonoidal.η (presheafToSheaf J (ModuleCat.{max u v} R))) ≫
    ((sheafificationAdjunction J _).homEquiv _ _).symm p, ?_⟩
  have hp : unitHom J ≫ (inv (Functor.OplaxMonoidal.η (presheafToSheaf J _)) ≫
      ((sheafificationAdjunction J _).homEquiv _ _).symm p).hom = p := by
    rw [← homEquiv_η_comp, IsIso.hom_inv_id_assoc, Equiv.apply_symm_apply]
  have h := congr_arg (fun φ ↦ φ.app (op W) (1 : R)) hp
  refine h.trans ?_
  simp only [p, ModuleCat.hom_ofHom]
  rw [hW.hom_ext (hW.from W) (𝟙 W), op_id, F.obj.map_id]
  simp only [ModuleCat.hom_id, LinearMap.id_apply]
  exact one_smul R s

/-- The section over the terminal object of `λ⁻¹ ≫ (s ⊗ t) : 𝟙 ⟶ F ⊗ G` is the image of
`s(1) ⊗ t(1)` under the comparison `F(W) ⊗ G(W) ⟶ (F ⊗ G)(W)`. -/
lemma leftUnitor_inv_comp_tensorHom_app {F G : Sheaf J (ModuleCat.{max u v} R)}
    (s : 𝟙_ (Sheaf J (ModuleCat.{max u v} R)) ⟶ F) (t : 𝟙_ (Sheaf J (ModuleCat.{max u v} R)) ⟶ G) :
    ((λ_ (𝟙_ (Sheaf J (ModuleCat.{max u v} R)))).inv ≫ (s ⊗ₘ t)).hom.app (op W)
        (unitSection J W) =
      (tensorObjComparison J F G).app (op W)
        (s.hom.app (op W) (unitSection J W) ⊗ₜ t.hom.app (op W) (unitSection J W)) := by
  have hl : (λ_ (𝟙_ (Sheaf J (ModuleCat.{max u v} R)))).inv.hom.app (op W) (unitSection J W) =
      (tensorObjComparison J _ _).app (op W) (unitSection J W ⊗ₜ[R] unitSection J W) := by
    rw [leftUnitor_inv_hom_eq_tensorObjComparison]
    rfl
  have hn := congr_arg (fun φ ↦ φ.app (op W) (unitSection J W ⊗ₜ[R] unitSection J W))
    (tensorObjComparison_naturality s t)
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hn
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply, hl,
    hn]
  rfl

variable [J.HasSheafCompose (forget (ModuleCat.{max u v} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{max u v} R)]

include hW in
/-- If the terminal object has finite disjoint refinements, the unit of sheaves of modules is
projective: morphisms out of it are sections over the terminal object, and epimorphisms are
surjective on these. -/
theorem projective_unit [HasSheafify J (ModuleCat.{max u v} R)]
    [Balanced (Sheaf J (ModuleCat.{max u v} R))] (hfd : J.HasFiniteDisjointRefinements W) :
    Projective (𝟙_ (Sheaf J (ModuleCat.{max u v} R))) where
  factors {E G} f e _ := by
    have : Presheaf.IsLocallySurjective J e.hom :=
      (Sheaf.isLocallySurjective_iff_epi' _ e).2 inferInstance
    obtain ⟨t, ht⟩ := Presheaf.surjective_app_of_hasFiniteDisjointRefinements e.hom
      (Sheaf.isSeparated G) hfd (fun _ _ _ hf t ↦ hf.exists_map_eq E t)
      (f.hom.app (op W) (unitSection J W))
    obtain ⟨x, hx⟩ := exists_unitHom_eq hW E t
    refine ⟨x, hom_ext_of_unitSection hW ?_⟩
    rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
      hx, ht]

omit [J.HasSheafCompose (forget (ModuleCat.{max u v} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{max u v} R)] in
/-- Taking the image of the unit section is additive. -/
lemma sum_hom_app_unitSection {F : Sheaf J (ModuleCat.{max u v} R)} {ι : Type*} (S : Finset ι)
    (x : ι → (𝟙_ (Sheaf J (ModuleCat.{max u v} R)) ⟶ F)) :
    (∑ i ∈ S, x i).hom.app (op W) (unitSection J W) =
      ∑ i ∈ S, (x i).hom.app (op W) (unitSection J W) := by
  let E := sheafToPresheaf J (ModuleCat.{max u v} R) ⋙ (evaluation _ _).obj (op W)
  have h := congr_arg (fun φ ↦ φ (unitSection J W)) (E.map_sum x S)
  simpa [E] using h

omit [J.HasSheafCompose (forget (ModuleCat.{max u v} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{max u v} R)] in
/-- Taking the image of the unit section is additive. -/
lemma sub_hom_app_unitSection {F : Sheaf J (ModuleCat.{max u v} R)}
    (x y : 𝟙_ (Sheaf J (ModuleCat.{max u v} R)) ⟶ F) :
    (x - y).hom.app (op W) (unitSection J W) =
      x.hom.app (op W) (unitSection J W) - y.hom.app (op W) (unitSection J W) := by
  let E := sheafToPresheaf J (ModuleCat.{max u v} R) ⋙ (evaluation _ _).obj (op W)
  have h := congr_arg (fun φ : E.obj _ ⟶ E.obj F ↦ φ (unitSection J W))
    (E.map_sub (f := x) (g := y))
  simpa [E] using h

include hW in
/-- If the terminal object has finite disjoint refinements, morphisms from the unit of sheaves
of modules to a tensor product are finite sums of tensor products. -/
theorem unitTensorFinite (hfd : J.HasFiniteDisjointRefinements W) :
    UnitTensorFinite (Sheaf J (ModuleCat.{max u v} R)) := by
  intro F G x
  have hθ : ((sheafificationAdjunction J _).homEquiv _ _).symm (tensorObjComparison J F G) =
      Functor.OplaxMonoidal.δ (presheafToSheaf J (ModuleCat.{max u v} R)) _ _ ≫
        ((sheafificationAdjunction J _).counit.app F ⊗ₘ
          (sheafificationAdjunction J _).counit.app G) :=
    Equiv.symm_apply_apply _ _
  have hiso : IsIso ((presheafToSheaf J _).map (tensorObjComparison J F G)) := by
    have : IsIso (((sheafificationAdjunction J _).homEquiv _ _).symm
        (tensorObjComparison J F G)) := by
      rw [hθ]
      infer_instance
    rw [Adjunction.homEquiv_counit] at this
    exact IsIso.of_isIso_comp_right _ ((sheafificationAdjunction J _).counit.app _)
  have : Presheaf.IsLocallySurjective J (tensorObjComparison J F G) :=
    ((J.W_iff _).2 hiso).isLocallySurjective
  obtain ⟨p, hp⟩ := Presheaf.surjective_app_of_hasFiniteDisjointRefinements
    (tensorObjComparison J F G) (Sheaf.isSeparated _) hfd
    (fun _ _ _ hf t ↦ hf.exists_map_tensorObj_eq F G t) (x.hom.app (op W) (unitSection J W))
  clear hθ hiso
  induction p using TensorProduct.inductionOn generalizing x with
  | tmul a b =>
    obtain ⟨s, hs⟩ := exists_unitHom_eq hW F a
    obtain ⟨t, ht⟩ := exists_unitHom_eq hW G b
    refine ⟨1, fun _ ↦ s, fun _ ↦ t, hom_ext_of_unitSection hW ?_⟩
    rw [Fin.sum_univ_one, leftUnitor_inv_comp_tensorHom_app, hs, ht, ← hp]
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨x₁, hx₁⟩ := exists_unitHom_eq hW (F ⊗ G) ((tensorObjComparison J F G).app (op W) p₁)
    obtain ⟨n₁, s₁, t₁, e₁⟩ := h₁ x₁ hx₁.symm
    obtain ⟨n₂, s₂, t₂, e₂⟩ := h₂ (x - x₁) (by
      rw [sub_hom_app_unitSection, ← hp, hx₁, map_add]
      abel)
    refine ⟨n₁ + n₂, Fin.append s₁ s₂, Fin.append t₁ t₂, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, ← e₁, ← e₂]
    abel

include hW in
/-- If the terminal object has finite disjoint refinements, morphisms from the unit of sheaves
of modules to a coproduct factor through a finite subcoproduct. -/
theorem unitFactorsThroughFiniteCoproducts (hfd : J.HasFiniteDisjointRefinements W) :
    UnitFactorsThroughFiniteCoproducts (Sheaf J (ModuleCat.{max u v} R)) := by
  classical
  intro K X _ x
  let a := presheafToSheaf J (ModuleCat.{max u v} R)
  let adj := sheafificationAdjunction J (ModuleCat.{max u v} R)
  let ψ : (∐ fun k ↦ (X k).obj) ⟶ (∐ X).obj := Sigma.desc fun k ↦ (Sigma.ι X k).hom
  -- the sheafification of `ψ` is an isomorphism
  have hc := isColimitOfPreserves a (colimit.isColimit (Discrete.functor fun k ↦ (X k).obj))
  let e : Discrete.functor (fun k ↦ (X k).obj) ⋙ a ≅ Discrete.functor X :=
    Discrete.natIso fun k ↦ asIso (adj.counit.app (X k.as))
  have hc' := (IsColimit.precomposeInvEquiv e _).symm hc
  let f : (Cocone.precompose e.inv).obj (a.mapCocone (colimit.cocone _)) ⟶
      colimit.cocone (Discrete.functor X) :=
    { hom := a.map ψ ≫ adj.counit.app _
      w := fun ⟨k⟩ ↦ by
        dsimp
        rw [Category.assoc, ← Functor.map_comp_assoc]
        erw [Sigma.ι_comp_desc]
        erw [adj.counit.naturality]
        simp [e] }
  have hiso : IsIso (a.map ψ) := by
    have := IsColimit.hom_isIso hc' (colimit.isColimit _) f
    have : IsIso f.hom := (Cocone.forget _).map_isIso f
    have : IsIso (a.map ψ ≫ adj.counit.app _) := inferInstanceAs (IsIso f.hom)
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  have : Presheaf.IsLocallySurjective J ψ := ((J.W_iff _).2 hiso).isLocallySurjective
  obtain ⟨p, hp⟩ := Presheaf.surjective_app_of_hasFiniteDisjointRefinements ψ
    (Sheaf.isSeparated _) hfd (fun _ _ _ hf t ↦ hf.exists_map_sigma_eq X t)
    (x.hom.app (op W) (unitSection J W))
  have hp' : p ∈ ⨆ d : Discrete K, LinearMap.range (((Sigma.ι (fun k ↦ (X k).obj) d.as).app
      (op W)).hom) := by
    have h := ModuleCat.iSup_range_ι_app_eq_top
      (isColimitOfPreserves ((evaluation _ _).obj (op W)) (colimit.isColimit
        (Discrete.functor fun k ↦ (X k).obj)))
    rw [_root_.eq_top_iff] at h
    exact h Submodule.mem_top
  obtain ⟨S, hS⟩ := Submodule.exists_finset_of_mem_iSup _ hp'
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 hS
  choose b hb using fun d ↦ (μ d).2
  choose y hy using fun k ↦ exists_unitHom_eq hW (X k) (b ⟨k⟩)
  refine ⟨S.image Discrete.as, y, hom_ext_of_unitSection hW ?_⟩
  rw [sum_hom_app_unitSection, ← hp, ← hμ, map_sum,
    Finset.sum_image (fun _ _ _ _ h ↦ Discrete.ext h)]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [← hb d, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, Sigma.ι_comp_desc,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    hy]

end Terminal

end Sheaf

end CategoryTheory
