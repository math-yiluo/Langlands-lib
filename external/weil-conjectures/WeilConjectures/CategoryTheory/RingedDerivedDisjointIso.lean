/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
public import WeilConjectures.CategoryTheory.Sites.FiniteDisjointCover
import WeilConjectures.CategoryTheory.SiteRestrictionKInjective
import WeilConjectures.CategoryTheory.Sites.DisjointGluing

/-! # Derived isomorphisms on a finite disjoint covering

Source: Stacks Project, Tags 03EM, 070I, 079P and 08FI.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme Opposite
namespace CategoryTheory

section HomGluing
variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})

private abbrev ring := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

private def restrictHom {U V : C} (f : V ⟶ U)
    {M N : SheafOfModules.{w} (ring R)}
    (a : (SheafOfModules.overFunctor (ring R) U).obj M ⟶
      (SheafOfModules.overFunctor (ring R) U).obj N) :
    (SheafOfModules.overFunctor (ring R) V).obj M ⟶
      (SheafOfModules.overFunctor (ring R) V).obj N :=
  ⟨PresheafOfModules.restrictOverMap f a.val⟩

private theorem glueHom {U : C} {I : Type*} {Y : I → C} {f : ∀ i, Y i ⟶ U}
    (hf : J.IsDisjointCover f) (M N : SheafOfModules.{w} (ring R))
    (a : ∀ i, (SheafOfModules.overFunctor (ring R) (Y i)).obj M ⟶
      (SheafOfModules.overFunctor (ring R) (Y i)).obj N) :
    ∃ b : (SheafOfModules.overFunctor (ring R) U).obj M ⟶
        (SheafOfModules.overFunctor (ring R) U).obj N,
      ∀ i, restrictHom R (f i) b = a i := by
  let F : Sheaf J (Type w) := (sheafCompose J (forget AddCommGrpCat.{w})).obj
    ((SheafOfModules.toSheaf (ring R)).obj (SheafOfModules.homObj.{w, w, w, w} (R := R) M N))
  have hF := (isSheaf_iff_isSheaf_of_type J F.obj).mp F.property
  have hdis : Presieve.IsDisjointFamily f J := ⟨hf.mono, hf.bot_mem⟩
  have hg := hF _ hf.ofArrows_mem
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hg
  obtain ⟨b, hb, _⟩ := hg (fun i ↦ (a i).val) (hdis.compatible F.property _)
  refine ⟨⟨b⟩, fun i ↦ ?_⟩
  exact SheafOfModules.hom_ext (hb i)

private theorem restrictHom_ext {U : C} {I : Type*} {Y : I → C} {f : ∀ i, Y i ⟶ U}
    (hf : J.IsDisjointCover f) {M N : SheafOfModules.{w} (ring R)}
    (a b : (SheafOfModules.overFunctor (ring R) U).obj M ⟶
      (SheafOfModules.overFunctor (ring R) U).obj N)
    (h : ∀ i, restrictHom R (f i) a = restrictHom R (f i) b) : a = b := by
  let F : Sheaf J (Type w) := (sheafCompose J (forget AddCommGrpCat.{w})).obj
    ((SheafOfModules.toSheaf (ring R)).obj (SheafOfModules.homObj.{w, w, w, w} (R := R) M N))
  apply SheafOfModules.hom_ext
  apply Sheaf.isSeparated F U _ hf.ofArrows_mem
  rintro W g ⟨_, k, _, ⟨i⟩, rfl⟩
  change PresheafOfModules.restrictOverMap (k ≫ f i) a.val =
    PresheafOfModules.restrictOverMap (k ≫ f i) b.val
  exact (PresheafOfModules.restrictOverMap_comp (f i) k a.val).trans
    ((congrArg (PresheafOfModules.restrictOverMap k)
      (congrArg SheafOfModules.Hom.val (h i))).trans
        (PresheafOfModules.restrictOverMap_comp (f i) k b.val).symm)

private theorem glueChainMap {U : C} {I : Type*} {Y : I → C} {f : ∀ i, Y i ⟶ U}
    (hf : J.IsDisjointCover f) (K L : CochainComplex (SheafOfModules.{w} (ring R)) ℤ)
    (a : ∀ i,
      ((SheafOfModules.overFunctor (ring R) (Y i)).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((SheafOfModules.overFunctor (ring R) (Y i)).mapHomologicalComplex (.up ℤ)).obj L) :
    ∃ b : ((SheafOfModules.overFunctor (ring R) U).mapHomologicalComplex (.up ℤ)).obj K ⟶
        ((SheafOfModules.overFunctor (ring R) U).mapHomologicalComplex (.up ℤ)).obj L,
      ∀ i n, restrictHom R (f i) (b.f n) = (a i).f n := by
  choose b hb using fun n ↦ glueHom R hf (K.X n) (L.X n) (fun i ↦ (a i).f n)
  refine ⟨{ f := b, comm' := ?_ }, fun i n ↦ hb n i⟩
  intro n m hnm
  apply restrictHom_ext R hf
  intro i
  have h₁ : restrictHom R (f i)
      ((SheafOfModules.overFunctor (ring R) U).map (K.d n m) ≫ b m) =
      (SheafOfModules.overFunctor (ring R) (Y i)).map (K.d n m) ≫
        restrictHom R (f i) (b m) := rfl
  have h₂ : restrictHom R (f i)
      (b n ≫ (SheafOfModules.overFunctor (ring R) U).map (L.d n m)) =
      restrictHom R (f i) (b n) ≫
        (SheafOfModules.overFunctor (ring R) (Y i)).map (L.d n m) := rfl
  change restrictHom R (f i)
      (b n ≫ (SheafOfModules.overFunctor (ring R) U).map (L.d n m)) =
    restrictHom R (f i)
      ((SheafOfModules.overFunctor (ring R) U).map (K.d n m) ≫ b m)
  rw [h₁, h₂, hb, hb]
  exact (a i).comm n m

private theorem restrictHom_comp {U V : C} (f : V ⟶ U)
    {M N P : SheafOfModules.{w} (ring R)}
    (a : (SheafOfModules.overFunctor (ring R) U).obj M ⟶
      (SheafOfModules.overFunctor (ring R) U).obj N)
    (b : (SheafOfModules.overFunctor (ring R) U).obj N ⟶
      (SheafOfModules.overFunctor (ring R) U).obj P) :
    restrictHom R f (a ≫ b) = restrictHom R f a ≫ restrictHom R f b := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  rfl

private theorem restrictHom_add {U V : C} (f : V ⟶ U)
    {M N : SheafOfModules.{w} (ring R)}
    (a b : (SheafOfModules.overFunctor (ring R) U).obj M ⟶
      (SheafOfModules.overFunctor (ring R) U).obj N) :
    restrictHom R f (a + b) = restrictHom R f a + restrictHom R f b := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  rfl

private theorem restrictHom_map {U V : C} (f : V ⟶ U)
    {M N : SheafOfModules.{w} (ring R)} (a : M ⟶ N) :
    restrictHom R f ((SheafOfModules.overFunctor (ring R) U).map a) =
      (SheafOfModules.overFunctor (ring R) V).map a := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  rfl

private theorem restrictHom_zero {U V : C} (f : V ⟶ U)
    {M N : SheafOfModules.{w} (ring R)} :
    restrictHom R f (0 : (SheafOfModules.overFunctor (ring R) U).obj M ⟶
      (SheafOfModules.overFunctor (ring R) U).obj N) = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  rfl

private theorem glueHomotopy {U : C} {I : Type*} {Y : I → C} {f : ∀ i, Y i ⟶ U}
    (hf : J.IsDisjointCover f) (K L : CochainComplex (SheafOfModules.{w} (ring R)) ℤ)
    (a b : ((SheafOfModules.overFunctor (ring R) U).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((SheafOfModules.overFunctor (ring R) U).mapHomologicalComplex (.up ℤ)).obj L)
    (ai bi : ∀ i,
      ((SheafOfModules.overFunctor (ring R) (Y i)).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((SheafOfModules.overFunctor (ring R) (Y i)).mapHomologicalComplex (.up ℤ)).obj L)
    (ha : ∀ i n, restrictHom R (f i) (a.f n) = (ai i).f n)
    (hb : ∀ i n, restrictHom R (f i) (b.f n) = (bi i).f n)
    (hi : ∀ i, Homotopy (ai i) (bi i)) : Nonempty (Homotopy a b) := by
  choose H hH using fun n m ↦
    glueHom R hf (K.X n) (L.X m) (fun i ↦ (hi i).hom n m)
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }⟩
  · intro n m hnm
    apply restrictHom_ext R hf
    intro i
    rw [hH, restrictHom_zero]
    exact (hi i).zero n m hnm
  · intro n
    let an : (SheafOfModules.overFunctor (ring R) U).obj (K.X n) ⟶
      (SheafOfModules.overFunctor (ring R) U).obj (L.X n) := a.f n
    let bn : (SheafOfModules.overFunctor (ring R) U).obj (K.X n) ⟶
      (SheafOfModules.overFunctor (ring R) U).obj (L.X n) := b.f n
    change an =
      (SheafOfModules.overFunctor (ring R) U).map (K.d n ((ComplexShape.up ℤ).next n)) ≫
        H ((ComplexShape.up ℤ).next n) n +
      H n ((ComplexShape.up ℤ).prev n) ≫
        (SheafOfModules.overFunctor (ring R) U).map (L.d ((ComplexShape.up ℤ).prev n) n) +
        bn
    apply restrictHom_ext R hf
    intro i
    rw [restrictHom_add, restrictHom_add, restrictHom_comp, restrictHom_comp,
      restrictHom_map, restrictHom_map, hH, hH]
    rw [show restrictHom R (f i) an = (ai i).f n from ha i n,
      show restrictHom R (f i) bn = (bi i).f n from hb i n]
    exact (hi i).comm n

end HomGluing

private theorem homotopyEquivOfDerivedIso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (K L : CochainComplex A ℤ) [K.IsKInjective] [L.IsKInjective]
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    Nonempty (HomotopyEquiv K L) := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let e' := (DerivedCategory.quotientCompQhIso A).app K ≪≫ e ≪≫
    ((DerivedCategory.quotientCompQhIso A).app L).symm
  obtain ⟨a, ha⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) L).surjective
    e'.hom
  obtain ⟨b, hb⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj L) K).surjective
    e'.inv
  refine ⟨HomotopyCategory.homotopyEquivOfIso
    { hom := a, inv := b, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · apply (CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) K).injective
    simp only [Functor.map_comp, ha, hb, Iso.hom_inv_id]
    exact (DerivedCategory.Qh.map_id (q.obj K)).symm
  · apply (CochainComplex.IsKInjective.Qh_map_bijective (q.obj L) L).injective
    simp only [Functor.map_comp, ha, hb, Iso.inv_hom_id]
    exact (DerivedCategory.Qh.map_id (q.obj L)).symm

/-- Derived module objects which are isomorphic on a finite disjoint cover are isomorphic.
Source: Stacks Project, Modules on Sites, Tag 03EM; Derived Categories, Tag 070I;
Injectives, Tag 079P; Cohomology on Sites, Tag 08FI.
(auxiliary; not a blueprint node).

Proof: Replace both objects on the slice by K-injective complexes. Exact restriction
preserves K-injectives. Represent the component isomorphisms by chain maps. Since the
covering arrows are monomorphisms and their distinct intersections have empty covering,
module morphisms on the pieces glue uniquely; glue each degree of the chain maps.
Separatedness verifies the differential equations. Lift the inverse maps too, and
represent the inverse identities by homotopies using full faithfulness of localization
on K-injectives. Glue their degreewise components; separatedness verifies the homotopy
equations. The two glued chain maps are homotopy inverse and induce the required derived
isomorphism. Transport through the exact restriction/localization comparisons. The same
argument treats the empty cover, where separatedness forces all morphisms to agree. -/
theorem ringedDerived_disjoint_iso
    {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (U : C)
    (L N : ConstantCompletion.D R)
    (n : ℕ) (Y : Fin n → C) (f : ∀ i, Y i ⟶ U)
    (hf : J.IsDisjointCover f)
    (hlocal : ∀ i, Nonempty ((adicResidueRestriction R (Y i)).obj L ≅
      (adicResidueRestriction R (Y i)).obj N)) :
    Nonempty ((adicResidueRestriction R U).obj L ≅
      (adicResidueRestriction R U).obj N) := by
  classical
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let (V : C) := HasDerivedCategory.standard (ConstantCompletion.Mod (R.over V))
  obtain ⟨_, _, I, η, hI⟩ :=
    SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J R
  let K₀ := DerivedCategory.Q.objPreimage L
  let M₀ := DerivedCategory.Q.objPreimage N
  let K := I.obj K₀
  let M := I.obj M₀
  have : QuasiIso (η.app K₀) := (hI K₀).1
  have : QuasiIso (η.app M₀) := (hI M₀).1
  have : K.IsKInjective := (hI K₀).2.1
  have : M.IsKInjective := (hI M₀).2.1
  let eL : DerivedCategory.Q.obj K ≅ L :=
    (asIso (DerivedCategory.Q.map (η.app K₀))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso L
  let eN : DerivedCategory.Q.obj M ≅ N :=
    (asIso (DerivedCategory.Q.map (η.app M₀))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso N
  let F (V : C) : ConstantCompletion.Mod R ⥤ ConstantCompletion.Mod (R.over V) :=
    SheafOfModules.overFunctor.{w} (ring R) V
  have (V : C) : (F V).Additive := ringedOverFunctor_additive R V
  have (V : C) : PreservesFiniteLimits (F V) := ringedOverFunctor_preservesFiniteLimits R V
  have (V : C) : PreservesFiniteColimits (F V) := ringedOverFunctor_preservesFiniteColimits R V
  have hF (V : C) : (F V).PreservesKInjectiveComplexes :=
    SheafOfModules.overFunctor_preservesKInjectiveComplexes_ofUniverses.{w, w, w} (ring R) V
  have hK (V : C) : CochainComplex.IsKInjective
      (((F V).mapHomologicalComplex (.up ℤ)).obj K) := by
    have := hF V
    exact Functor.PreservesKInjectiveComplexes.isKInjective_map K
  have hM (V : C) : CochainComplex.IsKInjective
      (((F V).mapHomologicalComplex (.up ℤ)).obj M) := by
    have := hF V
    exact Functor.PreservesKInjectiveComplexes.isKInjective_map M
  have he (i : Fin n) : Nonempty
      (HomotopyEquiv (((F (Y i)).mapHomologicalComplex (.up ℤ)).obj K)
        (((F (Y i)).mapHomologicalComplex (.up ℤ)).obj M)) := by
    have := hK (Y i)
    have := hM (Y i)
    apply homotopyEquivOfDerivedIso
    exact ((F (Y i)).mapDerivedCategoryFactors.app K).symm ≪≫
      (F (Y i)).mapDerivedCategory.mapIso eL ≪≫ (hlocal i).some ≪≫
      (F (Y i)).mapDerivedCategory.mapIso eN.symm ≪≫
      (F (Y i)).mapDerivedCategoryFactors.app M
  let e (i : Fin n) := (he i).some
  obtain ⟨a, ha⟩ := glueChainMap R hf K M (fun i ↦ (e i).hom)
  obtain ⟨b, hb⟩ := glueChainMap R hf M K (fun i ↦ (e i).inv)
  obtain ⟨hab⟩ := glueHomotopy R hf K K (a ≫ b) (𝟙 _)
    (fun i ↦ (e i).hom ≫ (e i).inv) (fun _ ↦ 𝟙 _)
    (by intro i k; change restrictHom R (f i) (a.f k ≫ b.f k) = _
        rw [restrictHom_comp, ha, hb]; rfl)
    (by intro i k; rfl) (fun i ↦ (e i).homotopyHomInvId)
  obtain ⟨hba⟩ := glueHomotopy R hf M M (b ≫ a) (𝟙 _)
    (fun i ↦ (e i).inv ≫ (e i).hom) (fun _ ↦ 𝟙 _)
    (by intro i k; change restrictHom R (f i) (b.f k ≫ a.f k) = _
        rw [restrictHom_comp, hb, ha]; rfl)
    (by intro i k; rfl) (fun i ↦ (e i).homotopyInvHomId)
  let eU : DerivedCategory.Q.obj (((F U).mapHomologicalComplex (.up ℤ)).obj K) ≅
      DerivedCategory.Q.obj (((F U).mapHomologicalComplex (.up ℤ)).obj M) :=
    { hom := DerivedCategory.Q.map a
      inv := DerivedCategory.Q.map b
      hom_inv_id := by
        rw [← Functor.map_comp,
          DerivedCategory.Q_map_eq_of_homotopy (ConstantCompletion.Mod (R.over U)) hab,
          Functor.map_id]
      inv_hom_id := by
        rw [← Functor.map_comp,
          DerivedCategory.Q_map_eq_of_homotopy (ConstantCompletion.Mod (R.over U)) hba,
          Functor.map_id] }
  exact ⟨(F U).mapDerivedCategory.mapIso eL.symm ≪≫
    (F U).mapDerivedCategoryFactors.app K ≪≫ eU ≪≫
    ((F U).mapDerivedCategoryFactors.app M).symm ≪≫ (F U).mapDerivedCategory.mapIso eN⟩

end CategoryTheory
