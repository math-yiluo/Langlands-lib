/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniversesMonoidalAdjunction
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.PerfectTensorHomDuality
import WeilConjectures.CategoryTheory.MonoidalProjectionConjugate

/-! # The direct-image factorization of a tensor precomposition

Source: Stacks Project, Tag 08EU and Tag 0E4G, Lemma 48.4.4.
(blueprint: lem-sc-derived-tensor-precomposition-projection).
-/

@[expose] public section

universe u wX wY

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projection_factorization
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Monoidal] (a : L ⊣ R)
    (I J : C) [ExactPairing I J] (P : D) (i : I ⟶ 𝟙_ C) :
    ∃ t : R.obj (L.obj I ⊗ P) ⟶ I ⊗ R.obj P,
      R.map (L.map i ▷ P ≫ (Functor.Monoidal.εIso L).inv ▷ P ≫ (λ_ P).hom) =
        t ≫ i ▷ R.obj P ≫ (λ_ (R.obj P)).hom := by
  let p := (a.homEquiv _ _)
    ((Functor.Monoidal.μIso L I (R.obj P)).inv ≫ L.obj I ◁ a.counit.app P)
  have hp : IsIso p := by
    dsimp only [p]
    rw [← monoidal_projection_conjugate L R a I J P]
    infer_instance
  refine ⟨inv p, ?_⟩
  apply (cancel_epi p).mp
  simp only [IsIso.hom_inv_id_assoc]
  apply (a.homEquiv _ _).symm.injective
  rw [a.homEquiv_naturality_right_symm]
  dsimp only [p]
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Functor.Monoidal.map_whiskerRight,
    Functor.Monoidal.map_leftUnitor, Category.assoc]
  simp only [Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μIso_inv,
    Functor.Monoidal.εIso_inv]
  congr 1
  have h₁ : L.obj I ◁ a.counit.app P ≫ L.map i ▷ P =
      L.map i ▷ L.obj (R.obj P) ≫ L.obj (𝟙_ C) ◁ a.counit.app P :=
    whisker_exchange (L.map i) (a.counit.app P)
  have h₂ : L.obj (𝟙_ C) ◁ a.counit.app P ≫
      Functor.OplaxMonoidal.η L ▷ P =
      Functor.OplaxMonoidal.η L ▷ L.obj (R.obj P) ≫
        (𝟙_ D) ◁ a.counit.app P :=
    whisker_exchange (Functor.OplaxMonoidal.η L) (a.counit.app P)
  rw [← Category.assoc, h₁, Category.assoc, reassoc_of% h₂]
  rw [leftUnitor_naturality]


private theorem projection_factorization_unit_change
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) (R : D ⥤ C) (I : C) (P : D) (i : I ⟶ 𝟙_ C)
    (e₀ e : L.obj (𝟙_ C) ≅ 𝟙_ D)
    (t₀ : R.obj (L.obj I ⊗ P) ⟶ I ⊗ R.obj P)
    (ht₀ : R.map (L.map i ▷ P ≫ e₀.hom ▷ P ≫ (λ_ P).hom) =
      t₀ ≫ i ▷ R.obj P ≫ (λ_ (R.obj P)).hom) :
    ∃ t : R.obj (L.obj I ⊗ P) ⟶ I ⊗ R.obj P,
      R.map (L.map i ▷ P ≫ e.hom ▷ P ≫ (λ_ P).hom) =
        t ≫ i ▷ R.obj P ≫ (λ_ (R.obj P)).hom := by
  let d : P ⟶ P := (λ_ P).inv ≫ (e₀.inv ≫ e.hom) ▷ P ≫ (λ_ P).hom
  have hj : L.map i ▷ P ≫ e.hom ▷ P ≫ (λ_ P).hom =
      (L.map i ▷ P ≫ e₀.hom ▷ P ≫ (λ_ P).hom) ≫ d := by
    simp [d, comp_whiskerRight, Category.assoc]
  refine ⟨t₀ ≫ I ◁ R.map d, ?_⟩
  rw [hj, R.map_comp, ht₀]
  simp only [Category.assoc]
  have hex := whisker_exchange i (R.map d)
  rw [reassoc_of% hex]
  rw [leftUnitor_naturality]

/-- The direct image of tensor precomposition factors through its base tensor map.
Source: Stacks Project, Tag 08EU, canonical projection formula and naturality,
and Tag 0E4G, Lemma 48.4.4, projection-formula paragraph.
(blueprint: lem-sc-derived-tensor-precomposition-projection).

Proof: For the canonical pullback unit identification e0, the perfect projection
formula, with the tensor symmetry, gives an isomorphism from Rf*(Lf*I tensor P)
to I tensor Rf*P. Naturality in i and unit coherence identify Rf* of the
precomposition map with that isomorphism followed by i tensor identity and the
left unitor. These identities are preserved by the localization equivalences
used in derivedPullbackAcrossUniverses. Conjugate the isomorphism by hF at R and P;
hF naturality identifies the resulting equality with F.map of the full-subcategory
morphism. For the supplied arbitrary unit isomorphism e, let c = e0.inv followed
by e.hom, an automorphism of the tensor unit on X, and let d be its action on P
via the left unitor. The map built with e equals the canonical map followed by d.
Modify the projection factor t0 by I tensor F(d). Tensor naturality moves F(d)
across i tensor identity, and left-unitor naturality gives precisely the displayed
factorization. Only existence of t is asserted; it is not chosen as definition data.
There is no adjunction, beta, Q, open or annihilation assumption in this statement.
Zero P and zero i obey the same naturality identities. -/
theorem exists_derivedTensor_precomposition_projection
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    [QuasiCompact f] [QuasiSeparated f]
    (F : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (hF : F ⋙ ObjectProperty.ι (schemeDerivedQCohProperty Y) ≅
      ObjectProperty.ι (schemeDerivedQCohProperty X) ⋙ schemeDerivedDirectImage f)
    (P : schemeDerivedQCohCategory X) (I : schemeDerivedCategory Y)
    (hI : Scheme.IsPerfect Y I) (i : I ⟶ 𝟙_ (schemeDerivedCategory Y))
    (e : (derivedPullbackAcrossUniverses f).obj (𝟙_ (schemeDerivedCategory Y)) ≅
      𝟙_ (schemeDerivedCategory X))
    (hR : schemeDerivedQCohProperty X
      ((derivedPullbackAcrossUniverses f).obj I ⊗ P.obj)) :
    ∃ t : (F.obj ⟨(derivedPullbackAcrossUniverses f).obj I ⊗ P.obj, hR⟩).obj ⟶
        I ⊗ (F.obj P).obj,
      (F.map (ObjectProperty.homMk
        ((derivedPullbackAcrossUniverses f).map i ▷ P.obj ≫
          e.hom ▷ P.obj ≫ (λ_ P.obj).hom))).hom =
        t ≫ i ▷ (F.obj P).obj ≫ (λ_ (F.obj P).obj).hom := by
  obtain ⟨m, ⟨a⟩⟩ := exists_derivedPullbackAcrossUniverses_monoidal_adjunction f
  let := m.toMonoidal
  let K : schemeDerivedQCohCategory Y :=
    ⟨I, schemeDerivedQCohProperty_of_isPerfect Y I hI⟩
  obtain ⟨J, ⟨pair⟩, _, _, _, _, _⟩ := perfect_tensor_hom_duality Y K hI
  let : ExactPairing I J.obj := pair
  obtain ⟨t₀, ht₀⟩ := projection_factorization
    (derivedPullbackAcrossUniverses f) (schemeDerivedDirectImage f) a I J.obj P.obj i
  obtain ⟨t, ht⟩ := projection_factorization_unit_change
    (derivedPullbackAcrossUniverses f) (schemeDerivedDirectImage f) I P.obj i
    (Functor.Monoidal.εIso (derivedPullbackAcrossUniverses f)).symm e t₀ ht₀
  let Q : schemeDerivedQCohCategory X :=
    ⟨(derivedPullbackAcrossUniverses f).obj I ⊗ P.obj, hR⟩
  let j : Q ⟶ P := ObjectProperty.homMk
    ((derivedPullbackAcrossUniverses f).map i ▷ P.obj ≫
      e.hom ▷ P.obj ≫ (λ_ P.obj).hom)
  refine ⟨(hF.app Q).hom ≫ t ≫ I ◁ (hF.app P).inv, ?_⟩
  have hn := hF.hom.naturality j
  change (F.map j).hom ≫ (hF.app P).hom =
    (hF.app Q).hom ≫ (schemeDerivedDirectImage f).map j.hom at hn
  have hmap : (F.map j).hom =
      (hF.app Q).hom ≫ (schemeDerivedDirectImage f).map j.hom ≫ (hF.app P).inv := by
    rw [← Category.assoc, ← hn]
    simp
  change (F.map j).hom = _
  rw [hmap]
  change (hF.app Q).hom ≫
    (schemeDerivedDirectImage f).map
      ((derivedPullbackAcrossUniverses f).map i ▷ P.obj ≫
        e.hom ▷ P.obj ≫ (λ_ P.obj).hom) ≫ (hF.app P).inv = _
  rw [ht]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc]
  rw [leftUnitor_naturality]

end AlgebraicGeometry
