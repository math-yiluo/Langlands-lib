/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.PointModelFreeModule
public import WeilConjectures.AlgebraicGeometry.PointModelPullbackFunctor
import WeilConjectures.AlgebraicGeometry.DiscreteSectionCoordinates
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.FiniteLocalSectionLifts
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Local descent of an internal matrix to the discrete condensed point

Source: Stacks, Tags 03CY and 00YV; the finite-section argument in
`lem-sfb-discrete-constant-presentation-lifting`, step 2.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

private theorem pointPullback_preservesFiniteColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Z : Scheme.{u}) :
    PreservesFiniteColimits (pointModelPullbackFunctor Λ Z) := by
  have : (upperStarFromPoint Z).IsLeftAdjoint := by
    unfold upperStarFromPoint
    exact (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Z))).isLeftAdjoint
  unfold pointModelPullbackFunctor
  infer_instance

@[irreducible] private noncomputable def mapRegularIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] (R : C) [MonObj R] :
    (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R) :=
  Mod.isoMk (Iso.refl _) (by simp)

private theorem mapRegularIso_unit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] (R : C) [MonObj R] (x : 𝟙_ C ⟶ R) :
    (MonObj.one : 𝟙_ D ⟶ F.obj R) ≫
      ((mapRegularIso F R).inv ≫ (F.mapMod R).map
        (Mod.regularLift (Mod.regular R) x) ≫ (mapRegularIso F R).hom).hom =
      Functor.LaxMonoidal.ε F ≫ F.map x := by
  simp only [mapRegularIso, Mod.comp_hom', Mod.isoMk_hom_hom, Mod.isoMk_inv_hom,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id]
  change (Functor.LaxMonoidal.ε F ≫ F.map (MonObj.one : 𝟙_ C ⟶ R)) ≫
    (𝟙 (F.obj R) ≫ F.map (Mod.regularLift (Mod.regular R) x).hom) = _
  simp only [Category.id_comp, Category.assoc, ← F.map_comp,
    Mod.one_comp_regularLift]

section RegularPullback
variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory D]
  [HasCoequalizers D] [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (F : C ⥤ D) [F.LaxMonoidal] (R : C) [MonObj R] [IsCommMonObj (F.obj R)]
  {S : D} [MonObj S] (φ : F.obj R ⟶ S) [IsMonHom φ]

@[irreducible] private noncomputable def regularPullbackIso :
    (F.mapMod R ⋙ Mod.extendScalars φ).obj (Mod.regular R) ≅ Mod.regular S :=
  (Mod.extendScalars φ).mapIso (mapRegularIso F R) ≪≫ Mod.regularExtensionIso φ

private theorem regularPullback_square
    (f : Mod.regular R ⟶ Mod.regular R) (q : Mod.regular S ⟶ Mod.regular S)
    (hx : Functor.LaxMonoidal.ε F ≫
      F.map ((MonObj.one : 𝟙_ C ⟶ R) ≫ f.hom) ≫ φ =
        (MonObj.one : 𝟙_ D ⟶ S) ≫ q.hom) :
    (F.mapMod R ⋙ Mod.extendScalars φ).map f ≫ (regularPullbackIso F R φ).hom =
      (regularPullbackIso F R φ).hom ≫ q := by
  let e := mapRegularIso F R
  let p := e.inv ≫ (F.mapMod R).map f ≫ e.hom
  have hp : p.hom ≫ φ = φ ≫ q.hom := by
    have ht : p ≫ Mod.regularCoefficientMap φ =
        Mod.regularCoefficientMap φ ≫ (Mod.comap φ).map q := by
      apply Mod.regular_hom_ext
      change (MonObj.one : 𝟙_ D ⟶ F.obj R) ≫ p.hom ≫ φ =
        (MonObj.one : 𝟙_ D ⟶ F.obj R) ≫ φ ≫ q.hom
      rw [← Category.assoc (MonObj.one : 𝟙_ D ⟶ F.obj R) φ,
        IsMonHom.one_hom (f := φ)]
      simp only [p, e, mapRegularIso, Mod.comp_hom', Mod.isoMk_hom_hom,
        Mod.isoMk_inv_hom, Iso.refl_hom, Iso.refl_inv, Category.comp_id]
      change (Functor.LaxMonoidal.ε F ≫ F.map (MonObj.one : 𝟙_ C ⟶ R)) ≫
        (𝟙 (F.obj R) ≫ F.map f.hom) ≫ φ = _
      simp only [Category.id_comp, Category.assoc]
      rw [← Category.assoc (F.map (MonObj.one : 𝟙_ C ⟶ R)) (F.map f.hom) φ,
        ← F.map_comp]
      exact hx
    exact congrArg Mod.Hom.hom ht
  have hn := Mod.regularExtensionIso_naturality φ p q hp
  have hc := congrArg (fun t ↦ (Mod.extendScalars φ).map e.hom ≫ t) hn
  dsimp only [p] at hc
  simp only [Functor.map_comp, ← Category.assoc] at hc
  rw [← (Mod.extendScalars φ).map_comp e.hom e.inv, Iso.hom_inv_id,
    (Mod.extendScalars φ).map_id, Category.id_comp] at hc
  simpa only [regularPullbackIso, Functor.comp_map, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc, e] using hc
end RegularPullback

private noncomputable def pointRegularIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (pointModelPullbackFunctor Λ X).obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ X) :=
  mapRegularIso (upperStarFromPoint X) Λ

@[irreducible] private noncomputable def freeComparison
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F] {R : C} {T : D}
    (e : F.obj R ≅ T) (n : ℕ) :
    F.obj (⨁ fun _ : Fin n ↦ R) ≅ ⨁ fun _ : Fin n ↦ T :=
  F.mapBiproduct (fun _ : Fin n ↦ R) ≪≫ biproduct.mapIso (fun _ ↦ e)

private theorem mapped_entry
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F] {R : C} {T : D} (e : F.obj R ≅ T)
    {m n : ℕ} (a : (⨁ fun _ : Fin m ↦ R) ⟶ ⨁ fun _ : Fin n ↦ R)
    (j : Fin m) (k : Fin n) :
    biproduct.ι (fun _ : Fin m ↦ T) j ≫
        (freeComparison F e m).inv ≫
        F.map a ≫
        (freeComparison F e n).hom ≫
        biproduct.π (fun _ : Fin n ↦ T) k =
      e.inv ≫ F.map (biproduct.ι (fun _ : Fin m ↦ R) j ≫ a ≫
        biproduct.π (fun _ : Fin n ↦ R) k) ≫ e.hom := by
  unfold freeComparison
  simp only [Iso.trans_inv, Iso.trans_hom, biproduct.mapIso_inv, biproduct.mapIso_hom,
    Category.assoc, biproduct.ι_map_assoc, Functor.mapBiproduct_inv,
    Functor.mapBiproduct_hom, biproduct.ι_desc_assoc, biproduct.map_π]
  erw [biproduct.lift_π_assoc]
  simp only [← Category.assoc, ← Functor.map_comp]

private theorem matrix_arrow_iso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasFiniteBiproducts E]
    (F : C ⥤ E) (H : D ⥤ E) [F.Additive] [H.Additive]
    [PreservesFiniteColimits F] [PreservesFiniteColimits H]
    {R : C} {S : D} {T : E} (e : F.obj R ≅ T) (q : H.obj S ≅ T)
    {m n : ℕ} (a : (⨁ fun _ : Fin m ↦ R) ⟶ ⨁ fun _ : Fin n ↦ R)
    (b : Fin m → Fin n → (S ⟶ S))
    (hb : ∀ j k, F.map (biproduct.ι _ j ≫ a ≫ biproduct.π _ k) ≫ e.hom =
      e.hom ≫ q.inv ≫ H.map (b j k) ≫ q.hom) :
    Nonempty (Arrow.mk (F.map a) ≅ Arrow.mk (H.map (biproduct.matrix b))) := by
  let eF (r : ℕ) := freeComparison F e r
  let eH (r : ℕ) := freeComparison H q r
  have he : (eF m).inv ≫ F.map a ≫ (eF n).hom =
      (eH m).inv ≫ H.map (biproduct.matrix b) ≫ (eH n).hom := by
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro k
    simp only [Category.assoc]
    dsimp only [eF, eH]
    rw [mapped_entry F e a j k, mapped_entry H q (biproduct.matrix b) j k]
    have hh := congrArg (fun f ↦ e.inv ≫ f) (hb j k)
    simpa only [Category.assoc, biproduct.ι_matrix_assoc, biproduct.lift_π,
      Iso.inv_hom_id_assoc] using hh
  refine ⟨Arrow.isoMk ((eF m) ≪≫ (eH m).symm) ((eF n) ≪≫ (eH n).symm) ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  apply (cancel_mono (eH n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (eF m).hom ≫ (eH m).inv ≫ H.map (biproduct.matrix b) ≫ (eH n).hom =
    F.map a ≫ (eF n).hom
  rw [← he, Iso.hom_inv_id_assoc]

private theorem regular_section_square
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z : Scheme.{u}} (h : Z ⟶ X)
    (f : Mod.regular (condensedRingObj Λ X) ⟶
      Mod.regular (condensedRingObj Λ X))
    (c : 𝟙_ _ ⟶ Λ)
    (hx : Functor.LaxMonoidal.ε (upperStar Ab.{u + 1} h) ≫
        (upperStar Ab.{u + 1} h).map
          ((MonObj.one : 𝟙_ _ ⟶ condensedRingObj Λ X) ≫ f.hom) ≫
        condensedPullbackHom Λ h =
      Functor.LaxMonoidal.ε (upperStarFromPoint Z) ≫
        (upperStarFromPoint Z).map c) :
    (CondensedRing.upperStar Λ h).map f ≫
        (regularPullbackIso (upperStar Ab.{u + 1} h)
          (condensedRingObj Λ X) (condensedPullbackHom Λ h)).hom =
      (regularPullbackIso (upperStar Ab.{u + 1} h)
          (condensedRingObj Λ X) (condensedPullbackHom Λ h)).hom ≫
        (pointRegularIso Λ Z).inv ≫
        (pointModelPullbackFunctor Λ Z).map
          (Mod.regularLift (Mod.regular Λ) c) ≫
        (pointRegularIso Λ Z).hom := by
  apply regularPullback_square
  exact hx.trans (mapRegularIso_unit (upperStarFromPoint Z) Λ c).symm

private theorem matrix_lifting_from_sections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z : Scheme.{u}} (h : Z ⟶ X) (m n : ℕ)
    (a : Mod.finiteFree (condensedRingObj Λ X) m ⟶
      Mod.finiteFree (condensedRingObj Λ X) n)
    (c : Fin m × Fin n → (𝟙_ _ ⟶ Λ))
    (hc : ∀ j k, Functor.LaxMonoidal.ε (upperStar Ab.{u + 1} h) ≫
      (upperStar Ab.{u + 1} h).map
        ((MonObj.one : 𝟙_ _ ⟶ condensedRingObj Λ X) ≫
          (biproduct.ι _ j ≫ a ≫ biproduct.π _ k).hom) ≫ condensedPullbackHom Λ h =
      Functor.LaxMonoidal.ε (upperStarFromPoint Z) ≫
        (upperStarFromPoint Z).map (c (j, k))) :
    ∃ d : pointModelFree Λ m ⟶ pointModelFree Λ n,
      Nonempty (Arrow.mk ((CondensedRing.upperStar Λ h).map a) ≅
        Arrow.mk ((pointModelPullbackFunctor Λ Z).map d)) := by
  let R := condensedRingObj Λ X
  let G := CondensedRing.upperStar Λ h
  let P := pointModelPullbackFunctor Λ Z
  have : PreservesFiniteColimits G := by unfold G; infer_instance
  have : PreservesFiniteColimits P := pointPullback_preservesFiniteColimits Λ Z
  have : P.Additive := by
    have : PreservesBinaryBiproducts P :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  let d : pointModelFree Λ m ⟶ pointModelFree Λ n :=
    biproduct.matrix fun j k ↦ Mod.regularLift (Mod.regular Λ) (c (j, k))
  refine ⟨d, matrix_arrow_iso G P
    (regularPullbackIso (upperStar Ab.{u + 1} h) R
      (condensedPullbackHom Λ h)) (pointRegularIso Λ Z)
    a (fun j k ↦ Mod.regularLift (Mod.regular Λ) (c (j, k))) ?_⟩
  intro j k
  exact regular_section_square Λ h _ (c (j, k)) (hc j k)

/-- A finite matrix over discrete scheme coefficients is locally the pullback of a
matrix on the condensed point, up to the finite-free comparison isomorphisms.
This assertion concerns only morphisms between free modules: there is no arbitrary
module, constant slice trivialization, cokernel or coefficient relabelling.

Source: Stacks, Modules on Sites, Tag 03CY; Sites, Tag 00YV; the second step of
`lem-sfb-discrete-constant-presentation-lifting`.
(auxiliary; not a blueprint node).

Proof: the entries of a are maps between regular modules, hence sections of the
discrete coefficient ring on the terminal object of the pro-etale site of the
underlying scheme of U. The monoidal constant-sheaf pullback comparison identifies
this ring with the constant sheaf of ULift A, including its unit and multiplication.
Apply finite_local_section_lifts to the constant-presheaf sheafification unit and
the Fin m times Fin n tuple of coordinates directly on the coefficient-sized
site of Y, giving a covering sieve S on U.
For each member choose the simultaneous scalar lifts. Each scalar defines a
regular point-module endomorphism by multiplication; the biproduct matrix of these
endomorphisms is d. Pullback preserves the finite biproducts and their injections
and projections. Its regular-module comparison carries the scalar endomorphisms
to multiplication by the corresponding constant sections. The entrywise lifting
equalities therefore give the square between the two pulled-back matrices.
The finite-free comparison isomorphisms and this square give the asserted arrow
isomorphism. An empty index set gives the maximal covering sieve and the unique
zero matrix. An empty scheme allows the empty covering sieve. -/
theorem discrete_internal_matrix_local_lifting
    (A : Type u) [CommRing A] {Y : Scheme.{u}}
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (m n : ℕ)
    (a : Mod.finiteFree (condensedRingObj (discreteObj A) (AsSmall.down.obj U).left) m ⟶
      Mod.finiteFree (condensedRingObj (discreteObj A) (AsSmall.down.obj U).left) n) :
    ∃ S : Sieve U, S ∈ Scheme.coefficientProEtaleModelTopology.{u, u} Y U ∧
      ∀ (V : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (g : V ⟶ U), S g →
        ∃ d : pointModelFree (discreteObj A) m ⟶ pointModelFree (discreteObj A) n,
          Nonempty
            (Arrow.mk ((CondensedRing.upperStar (discreteObj A)
                (AsSmall.down.map g).left).map a) ≅
              Arrow.mk ((pointModelPullbackFunctor (discreteObj A)
                (AsSmall.down.obj V).left).map d)) := by
  classical
  let R := condensedRingObj (discreteObj A) (AsSmall.down.obj U).left
  let entry (i : Fin m × Fin n) : Mod.regular R ⟶ Mod.regular R :=
    biproduct.ι (fun _ : Fin m ↦ Mod.regular R) i.1 ≫ a ≫
      biproduct.π (fun _ : Fin n ↦ Mod.regular R) i.2
  choose s hs using fun i : Fin m × Fin n ↦
    discrete_section_coordinates A U
      ((MonObj.one : 𝟙_ _ ⟶ R) ≫ (entry i).hom)
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} Y
  let q := toSheafify J
    ((Functor.const (Scheme.coefficientProEtaleSiteModel.{u, u} Y)ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} A)))
  obtain ⟨S, hS, hlocal⟩ := Presheaf.finite_local_section_lifts J q s
  refine ⟨S, hS, ?_⟩
  intro V g hg
  obtain ⟨c, hc⟩ := hlocal V g hg
  apply matrix_lifting_from_sections (discreteObj A) (AsSmall.down.map g).left m n a
    (fun i ↦ discretePointScalarSection A (c i))
  intro j k
  exact hs (j, k) V g (c (j, k)) (hc (j, k))

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
