/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechCoefficientMap
import WeilConjectures.AlgebraicGeometry.EtaleTensorUnitSectionsNatural
import WeilConjectures.AlgebraicGeometry.EtaleAffineTensorCechVanishing
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleAffineOpenCechResolutionColumns

/-! # The fixed additive coefficient augmentation on vertical columns

Source: Stacks Project, Tags 03P2 and 01EQ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def additive_coordinate_iso {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ V : X.Etaleᵒᵖ, G.obj.obj V ≃+ Γ(V.unop.left, ⊤))
    (ha : ∀ (V W : X.Etaleᵒᵖ) (g : V ⟶ W) (x : G.obj.obj V),
      a W (G.obj.map g x) = g.unop.left.appTop (a V x)) :
    G ≅ X.etaleAdditiveSheaf :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun V ↦ ((a V).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun g ↦ by ext x; apply ULift.ext; exact ha _ _ g x))

private noncomputable def lifted_additive_coordinate_iso {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : ∀ V : X.Etaleᵒᵖ, G.obj.obj V ≃+ Γ(V.unop.left, ⊤))
    (ha : ∀ (V W : X.Etaleᵒᵖ) (g : V ⟶ W) (x : G.obj.obj V),
      a W (G.obj.map g x) = g.unop.left.appTop (a V x)) :
    (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj G ≅
      X.etaleAdditiveSheaf :=
  additive_coordinate_iso _ (fun V ↦ AddEquiv.ulift.trans (a V))
    (fun V W g x ↦ ha V W g x.down)

private theorem additive_affine_derived_vanishing (X : Scheme.{u})
    (W : X.Etale) (hW : IsAffine W.left) (q : ℕ) (hq : 0 < q) :
    IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
        (op W)).rightDerived q).obj X.etaleAdditiveSheaf) := by
  classical
  let F : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let : F.IsQuasicoherent := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  let G := (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    (etaleTensorSectionsSheaf (X := X) F)
  obtain ⟨b, hb, _⟩ := exists_etaleTensorUnit_sections_natural X
  let es := lifted_additive_coordinate_iso (X := X)
    (etaleTensorSectionsSheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)) b hb
  obtain ⟨hB, hcofinal⟩ := finiteAffineEtaleCechCover_basis X
  have hv := isZero_rightDerived_etale_of_cech_vanishing X
    {V | IsAffine V.left} (finiteAffineEtaleCechCover X) G
    (fun _ _ _ _ hf ↦ hf.2.2.2) hB hcofinal
    (fun V J Z f hf p hp ↦
      isZero_etaleTensorSectionsSheaf_ulift_cech X F V J Z f hf p hp)
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op W)
  exact ((E.rightDerived q).mapIso es).isZero_iff.mp (hv W hW q hq)



private theorem cechEvaluation_preservesFiniteLimits (X : Scheme.{u})
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    PreservesFiniteLimits (cechComplexFunctor (A := AddCommGrpCat.{u + 1}) U ⋙
      HomologicalComplex.eval _ (.up ℕ) n) := by
  let V := (Limits.FormalCoproduct.mk _ U).cech.obj (op (SimplexCategory.mk n))
  let T : Discrete V.I ⥤ X.Opensᵒᵖ :=
    Discrete.functor (fun t ↦ op (V.obj t))
  let F := cechComplexFunctor (A := AddCommGrpCat.{u + 1}) U ⋙
    HomologicalComplex.eval _ (.up ℕ) n
  let L := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj T ⋙ lim
  let e : F ≅ L := NatIso.ofComponents (fun P ↦ Pi.isoLimit (T ⋙ P)) (by
    intro P Q α
    apply limit.hom_ext
    intro ⟨t⟩
    simp [F, L, T, V, cechComplexFunctor, Limits.FormalCoproduct.cochainComplexFunctor,
      Limits.FormalCoproduct.cosimplicialObjectFunctor, Pi.isoLimit_hom_π,
      Limits.FormalCoproduct.evalOp])
  have : PreservesFiniteLimits L := inferInstance
  exact preservesFiniteLimits_of_natIso e.symm

private noncomputable def coefficient_sections_iso (X : Scheme.{u})
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
      (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf))).X n ≅
    ((cechComplexFunctor U).obj
      ((additiveCechOpenInclusion X).op ⋙ X.etaleAdditiveSheaf.obj)).X n := by
  let P := presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)
  let L := forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}
  let Z := fun y : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun l ↦ U (y l)))
  exact PreservesProduct.iso L Z ≪≫ Pi.mapIso (fun y ↦
    etaleAdditiveCoefficients.mapIso (X.restrictFunctorΓ.app
      (op (∏ᶜ fun l ↦ U (y l)))).symm)

private noncomputable def coefficient_sections_kernel (X : Scheme.{u})
    {ι : Type u} (U : ι → X.Opens)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ) :
    let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
        (additiveCechOpenInclusion X).op ⋙ cechComplexFunctor U ⋙
          HomologicalComplex.eval _ (.up ℕ) n
    IsLimit (KernelFork.ofι
      ((coefficient_sections_iso X U n).hom ≫ E.map (I.ι.f 0))
      (show (coefficient_sections_iso X U n).hom ≫ E.map (I.ι.f 0) ≫
          E.map (I.cocomplex.d 0 1) = 0 by
        rw [← E.map_comp, I.ι_f_zero_comp_complex_d, E.map_zero,
          comp_zero])) := by
  dsimp only
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      (additiveCechOpenInclusion X).op ⋙ cechComplexFunctor U ⋙
        HomologicalComplex.eval _ (.up ℕ) n
  have : PreservesFiniteLimits (cechComplexFunctor (A := AddCommGrpCat.{u + 1}) U ⋙
      HomologicalComplex.eval _ (.up ℕ) n) := cechEvaluation_preservesFiniteLimits X U n
  have : PreservesFiniteLimits E := inferInstance
  have hk := KernelFork.mapIsLimit _ I.isLimitKernelFork E
  exact IsLimit.ofIsoLimit hk
    (Fork.ext (coefficient_sections_iso X U n).symm (by simp; rfl))

private theorem coefficient_sections_coordinate (X : Scheme.{u})
    {ι : Type u} (U : ι → X.Opens)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ)
    (y : Fin (n + 1) → ι)
    (x : (((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
      (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf))).X n) :
    let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
        (additiveCechOpenInclusion X).op ⋙ cechComplexFunctor U ⋙
          HomologicalComplex.eval _ (.up ℕ) n
    ((coefficient_sections_iso X U n).hom ≫ E.map (I.ι.f 0) ≫
      Pi.π (fun y : Fin (n + 1) → ι ↦
        (I.cocomplex.X 0).obj.obj
          (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))) y) x =
      (I.ι.f 0).hom.app
        (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))
        (ULift.up ((X.restrictFunctorΓ.inv.app (op (∏ᶜ fun l ↦ U (y l)))).hom
          (TopCat.Presheaf.cechComplexFunctorπ U
            (presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)) n y x.down))) := by
  dsimp only
  change ((coefficient_sections_iso X U n).hom ≫
    Limits.Pi.map (fun y : Fin (n + 1) → ι ↦
      (I.ι.f 0).hom.app
        (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))) ≫ _) x = _
  rw [Pi.map_π, ← Category.assoc]
  dsimp only [coefficient_sections_iso, Iso.trans_hom]
  simp only [Category.assoc]
  erw [Pi.mapIso_hom_π_assoc, PreservesProduct.iso_hom, piComparison_comp_π_assoc]
  rfl


/-- Each fixed coefficient map augments its vertical resolution column by a
quasi-isomorphism when the tuple intersections are affine.
Source: Stacks Project, Theorem 59.22.4 (Tag 03P2), affine acyclicity, and
Lemma 20.11.2 (Tag 01EQ), the augmented vertical columns.
(blueprint: lem-pbc-additive-cech-coefficient-columns)

Proof: Fix n. For each tuple y the underlying open is the categorical product
of U(y l), equal to their infimum by the universal property in the poset of
opens. Thus hU makes this open affine. Evaluating I on this open computes
right-derived evaluation of the additive structure sheaf. Its positive
cohomology vanishes by affine quasi-coherent etale acyclicity: identify the
unit's tensor-section sheaf with additive structural sections using the
natural unit coordinates, apply finite affine etale Cech vanishing and the
Cech vanishing criterion. Left exactness of evaluation identifies degree-zero
homology with additive sections, through the evaluated resolution augmentation.
The inverse of restrictFunctorΓ is the canonical identification from ordinary
unit sections with these sections, including the ULift. Take the product over
y. Products in abelian groups are exact, so they preserve these homology
calculations, and forgetting scalars and lifting the universe commute with the
finite products in the ordinary Cech term. The resulting degree-zero map is
exactly additiveCechCoefficientMap, by its projections. Its composition with
the next differential vanishes by additiveCechCoefficientMap_vertical, so
fromSingle₀Equiv constructs the augmented column map. It is an isomorphism on
homology in degree zero and between zero objects in every positive degree.
There is no covering hypothesis: the reasoning is on individual affine
intersections. Empty tuple families give zero columns and empty intersections
have zero sections; the same proof applies in degree zero and to repeated opens. -/
theorem additiveCechCoefficientMap_column_quasiIso
    (X : Scheme.{u}) [X.IsSeparated] {ι : Type u} [Finite ι]
    (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ) :
    QuasiIso
      ((CochainComplex.fromSingle₀Equiv
        ((etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).X n)
        ((additiveCechCoefficientComplex U).X n)).symm
          ⟨additiveCechCoefficientMap U I n, additiveCechCoefficientMap_vertical U I n⟩) := by
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      (additiveCechOpenInclusion X).op ⋙ cechComplexFunctor U ⋙
        HomologicalComplex.eval _ (.up ℕ) n
  have heq : additiveCechCoefficientMap U I n =
      (coefficient_sections_iso X U n).hom ≫ E.map (I.ι.f 0) := by
    apply Pi.hom_ext
    intro y
    erw [additiveCechCoefficientMap, Pi.lift_comp_π]
    apply AddCommGrpCat.ext
    intro x
    exact (coefficient_sections_coordinate X U I n y x).symm
  have hk : IsLimit (KernelFork.ofι (additiveCechCoefficientMap U I n)
      (additiveCechCoefficientMap_vertical U I n)) := by
    apply IsLimit.ofIsoLimit (coefficient_sections_kernel X U I n)
    exact Fork.ext (Iso.refl _) (by
      change additiveCechCoefficientMap U I n = _
      exact heq)
  have hU₀ : ∀ j, IsAffineOpen (U j) := by
    intro j
    simpa using hU 0 (fun _ ↦ j)
  have hv := (etale_affineOpenCech_resolution_columns X (additiveCechOpenInclusion X)
    rfl U hU₀ X.etaleAdditiveSheaf (additive_affine_derived_vanishing X) I).2
  refine ⟨fun q ↦ ?_⟩
  cases q with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · change (ShortComplex.mk (additiveCechCoefficientMap U I n) _ _).Exact ∧
        Mono (additiveCechCoefficientMap U I n)
      exact ⟨ShortComplex.exact_of_f_is_kernel _ hk, mono_of_isLimit_fork hk⟩
    · rfl
    · rfl
    · change ((etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).X
        n).d 0 0 = 0
      simp
  | succ q =>
    rw [quasiIsoAt_iff_exactAt]
    · exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
        (hv (q + 1) (Nat.zero_lt_succ q) n)
    · apply CochainComplex.exactAt_succ_single_obj

end AlgebraicGeometry.Scheme.Modules
