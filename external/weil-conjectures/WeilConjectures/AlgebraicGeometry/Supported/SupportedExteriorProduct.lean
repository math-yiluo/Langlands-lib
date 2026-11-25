/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedSections
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.SixFunctors.OpenClosed.SupportedSections
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.OpenClosed.Points
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.CategoryTheory.Sites.SectionsWithSupport

/-!
# The supported exterior product

Source: blueprint, sec-smooth-purity/sk-prop-a1-kummer,
`proposition-purity-vector-bundles`, pulling back supported sections and tensoring them
(blueprint: proposition-purity-vector-bundles).

Supported coefficients are closed direct images of constant modules. The ordinary
adjunction is normalized by the quotient from constant coefficients. Its derived
adjunction and the coefficient tensor comparison specify the supported pairing.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u v w

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

/-- Cache the existing sheafification existence proof at the coefficient universe.
Source: the small-etale sheafification API (blueprint: proposition-purity-vector-bundles). -/
theorem supportedHasSheafify
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  GrothendieckTopology.hasSheafify_smallEtaleTopology (ModuleCat.{u + 1} A) X

/-- Cache the weak sheafification consequence of the existing exact sheafification.
Source: the small-etale sheafification API (blueprint: proposition-purity-vector-bundles). -/
theorem supportedHasWeakSheafify
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (GrothendieckTopology.hasSheafify_smallEtaleTopology (ModuleCat.{u + 1} A) X).isRightAdjoint

attribute [local instance] supportedHasSheafify supportedHasWeakSheafify

/-- Use the existing preadditive tensor structure without reopening sheafification
instance search under each tensor-complex binder.
Source: blueprint `proposition-purity-vector-bundles`, tensor construction
(blueprint: proposition-purity-vector-bundles). -/
noncomputable instance supportedSheaf_monoidalPreadditive (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) : MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  Sheaf.monoidalPreadditive

/-- The cochain tensor is the signed total tensor complex.
Source: Mathlib cochain monoidal structure (blueprint: proposition-purity-vector-bundles). -/
theorem supportedComplexTensor_eq
    {D : Type*} [Category.{w} D] [Abelian D] [HasColimitsOfSize.{0, 0} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    (P Q : CochainComplex D ℤ) : P ⊗ Q = HomologicalComplex.tensorObj P Q := by
  rfl

section TensorWrappers

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

/-- The existing monoidal sheafification property, with generic coefficients.
Source: blueprint tensor construction (blueprint: proposition-purity-vector-bundles). -/
noncomputable instance supportedSheaf_isMonoidalGeneric (X : Scheme.{u}) :
    (X.smallEtaleTopology.W (A := C)).IsMonoidal := GrothendieckTopology.W.monoidal

/-- The existing preadditive tensor structure, with generic coefficients.
Source: blueprint tensor construction (blueprint: proposition-purity-vector-bundles). -/
noncomputable instance supportedSheaf_monoidalPreadditiveGeneric (X : Scheme.{u}) :
    MonoidalPreadditive (Sheaf X.smallEtaleTopology C) := Sheaf.monoidalPreadditive

/-- The existing sheaf tensor bifunctor at a variable scheme.
Source: blueprint constant tensor pairing (blueprint: proposition-purity-vector-bundles). -/
@[implicit_reducible]
noncomputable def supportedSheafTensorGeneric (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology C :=
      curriedTensor _

/-- The signed complex tensor at a variable scheme, using the upstream structure.
Source: blueprint signed tensor pairing (blueprint: proposition-purity-vector-bundles). -/
@[implicit_reducible]
noncomputable def supportedComplexTensorGeneric (X : Scheme.{u}) :
    CochainComplex (Sheaf X.smallEtaleTopology C) ℤ ⥤
      CochainComplex (Sheaf X.smallEtaleTopology C) ℤ ⥤
        CochainComplex (Sheaf X.smallEtaleTopology C) ℤ := curriedTensor _

/-- The signed total tensor object, using the existing total complex construction.
Source: blueprint signed tensor construction (blueprint: proposition-purity-vector-bundles). -/
noncomputable def supportedTotalTensorGeneric (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ) :=
  HomologicalComplex.tensorObj (C := Sheaf X.smallEtaleTopology C) (c := .up ℤ) P Q

end TensorWrappers

/-- Closed supported constant coefficients. Source: blueprint
`proposition-purity-vector-bundles`, supported-section construction
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def supportedCoefficients (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    ModuleCat.{u + 1} A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    lowerStar (ModuleCat.{u + 1} A) i

/-- The quotient from constant coefficients to closed supported coefficients.
Source: blueprint `proposition-purity-vector-bundles`, open-closed coefficient sequence
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def supportedCoefficientQuotient (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) (M : ModuleCat.{u + 1} A) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⟶
      (supportedCoefficients A i).obj M :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).hom.app M)

/-- Additivity of closed supported coefficients. Source: blueprint
`proposition-purity-vector-bundles` (blueprint: proposition-purity-vector-bundles). -/
noncomputable instance supportedCoefficients_additive
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (supportedCoefficients A i).Additive :=
  inferInstanceAs ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    lowerStar (ModuleCat.{u + 1} A) i).Additive)

/-- Exactness of closed supported coefficients.
Source: blueprint `proposition-purity-vector-bundles`, closed-support construction
(blueprint: proposition-purity-vector-bundles).
Proof: at a geometric point the closed direct image of a constant module has stalk
that module on the closed subset and zero outside. Both functors on modules are exact.
Exact and conservative geometric stalks detect finite limits and finite colimits.
The same argument handles the empty closed subscheme. -/
theorem supportedCoefficients_exact (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteLimits (supportedCoefficients A i) ∧
      PreservesFiniteColimits (supportedCoefficients A i) := by
  constructor <;> unfold supportedCoefficients <;> infer_instance

/-- The finite-limit instance from closed-support exactness. Source: blueprint
`proposition-purity-vector-bundles` (blueprint: proposition-purity-vector-bundles). -/
noncomputable instance supportedCoefficients_preservesFiniteLimits
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteLimits (supportedCoefficients A i) := (supportedCoefficients_exact A i).1

/-- The finite-colimit instance from closed-support exactness. Source: blueprint
`proposition-purity-vector-bundles` (blueprint: proposition-purity-vector-bundles). -/
noncomputable instance supportedCoefficients_preservesFiniteColimits
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteColimits (supportedCoefficients A i) := (supportedCoefficients_exact A i).2

section OrdinaryAdjunctionProof

set_option backward.isDefEq.respectTransparency false

private theorem adjunctionNormalization
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {LZ : C ⥤ E} {RZ : E ⥤ C}
    {I : E ⥤ D} {J : D ⥤ E} {S : D ⥤ C}
    (ax : L ⊣ R) (az : LZ ⊣ RZ) (b : I ⊣ J)
    (γ : I ⋙ R ≅ RZ) (ε : J ⋙ RZ ≅ S) (δ : S ⟶ R)
    (M : C) (F : D) (q : L.obj M ⟶ I.obj (LZ.obj M))
    (hq : ax.unit.app M ≫ R.map q ≫ γ.hom.app (LZ.obj M) = az.unit.app M)
    (hc : ε.hom.app F ≫ δ.app F = γ.inv.app (J.obj F) ≫ R.map (b.counit.app F))
    (f : M ⟶ S.obj F) :
    q ≫ (((az.comp b).ofNatIsoRight ε).homEquiv M F).symm f =
      (ax.homEquiv M F).symm (f ≫ δ.app F) := by
  have hq' : ax.unit.app M ≫ R.map q =
      az.unit.app M ≫ γ.inv.app (LZ.obj M) := by
    erw [← hq]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    dsimp only [Functor.comp_obj]
    simp only [Category.comp_id]
  apply (ax.homEquiv M F).injective
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_ofNatIsoRight_symm_apply,
    Adjunction.comp_homEquiv]
  simp only [Equiv.symm_trans_apply]
  erw [Adjunction.homEquiv_apply, Adjunction.homEquiv_counit]
  erw [Functor.map_comp, Functor.map_comp, ← Category.assoc, hq', Category.assoc,
    ← γ.inv.naturality_assoc]
  erw [← Category.assoc, ← Adjunction.homEquiv_apply, Equiv.apply_symm_apply]
  erw [Category.assoc, ← hc, Iso.inv_hom_id_app_assoc]

private lemma constantUnit_terminal
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C] {Z X : Scheme.{u}}
    (i : Z ⟶ X) (M : C) :
    (constantSheafAdj X.smallEtaleTopology C
      terminalIsTerminal).unit.app M ≫
      ((sheafSections X.smallEtaleTopology C).obj
        (op (⊤_ X.Etale))).map (((upperStarLowerStarAdjunction C i).unit.app _ ≫
          (lowerStar C i).map ((Scheme.upperStarConstantSheafIso C i).hom.app M))) ≫
      (lowerStarCompSheafSectionsTerminalIso C i).hom.app _ =
    (constantSheafAdj Z.smallEtaleTopology C
      terminalIsTerminal).unit.app M := by
  let ax := constantSheafAdj X.smallEtaleTopology C terminalIsTerminal
  let az := constantSheafAdj Z.smallEtaleTopology C terminalIsTerminal
  let p := upperStarLowerStarAdjunction C i
  let e := lowerStarCompSheafSectionsTerminalIso C i
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((ax.comp p).ofNatIsoRight e) az M
  rw [Adjunction.homEquiv_unit] at h
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] at h
  change (ax.comp p).unit.app M ≫ e.hom.app _ ≫
    ((sheafSections Z.smallEtaleTopology C).obj
      (op (⊤_ Z.Etale))).map ((Scheme.upperStarConstantSheafIso
        C i).hom.app M) = az.unit.app M at h
  rw [← h]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  erw [← e.hom.naturality]
  rfl

private lemma constantUnit_global
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C] {Z X : Scheme.{u}}
    (i : Z ⟶ X) (M : C) :
    (constantSheafΓAdj X.smallEtaleTopology C).unit.app M ≫
      (Sheaf.Γ X.smallEtaleTopology C).map
        (((upperStarLowerStarAdjunction C i).unit.app _ ≫
          (lowerStar C i).map ((Scheme.upperStarConstantSheafIso C i).hom.app M))) ≫
      (lowerStarCompGlobalSectionsIso C i).hom.app _ =
    (constantSheafΓAdj Z.smallEtaleTopology C).unit.app M := by
  let nx : Sheaf.Γ X.smallEtaleTopology C ≅
      (sheafSections X.smallEtaleTopology C).obj
        (op (⊤_ X.Etale)) := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology C terminalIsTerminal
  let nz : Sheaf.Γ Z.smallEtaleTopology C ≅
      (sheafSections Z.smallEtaleTopology C).obj
        (op (⊤_ Z.Etale)) := Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology C terminalIsTerminal
  let e := lowerStarCompSheafSectionsTerminalIso C i
  have hx := (constantSheafΓAdj X.smallEtaleTopology C).unit_rightAdjointUniq_hom_app
    (constantSheafAdj X.smallEtaleTopology C terminalIsTerminal) M
  have hz := (constantSheafΓAdj Z.smallEtaleTopology C).unit_rightAdjointUniq_hom_app
    (constantSheafAdj Z.smallEtaleTopology C terminalIsTerminal) M
  have hinj : Function.Injective
      (fun f : M ⟶ (Sheaf.Γ Z.smallEtaleTopology C).obj
        ((constantSheaf Z.smallEtaleTopology C).obj M) ↦
        f ≫ nz.hom.app ((constantSheaf Z.smallEtaleTopology C).obj M)) :=
    fun f g h ↦ (cancel_mono _).1 h
  apply hinj
  simp only [nz, lowerStarCompGlobalSectionsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.assoc]
  erw [nx.hom.naturality_assoc]
  erw [Iso.inv_hom_id_app]
  simp only [Category.comp_id]
  rw [← Category.assoc]
  erw [hx, hz]
  exact constantUnit_terminal C i M

section Site

variable {X : Scheme.{u}}

/-- A morphism of étale `X`-schemes whose underlying morphism of schemes is an isomorphism is an
isomorphism. -/
private lemma aux_isIso_of_isIso_left {V W : X.Etale} (f : V ⟶ W)
    (hf : IsIso f.left) : IsIso f := by
  have : IsIso ((Over.forget X).map ((Scheme.Etale.forget X).map f)) := hf
  have : IsIso ((Scheme.Etale.forget X).map f) :=
    isIso_of_reflects_iso _ (Over.forget X)
  exact isIso_of_reflects_iso f (Scheme.Etale.forget X)

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The counit `U ×_X U ⟶ U` at `U` of the adjunction between composition with and base change
along the open immersion `j` is an isomorphism, `j` being a monomorphism. -/
private theorem aux_isIso_mapPullbackAdj_counit_app_mk :
    IsIso ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial).counit.app
      (Scheme.Etale.mk j)) :=
  aux_isIso_of_isIso_left _ (inferInstanceAs (IsIso (pullback.fst j j)))

attribute [local instance] aux_isIso_mapPullbackAdj_counit_app_mk

/-- The base change along the open immersion `j` of the map from `U` to the terminal étale
`X`-scheme `X` is an isomorphism `U ×_X U ≅ X ×_X U`, both being isomorphic to `U` over `U`. -/
private theorem aux_isIso_overPullback_map_isTerminalMkId_from :
    IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).map
      ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j))) := by
  refine aux_isIso_of_isIso_left _ ?_
  have h := MorphismProperty.Over.w ((MorphismProperty.Over.pullback @Etale ⊤ j).map
    ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j)))
  have : IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).obj (Scheme.Etale.mk j)).hom :=
    inferInstanceAs (IsIso (pullback.snd j j))
  have : IsIso ((MorphismProperty.Over.pullback @Etale ⊤ j).obj (Scheme.Etale.mk (𝟙 X))).hom :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 X) j))
  exact IsIso.of_isIso_fac_right h

end Site

variable (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]

section Restriction

attribute [local instance] aux_isIso_mapPullbackAdj_counit_app_mk

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

attribute [local instance] aux_isIso_overPullback_map_isTerminalMkId_from

omit [Abelian C] [IsGrothendieckAbelian.{u + 1} C] in
/-- For a sheaf `G` on `U`, the restriction `(j_* G)(X) ⟶ (j_* G)(U)` along the open immersion
`j` is an isomorphism: both are the sections of `G` over `U`. -/
private theorem aux_isIso_lowerStar_obj_map_isTerminalMkId_from (G : Sheaf U.smallEtaleTopology C) :
    IsIso (((j)_*[C].obj G).obj.map ((Scheme.Etale.isTerminalMkId X).from
      (Scheme.Etale.mk j)).op) := by
  rw [lowerStar_obj_val_map]
  infer_instance

attribute [local instance] aux_isIso_lowerStar_obj_map_isTerminalMkId_from

omit [Abelian C] [IsGrothendieckAbelian.{u + 1} C] in
/-- For a sheaf `M` on `X`, the unit `M ⟶ j_* j^* M` of the restriction along the open immersion
`j` is an isomorphism on the sections over `U`. -/
private theorem aux_isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_mk
    (M : Sheaf X.smallEtaleTopology C) :
    IsIso (((openImmersionRestrictionLowerStarAdjunction C j).unit.app M).hom.app
      (op (Scheme.Etale.mk j))) :=
  inferInstanceAs (IsIso (𝟙 _ ≫ M.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
    inferInstance trivial).counit.app (Scheme.Etale.mk j)).op ≫ 𝟙 _))

attribute [local instance] aux_isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_mk

/-- The restriction `Γ(X, M) ⟶ M(U)` from the global sections to the sections over `U` is the
restriction along the map from `U` to the terminal étale `X`-scheme, preceded by the isomorphism
`Γ(X, M) ≅ M(X)`. -/
private lemma aux_ΓRes_eq (M : Sheaf X.smallEtaleTopology C) :
    M.ΓRes (op (Scheme.Etale.mk j)) =
      M.ΓRes (op (Scheme.Etale.mk (𝟙 X))) ≫
        M.obj.map ((Scheme.Etale.isTerminalMkId X).from (Scheme.Etale.mk j)).op :=
  (M.ΓRes_map _).symm

private theorem aux_isIso_ΓRes_terminal (M : Sheaf X.smallEtaleTopology C) :
    IsIso (M.ΓRes (op (Scheme.Etale.mk (𝟙 X)))) :=
  M.isLimitConeΓ.isIso_π_app_of_isInitial _ (Scheme.Etale.isTerminalMkId X).op

attribute [local instance] aux_isIso_ΓRes_terminal
end Restriction

section Sections

attribute [local instance] aux_isIso_lowerStar_obj_map_isTerminalMkId_from
  aux_isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_mk
  aux_isIso_ΓRes_terminal
variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

omit [HasSmallSiteSheafify C] in
/-- For a sheaf `G` on `U`, the restriction `Γ(X, j_* G) ⟶ (j_* G)(U)` is an isomorphism. -/
private theorem normalization_isIso_ΓRes_lowerStar_obj (G : Sheaf U.smallEtaleTopology C) :
    IsIso (((j)_*[C].obj G).ΓRes (op (Scheme.Etale.mk j))) := by
  rw [aux_ΓRes_eq]
  infer_instance

attribute [local instance] normalization_isIso_ΓRes_lowerStar_obj

omit [HasSmallSiteSheafify C] in
/-- The sections over `U` of the inclusion `𝒢_Z M ⟶ M` of the supported sections vanish, so the
global sections of the inclusion restrict to zero on `U`. -/
@[reassoc]
private lemma normalization_ΓMap_sectionsWithSupportι_app_comp_ΓRes
    (M : Sheaf X.smallEtaleTopology C) :
    (Sheaf.Γ X.smallEtaleTopology C).map ((sectionsWithSupportι C j).app M) ≫
      M.ΓRes (op (Scheme.Etale.mk j)) = 0 := by
  erw [Sheaf.ΓRes_naturality]
  have : IsZero (((sectionsWithSupport C j).obj M).obj.obj (op (Scheme.Etale.mk j))) :=
    isZero_obj_of_isZero_upperStar (isZero_upperStar_sectionsWithSupport C j M) _
      subset_rfl
  rw [this.eq_of_tgt (Sheaf.ΓRes _ _) 0, zero_comp]

omit [HasSmallSiteSheafify C] in
/-- The global sections of the unit `M ⟶ j_* j^* M` are the restriction `Γ(X, M) ⟶ M(U)`
followed by the identification `M(U) ≅ (j_* j^* M)(U) ≅ Γ(X, j_* j^* M)`. -/
private lemma normalization_ΓMap_unit_app_eq (M : Sheaf X.smallEtaleTopology C) :
    (Sheaf.Γ X.smallEtaleTopology C).map ((upperStarLowerStarAdjunction C j).unit.app M) =
      M.ΓRes (op (Scheme.Etale.mk j)) ≫
        ((openImmersionRestrictionLowerStarAdjunction C j).unit.app M).hom.app
          (op (Scheme.Etale.mk j)) ≫
        inv (((j)_*[C].obj ((openImmersionRestriction C j).obj M)).ΓRes
          (op (Scheme.Etale.mk j))) ≫
        (Sheaf.Γ X.smallEtaleTopology C).map ((j)_*[C].map
          (((upperStarLowerStarAdjunction C j).leftAdjointUniq
            (openImmersionRestrictionLowerStarAdjunction C j)).inv.app M)) := by
  have h₁ := Sheaf.ΓRes_naturality ((openImmersionRestrictionLowerStarAdjunction C j).unit.app M)
    (op (Scheme.Etale.mk j))
  rw [← reassoc_of% h₁, IsIso.hom_inv_id_assoc, ← Functor.map_comp]
  congr 1
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction C j)
    (openImmersionRestrictionLowerStarAdjunction C j), assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp

/-- The global sections of the inclusion `𝒢_Z M ⟶ M` of the sections supported on the closed
complement `Z` of `j` form a kernel of the restriction `Γ(X, M) ⟶ M(U)`: `Γ` preserves the kernel
`𝒢_Z M` of `M ⟶ j_* j^* M`, and `Γ(X, M) ⟶ Γ(X, j_* j^* M)` is the restriction `Γ(X, M) ⟶ M(U)`
followed by an isomorphism (`AlgebraicGeometry.Etale.normalization_ΓMap_unit_app_eq`). -/
private noncomputable def normalization_isLimitΓMapSectionsWithSupportι
    (M : Sheaf X.smallEtaleTopology C) :
    IsLimit (KernelFork.ofι _ (normalization_ΓMap_sectionsWithSupportι_app_comp_ΓRes C j M)) :=
  isKernelOfComp _ _ (KernelFork.mapIsLimit _
    (kernelIsKernel ((upperStarLowerStarAdjunction C j).unit.app M))
      (Sheaf.Γ X.smallEtaleTopology C))
    (normalization_ΓMap_sectionsWithSupportι_app_comp_ΓRes C j M)
    (normalization_ΓMap_unit_app_eq C j M).symm

end Sections

section SupportCohomology
variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C]

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The sections with support `Γ_Z(X, M) ⟶ Γ(X, M)` form a kernel of the restriction
`Γ(X, M) ⟶ M(U)`. -/
private noncomputable def normalization_isLimitSectionsWithSupport
    (M : Sheaf X.smallEtaleTopology C) :
    IsLimit (KernelFork.ofι _ (Sheaf.ΓSupportι_app_comp_ΓRes X.smallEtaleTopology C
      (op (Scheme.Etale.mk i.openComplement.ι)) M)) :=
  KernelFork.mapIsLimit _ (kernelIsKernel (Sheaf.natTransΓRes X.smallEtaleTopology C
    (op (Scheme.Etale.mk i.openComplement.ι)))) ((evaluation _ C).obj M)

/-- The sections with support in `Z` are the global sections of the subsheaf of sections
supported on `Z`: `Γ(X, 𝒢_Z M) ≅ Γ_Z(X, M)`, compatibly with the inclusions into `Γ(X, M)`. -/
private noncomputable def normalization_sectionsWithSupportCompΓIso :
    sectionsWithSupport C i.openComplement.ι ⋙ Sheaf.Γ X.smallEtaleTopology C ≅
      kernel (Sheaf.natTransΓRes X.smallEtaleTopology C
        (op (Scheme.Etale.mk i.openComplement.ι))) :=
  NatIso.ofComponents
    (fun M ↦
      (normalization_isLimitΓMapSectionsWithSupportι C i.openComplement.ι M).conePointUniqueUpToIso
      (normalization_isLimitSectionsWithSupport C i M))
    (fun {M N} f ↦ by
      rw [← cancel_mono ((Sheaf.ΓSupportι X.smallEtaleTopology C _).app N)]
      have h₁ := (normalization_isLimitΓMapSectionsWithSupportι C i.openComplement.ι
        M).conePointUniqueUpToIso_hom_comp (normalization_isLimitSectionsWithSupport C i M) .zero
      have h₂ := (normalization_isLimitΓMapSectionsWithSupportι C i.openComplement.ι
        N).conePointUniqueUpToIso_hom_comp (normalization_isLimitSectionsWithSupport C i N) .zero
      simp only [KernelFork.ofι, Fork.ofι_π_app] at h₁ h₂
      simp only [Functor.comp_map, assoc, h₂]
      erw [(Sheaf.ΓSupportι X.smallEtaleTopology C _).naturality f, reassoc_of% h₁]
      erw [← Functor.map_comp, ← Functor.map_comp,
        ← (sectionsWithSupportι C i.openComplement.ι).naturality f])

omit [HasSmallSiteSheafify C] in
@[reassoc (attr := simp)]
private lemma normalization_sectionsWithSupportCompΓIso_hom_app_comp
    (M : Sheaf X.smallEtaleTopology C) :
    (normalization_sectionsWithSupportCompΓIso C i).hom.app M ≫
        (Sheaf.ΓSupportι X.smallEtaleTopology C _).app M =
      (Sheaf.Γ X.smallEtaleTopology C).map ((sectionsWithSupportι C _).app M) := by
  let e := normalization_isLimitΓMapSectionsWithSupportι C i.openComplement.ι M
  have h := e.conePointUniqueUpToIso_hom_comp
    (normalization_isLimitSectionsWithSupport C i M) WalkingParallelPair.zero
  simp only [KernelFork.ofι, Fork.ofι_π_app] at h
  exact h

/-- `Γ_Z(X, M) ≅ Γ(Z, i^! M)`: the sections with support in `Z` are the global sections of the
exceptional inverse image `i^! M` (`AlgebraicGeometry.Etale.closedUpperShriek`), through
`Γ(Z, i^! M) ≅ Γ(X, i_* i^! M) ≅ Γ(X, 𝒢_Z M)`. -/
private noncomputable def normalization_closedUpperShriekCompΓIso :
    closedUpperShriek C i i.openComplement.ι ⋙ Sheaf.Γ Z.smallEtaleTopology C ≅
      kernel (Sheaf.natTransΓRes X.smallEtaleTopology C
        (op (Scheme.Etale.mk i.openComplement.ι))) :=
  Functor.isoWhiskerLeft _ (lowerStarCompGlobalSectionsIso C i).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (closedUpperShriekCompLowerStarIso C i _
      i.range_eq_compl_range_openComplement_ι) _ ≪≫
    normalization_sectionsWithSupportCompΓIso C i

omit [HasSmallSiteSheafify C] in
private lemma normalization_closedUpperShriekCompΓIso_hom_comp
    (F : Sheaf X.smallEtaleTopology C) :
    (normalization_closedUpperShriekCompΓIso C i).hom.app F ≫
      (Sheaf.ΓSupportι X.smallEtaleTopology C
        (op (Scheme.Etale.mk i.openComplement.ι))).app F =
      (lowerStarCompGlobalSectionsIso C i).inv.app
        ((closedUpperShriek C i i.openComplement.ι).obj F) ≫
      (Sheaf.Γ X.smallEtaleTopology C).map
        ((lowerStarClosedUpperShriekAdjunction C i i.openComplement.ι
          i.range_eq_compl_range_openComplement_ι).counit.app F) := by
  simp only [normalization_closedUpperShriekCompΓIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.id_comp, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.assoc,
    normalization_sectionsWithSupportCompΓIso_hom_app_comp,
    lowerStarClosedUpperShriekAdjunction_counit_app, Functor.map_comp]

end SupportCohomology

private theorem closedUnit_epi
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app G) := by
  let C := ModuleCat.{u + 1} A
  let adj := upperStarLowerStarAdjunction C i
  let j := i.openComplement.ι
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    simp [j, Scheme.Hom.coe_openComplement]
  refine Preadditive.epi_of_isZero_cokernel _
    (isZero_of_isZero_upperStar (j := j) i hij ?_ ?_)
  · refine IsZero.of_iso ?_ (PreservesCokernel.iso (upperStar C j) (adj.unit.app G))
    refine IsZero.of_epi (cokernel.π _) ?_
    exact isZero_upperStar_lowerStar_of_disjoint_range C j i
      (by rw [hij]; exact disjoint_compl_right) _
  · refine IsZero.of_iso ?_ (PreservesCokernel.iso (upperStar C i) (adj.unit.app G))
    have : IsIso ((upperStar C i).map (adj.unit.app G)) := by
      have : IsIso ((upperStar C i).map (adj.unit.app G) ≫ adj.counit.app _) := by
        rw [adj.left_triangle_components G]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
    exact isZero_cokernel_of_epi _

private theorem coefficientQuotient_epi
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (M : ModuleCat.{u + 1} A) :
    Epi (supportedCoefficientQuotient A i M) := by
  change Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app _ ≫
    (lowerStar (ModuleCat.{u + 1} A) i).map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).hom.app M))
  have := closedUnit_epi A i
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)
  infer_instance

private theorem ordinaryAdjunctionExists
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ a : supportedCoefficients A i ⊣ supportedEtaleSections A X i.openComplement,
      ∀ (M : ModuleCat.{u + 1} A)
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
        (f : M ⟶ (supportedEtaleSections A X i.openComplement).obj F),
      supportedCoefficientQuotient A i M ≫ (a.homEquiv M F).symm f =
        ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv M F).symm
          (f ≫ (supportedEtaleSectionsι A X i.openComplement).app F) := by
  let C := ModuleCat.{u + 1} A
  let b := lowerStarClosedUpperShriekAdjunction C i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι
  let e := normalization_closedUpperShriekCompΓIso C i
  let a : supportedCoefficients A i ⊣ supportedEtaleSections A X i.openComplement :=
    ((constantSheafΓAdj Z.smallEtaleTopology C).comp b).ofNatIsoRight e
  refine ⟨a, ?_⟩
  intro M F f
  exact adjunctionNormalization (constantSheafΓAdj X.smallEtaleTopology C)
    (constantSheafΓAdj Z.smallEtaleTopology C) b (lowerStarCompGlobalSectionsIso C i)
    e (supportedEtaleSectionsι A X i.openComplement) M F
    (supportedCoefficientQuotient A i M) (constantUnit_global C i M)
    (normalization_closedUpperShriekCompΓIso_hom_comp C i F) f
end OrdinaryAdjunctionProof

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary adjunction, uniquely normalized by inclusion of the support kernel.
Source: blueprint `proposition-purity-vector-bundles`, supported-section construction
(blueprint: proposition-purity-vector-bundles).
Proof: apply Hom into F to the open-closed sequence of constant M. The kernel of
restriction is Hom from M into the kernel defining supported sections. The quotient
is epic, so precomposition determines the Hom equivalence uniquely. Naturality of
restriction gives naturality in both variables and hence the adjunction. -/
theorem exists_unique_supportedCoefficientAdjunction
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃! a : supportedCoefficients A i ⊣ supportedEtaleSections A X i.openComplement,
      ∀ (M : ModuleCat.{u + 1} A)
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
        (f : M ⟶ (supportedEtaleSections A X i.openComplement).obj F),
      supportedCoefficientQuotient A i M ≫ (a.homEquiv M F).symm f =
        ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv M F).symm
          (f ≫ (supportedEtaleSectionsι A X i.openComplement).app F) := by
  obtain ⟨a, ha⟩ := ordinaryAdjunctionExists A i
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply Adjunction.ext_counit
  apply NatTrans.ext
  funext F
  let M := (supportedEtaleSections A X i.openComplement).obj F
  have := coefficientQuotient_epi A i M
  have h := (cancel_epi (supportedCoefficientQuotient A i M)).1
    ((ha' M F (𝟙 _)).trans (ha M F (𝟙 _)).symm)
  simp only [Adjunction.homEquiv_symm_apply] at h
  erw [(supportedCoefficients A i).map_id M, Category.id_comp] at h
  exact h

/-- Canonical ordinary supported-coefficient adjunction, selected from its unique
normalization. Source: blueprint `proposition-purity-vector-bundles`
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def supportedCoefficientAdjunction
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    supportedCoefficients A i ⊣ supportedEtaleSections A X i.openComplement :=
  (exists_unique_supportedCoefficientAdjunction A i).choose

/-- The unbounded support functor, extending the bounded-below injective construction.
Source: blueprint `proposition-purity-vector-bundles`, derived support resolutions
(blueprint: proposition-purity-vector-bundles). -/
noncomputable abbrev supportedSectionsDerived
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :=
  (supportedEtaleSections A X i.openComplement).rightDerivedFunctor

/-- Derive the normalized ordinary adjunction with its exact left adjoint.
Source: blueprint `proposition-purity-vector-bundles`, K-flat and injective derivation
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def supportedCoefficientDerivedAdjunction
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (supportedCoefficients A i).mapDerivedCategory ⊣ supportedSectionsDerived A i :=
  (supportedCoefficientAdjunction A i).mapDerivedCategoryRightDerivedAdjunction

/-- The closed immersion of the product of the two supports.
Source: blueprint `proposition-purity-vector-bundles`
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def supportedProductImmersion {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y) :
    pullback (i ≫ f) (j ≫ g) ⟶ pullback f g :=
  pullback.map (i ≫ f) (j ≫ g) f g i j (𝟙 B) (by simp) (by simp)

/-- Closedness of the product support. Source: blueprint
`proposition-purity-vector-bundles` (blueprint: proposition-purity-vector-bundles).
Proof: the product map is the composite of the two base changes of the closed
immersions. Closed immersions are stable under base change and composition. -/
@[instance]
theorem supportedProductImmersion_isClosedImmersion {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsClosedImmersion (supportedProductImmersion f g i j) := by
  set_option backward.isDefEq.respectTransparency false in
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (inferInstanceAs (IsClosedImmersion i))
      (inferInstanceAs (IsClosedImmersion j)) rfl rfl

/-- Supported coefficients pulled back along the first projection.
Source: blueprint `proposition-purity-vector-bundles`
(blueprint: proposition-purity-vector-bundles). -/
noncomputable abbrev supportedFirstCoefficients (A : Type (u + 1)) [CommRing A]
    {B X Y Z : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) :=
  supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)

/-- Supported coefficients pulled back along the second projection.
Source: blueprint `proposition-purity-vector-bundles`
(blueprint: proposition-purity-vector-bundles). -/
noncomputable abbrev supportedSecondCoefficients (A : Type (u + 1)) [CommRing A]
    {B X Y W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (j : W ⟶ Y) :=
  supportedCoefficients A j ⋙ upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)

attribute [local irreducible] HomologicalComplex₂.total

section CoefficientTensorProof

attribute [local instance] supportedHasSheafify supportedHasWeakSheafify

end CoefficientTensorProof

section ComplexTensorProof

attribute [local instance] supportedHasSheafify supportedHasWeakSheafify

end ComplexTensorProof

/-- Morphisms from the image of a tensor complex to the tensor of the two images.
Source: blueprint total tensor construction (blueprint: proposition-purity-vector-bundles). -/
noncomputable def supportedComplexComparisonHom
    {D : Type*} [Category.{w} D] {E : Type*} [Category.{w} E]
    [Preadditive D] [Preadditive E] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    (G G₁ G₂ : D ⥤ E) [G.Additive] [G₁.Additive] [G₂.Additive]
    (P Q : CochainComplex D ℤ) : Type _ :=
     (G.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ⟶
        HomologicalComplex.tensorObj
          ((G₁.mapHomologicalComplex (.up ℤ)).obj P)
          ((G₂.mapHomologicalComplex (.up ℤ)).obj Q)

/-- Normalization on all bidegree summands of a tensor-complex comparison.
Source: blueprint signed total tensor construction
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def supportedComplexComparisonCondition
    {D : Type*} [Category.{w} D] {E : Type*} [Category.{w} E]
    [Preadditive D] [Preadditive E] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    (G G₁ G₂ : D ⥤ E) [G.Additive] [G₁.Additive] [G₂.Additive]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ E).obj G₁).obj G₂).obj (curriedTensor E))
    (P Q : CochainComplex D ℤ)
    (t : supportedComplexComparisonHom G G₁ G₂ P Q) : Prop :=
      ∀ (r s n : ℤ) (h : r + s = n),
        G.map (HomologicalComplex.ιTensorObj P Q r s n h) ≫ t.f n =
          (τ.app (P.X r)).app (Q.X s) ≫ HomologicalComplex.ιTensorObj
            ((G₁.mapHomologicalComplex (.up ℤ)).obj P)
            ((G₂.mapHomologicalComplex (.up ℤ)).obj Q) r s n h

section AbstractDerivedTensor

variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type w} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [HasDerivedCategory.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]

/-- The natural transformation of signed tensor complexes induced by a coefficient pairing.
Source: blueprint signed tensor construction (blueprint: proposition-purity-vector-bundles). -/
noncomputable def supportedComplexComparisonNatTrans
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesColimitsOfSize.{0, 0} G]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F₁).obj F₂).obj (curriedTensor D)) :
    (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _) :=
  HomologicalComplex.mapBifunctorComparisonNatTrans τ (.up ℤ)

/-- A signed tensor comparison, constructed through the totalization bifunctor.
Source: blueprint signed tensor construction (blueprint: proposition-purity-vector-bundles). -/
noncomputable def supportedComplexComparison
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesColimitsOfSize.{0, 0} G]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F₁).obj F₂).obj (curriedTensor D))
    (P Q : CochainComplex C ℤ) : supportedComplexComparisonHom G F₁ F₂ P Q :=
  ((supportedComplexComparisonNatTrans G F₁ F₂ τ).app P).app Q

private theorem tensorLocalization_isIso (P Q : CochainComplex D ℤ)
    (hQ : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat Q) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient D (.up ℤ)).obj P)
      ((HomotopyCategory.quotient D (.up ℤ)).obj Q)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
      (HomotopyCategory.quasiIso D (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff Q).2 hQ)
  change IsIso ((_ ⊗ₘ _) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
  infer_instance

/-- Families of morphisms between the derived tensor images.
Source: blueprint derived tensor comparison (blueprint: proposition-purity-vector-bundles). -/
noncomputable def supportedDerivedComparisonHom
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂] : Type _ :=
  ∀ M N : DerivedCategory C,
      G.mapDerivedCategory.obj (M ⊗ N) ⟶
        F₁.mapDerivedCategory.obj M ⊗ F₂.mapDerivedCategory.obj N

/-- Naturality and normalization on all complex models, retaining the signed total tensor.
Source: blueprint derived tensor comparison (blueprint: proposition-purity-vector-bundles). -/
noncomputable def supportedDerivedComparisonCondition
    (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _))
    (t : supportedDerivedComparisonHom G F₁ F₂) : Prop :=
  (∀ (M M' N N' : DerivedCategory C) (a : M ⟶ M') (b : N ⟶ N'),
        G.mapDerivedCategory.map (a ⊗ₘ b) ≫ t M' N' =
          t M N ≫ (F₁.mapDerivedCategory.map a ⊗ₘ F₂.mapDerivedCategory.map b)) ∧
      (∀ P Q : CochainComplex C ℤ,
        G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          G.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
          DerivedCategory.Q.map ((τ.app P).app Q) =
        t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
          (F₁.mapDerivedCategoryFactors.hom.app P ⊗ₘ
            F₂.mapDerivedCategoryFactors.hom.app Q) ≫
          (Functor.LaxMonoidal.μ DerivedCategory.Q
            ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
            ((F₂.mapHomologicalComplex (.up ℤ)).obj Q) ≫
            DerivedCategory.Q.map (eqToHom (supportedComplexTensor_eq
              ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
              ((F₂.mapHomologicalComplex (.up ℤ)).obj Q)))))

end AbstractDerivedTensor

attribute [local irreducible] supportedDerivedComparisonHom
  supportedDerivedComparisonCondition supportedComplexComparisonHom
  supportedComplexComparisonCondition

section SchemeComparisons

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] (T : Scheme.{u})
  (G F₁ F₂ : C ⥤ Sheaf T.smallEtaleTopology C)
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]

variable [G.IsLeftAdjoint]

section ComparisonSpec

attribute [local semireducible] supportedComplexComparisonHom

end ComparisonSpec

end SchemeComparisons

section DerivedTensorProof

attribute [local instance] supportedHasSheafify supportedHasWeakSheafify

end DerivedTensorProof

end AlgebraicGeometry.Etale
