/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Homology.AcyclicTensorTestEquivalence
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat

/-! # Constant-ring realization on a pro-etale slice

Let `U` be an object of the small pro-etale site of `X` and `B` a commutative ring. Sheaves of
`B`-modules on `U.left` are identified with sheaves of modules over the restriction to the
slice `Over U` of the constant ring sheaf `B`: transport along the slice equivalence
`Over U ≌ U.left.ProEt`, keep the fixed-scalar module presheaf and sheafify it along the
constant-scalar unit. This realization is an additive equivalence compatible with the
sheafified tensor products, and it recovers slice restriction of modules from the fixed-scalar
chart coordinates `finiteCoefficientSliceRestriction`.

Source: Stacks Project, Tags 00YV, 03CY, 03EK and 0GMW
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w v' u' u t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

/-- Sheafifying fixed-scalar module presheaves along a locally bijective constant-scalar unit
is an equivalence onto sheaves of modules.
Source: Stacks Project, Tag 00YV (auxiliary; not a blueprint node).

Proof: the fixed-scalar module presheaf functor is fully faithful, and the sheafification
unit is invertible on sheaves; restriction of scalars along the unit gives essential
surjectivity, with the sheafification counit as comparison. -/
theorem finiteCoefficientModulePresheaf_sheafification_isEquivalence
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (Λ : Type (u + 1)) [Ring Λ] (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    (sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
      finiteCoefficientModulePresheaf C Λ ⋙
      PresheafOfModules.sheafification.{u + 1} α).IsEquivalence := by
  let ff : (finiteCoefficientModulePresheaf C Λ).FullyFaithful :=
    { preimage φ :=
        { app := φ.app
          naturality _ _ f := by
            ext x
            exact ConcreteCategory.congr_hom (φ.naturality f) x }
      map_preimage φ := by
        ext U x
        rfl
      preimage_map φ := by
        ext U x
        rfl }
  have : (finiteCoefficientModulePresheaf C Λ).Full := ff.full
  have : (finiteCoefficientModulePresheaf C Λ).Faithful := ff.faithful
  let E := sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
    finiteCoefficientModulePresheaf C Λ
  let S := PresheafOfModules.sheafification.{u + 1} α
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α
  have hunit (F : Sheaf J (ModuleCat.{u + 1} Λ)) :
      IsIso ((PresheafOfModules.sheafificationAdjunction α).unit.app (E.obj F)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose J
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F).property
  let η : E ⟶ (E ⋙ S) ⋙ G :=
    Functor.whiskerLeft E (PresheafOfModules.sheafificationAdjunction α).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hunit
  have : (E ⋙ S).Faithful := Functor.Faithful.of_comp_iso (asIso η).symm
  have : (E ⋙ S).Full := Functor.Full.of_comp_faithful_iso (asIso η).symm
  have : (E ⋙ S).EssSurj := by
    refine ⟨fun M ↦ ?_⟩
    let P := (PresheafOfModules.restrictScalars α).obj M.val
    let F : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
      { obj := P.obj
        map f := P.map f
        map_id U := by
          ext x
          exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by
          ext x
          exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    let F' : Sheaf J (ModuleCat.{u + 1} Λ) :=
      ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M.isSheaf⟩
    exact ⟨F', ⟨asIso ((PresheafOfModules.sheafificationAdjunction α).counit.app M)⟩⟩
  exact Functor.IsEquivalence.mk (F := E ⋙ S)

/-- Sheafifying fixed-scalar module presheaves inverts the sheafification unit of a
presheaf of modules.
Source: Stacks Project, Tags 00YV and 03CY (auxiliary; not a blueprint node).

Proof: the underlying morphism of abelian presheaves is the whiskered sheafification unit,
which is inverted by abelian sheafification since forgetting the module structure preserves
sheafification. -/
theorem isIso_sheafification_map_toSheafify
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (Λ : Type (u + 1)) [CommRing Λ] (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [HasSheafify J AddCommGrpCat.{u + 1}] [HasSheafify J (ModuleCat.{u + 1} Λ)]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (P : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    IsIso ((PresheafOfModules.sheafification.{u + 1} α).map
      ((finiteCoefficientModulePresheaf C Λ).map (toSheafify J P))) := by
  rw [← MorphismProperty.isomorphisms.iff]
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification.{u + 1} α)) _
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  change J.W (Functor.whiskerRight (toSheafify J P)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
  let : J.PreservesSheafification (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction _ (ModuleCat.forget₂CoinduceAdj Λ)
  exact J.W_of_preservesSheafification _ _ (J.W_toSheafify P)

end AlgebraicGeometry.ProEtale

namespace SheafOfModules

/-- Restriction of a sheaf of modules to constant scalars along a map from the constant ring
presheaf: the same section groups, with the induced action of the constant ring.
Source: Stacks Project, Tag 03CY (auxiliary; not a blueprint node). -/
def constantRingRestriction {C : Type u'} [Category.{v'} C]
    (J : GrothendieckTopology C) (Λ : Type w) [Ring Λ] {R : Sheaf J RingCat.{w}}
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj) :
    SheafOfModules.{w} R ⥤ Sheaf J (ModuleCat.{w} Λ) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars α).obj M.val
    let F : Cᵒᵖ ⥤ ModuleCat.{w} Λ :=
      { obj := P.obj
        map f := P.map f
        map_id U := by
          ext x
          exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by
          ext x
          exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) M.isSheaf⟩
  map φ := ⟨{
    app U := ((PresheafOfModules.restrictScalars α).map φ.val).app U
    naturality _ _ f := by
      ext x
      exact ConcreteCategory.congr_hom (φ.val.naturality f) x }⟩
  map_id M := by
    ext U x
    rfl
  map_comp φ ψ := by
    ext U x
    rfl

end SheafOfModules

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{t}) (B : Type t) [CommRing B] (U : X.ProEt)

/-- The slice equivalence `Over U ⥤ U.left.ProEt` is a dense subsite.
Source: Stacks Project, Tag 098K (auxiliary; not a blueprint node). -/
instance ProEt.sliceTo_isDenseSubsite :
    (ProEt.sliceTo X U).IsDenseSubsite ((ProEt.topology X).over U) (ProEt.topology U.left) := by
  have := ProEt.sliceDense X U
  exact inferInstanceAs ((ProEt.sliceEquiv X U).functor.IsDenseSubsite _ _)

/-- The constant-scalar unit of the constant ring sheaf, restricted to the slice at `U`.
Source: Stacks Project, Tag 00YV (auxiliary; not a blueprint node). -/
def proEtaleSliceScalarMap :
    (Functor.const (Over U)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} B)) ⟶
      ((sheafCompose ((ProEt.topology X).over U)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj
          ((adicConstantRing X B).over U)).obj :=
  Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit X B)

instance : Presheaf.IsLocallyInjective ((ProEt.topology X).over U)
    (proEtaleSliceScalarMap X B U) := by
  have : Presheaf.IsLocallyInjective (ProEt.topology X) (proEtaleModuleScalarUnit X B) :=
    (proEtaleConstantRingUnit_locallyBijective X B).1
  exact Presheaf.isLocallyInjective_whisker ((ProEt.topology X).over U) (ProEt.topology X)
    (Over.forget U) (proEtaleModuleScalarUnit X B)

instance : Presheaf.IsLocallySurjective ((ProEt.topology X).over U)
    (proEtaleSliceScalarMap X B U) := by
  have : Presheaf.IsLocallySurjective (ProEt.topology X) (proEtaleModuleScalarUnit X B) :=
    (proEtaleConstantRingUnit_locallyBijective X B).2
  exact Presheaf.isLocallySurjective_whisker ((ProEt.topology X).over U) (ProEt.topology X)
    (Over.forget U) (proEtaleModuleScalarUnit X B)

/-- Realize a sheaf of `B`-modules on `U.left` as a sheaf of modules over the constant ring
sheaf on the slice at `U`: transport along the slice equivalence, then sheafify the
fixed-scalar module presheaf along the constant-scalar unit.
Source: Stacks Project, Tags 00YV and 03CY (auxiliary; not a blueprint node). -/
def proEtaleSliceRealization :
    Sheaf (ProEt.topology U.left) (ModuleCat.{t + 1} (ULift.{t + 1} B)) ⥤
      SheafOfModules.{t + 1} ((sheafCompose ((ProEt.topology X).over U)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj ((adicConstantRing X B).over U)) :=
  (ProEt.sliceTo X U).sheafPushforwardContinuous _ ((ProEt.topology X).over U)
      (ProEt.topology U.left) ⋙
    sheafToPresheaf _ _ ⋙ ProEtale.finiteCoefficientModulePresheaf (Over U) (ULift.{t + 1} B) ⋙
      PresheafOfModules.sheafification (proEtaleSliceScalarMap X B U)

instance : (proEtaleSliceRealization X B U).IsEquivalence := by
  have := ProEtale.finiteCoefficientModulePresheaf_sheafification_isEquivalence
    ((ProEt.topology X).over U) (ULift.{t + 1} B) _ (proEtaleSliceScalarMap X B U)
  have (Y : (U.left.ProEt)ᵒᵖ) : HasLimitsOfShape (StructuredArrow Y (ProEt.sliceTo X U).op)
      (ModuleCat.{t + 1} (ULift.{t + 1} B)) := hasLimitsOfShape_of_essentiallySmall.{t + 1} _ _
  exact inferInstanceAs (Functor.IsEquivalence (_ ⋙ _))

-- The tensor product of module presheaves over the constant ring presheaf.
private instance constModuleMonoidal (C : Type*) [Category C] (Λ : Type (t + 1))
    [CommRing Λ] :
    MonoidalCategory (PresheafOfModules.{t + 1}
      ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{t + 1}
    (((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ)) ⋙
      forget₂ CommRingCat RingCat)))

/-- The slice realization commutes with the sheafified tensor products.
Source: Stacks Project, Tags 03EK and 0GMW (auxiliary; not a blueprint node).

Proof: the tensor product of sheaves is the sheafification of the sectionwise tensor
product. Transport along the slice equivalence commutes with sheafification and with
sectionwise tensors, and so does the fixed-scalar module presheaf functor. Sheafification
along the constant-scalar unit inverts the sheafification unit and identifies the
sheafified sectionwise tensor product with the tensor product of the associated sheaves of
modules (Tag 0GMW). -/
theorem proEtaleSliceRealization_tensor :
    letI := SheafOfModules.monoidalCategory ((adicConstantRing X B).over U)
    Nonempty (tensor _ ⋙ proEtaleSliceRealization X B U ≅
      (proEtaleSliceRealization X B U).prod (proEtaleSliceRealization X B U) ⋙ tensor _) := by
  let J := ProEt.topology U.left
  let K := (ProEt.topology X).over U
  let A := ModuleCat.{t + 1} (ULift.{t + 1} B)
  let G := ProEt.sliceTo X U
  let E := ProEtale.finiteCoefficientModulePresheaf (Over U) (ULift.{t + 1} B)
  let α := proEtaleSliceScalarMap X B U
  let S := PresheafOfModules.sheafification.{t + 1} α
  let F := proEtaleSliceRealization X B U
  let Us := sheafToPresheaf J A
  let L := presheafToSheaf J A
  let L' := presheafToSheaf K A
  let Wh := (Functor.whiskeringLeft _ _ A).obj G.op
  let := SheafOfModules.monoidalCategory ((adicConstantRing X B).over U)
  have (Y : (U.left.ProEt)ᵒᵖ) : HasLimitsOfShape (StructuredArrow Y G.op) A :=
    hasLimitsOfShape_of_essentiallySmall.{t + 1} _ _
  let h₀ : L ⋙ G.sheafPushforwardContinuous A K J ≅ Wh ⋙ L' :=
    (G.pushforwardContinuousSheafificationCompatibility A K J).symm
  let τ : E ⋙ S ⟶ L' ⋙ sheafToPresheaf K A ⋙ E ⋙ S :=
    Functor.whiskerRight (sheafificationAdjunction K A).unit (E ⋙ S)
  have : IsIso τ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro P
    exact ProEtale.isIso_sheafification_map_toSheafify K (ULift.{t + 1} B) _ α P
  let h : L ⋙ F ≅ Wh ⋙ E ⋙ S :=
    Functor.isoWhiskerRight h₀ (sheafToPresheaf K A ⋙ E ⋙ S) ≪≫
      Functor.isoWhiskerLeft Wh (asIso τ).symm
  let c := asIso (sheafificationAdjunction J A).counit
  let e : Us.prod Us ⋙ tensor _ ⋙ L ≅ tensor _ :=
    Functor.isoWhiskerLeft (Us.prod Us) (Functor.Monoidal.μNatIso L).symm ≪≫
      Functor.isoWhiskerRight (NatIso.prod c c) (tensor _)
  let tW : tensor _ ⋙ Wh ≅ Wh.prod Wh ⋙ tensor _ := Iso.refl _
  let eE : tensor _ ⋙ E ≅ E.prod E ⋙ tensor _ := Iso.refl _
  obtain ⟨eS, _⟩ := PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
    (J := K) (R := (adicConstantRing X B).over U)
    (O := (Functor.const (Over U)ᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} B))) α
  exact ⟨(Functor.isoWhiskerRight e F).symm ≪≫
    Functor.isoWhiskerLeft (Us.prod Us ⋙ tensor _) h ≪≫
    Functor.isoWhiskerLeft (Us.prod Us) (Functor.isoWhiskerRight tW (E ⋙ S)) ≪≫
    Functor.isoWhiskerLeft ((Us ⋙ Wh).prod (Us ⋙ Wh)) (Functor.isoWhiskerRight eE S) ≪≫
    Functor.isoWhiskerLeft ((Us ⋙ Wh ⋙ E).prod (Us ⋙ Wh ⋙ E)) eS.symm⟩

variable (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}) (φ : adicConstantRing X B ⟶ R)
  (V : X.Etale)

/-- Realizing the fixed-scalar chart coordinates of a module recovers its restriction of
scalars to the constant ring, restricted to the slice at the chart.
Source: Stacks Project, Tags 00YV, 03CY and 099R (auxiliary; not a blueprint node).

Proof: the chart coordinates are the slice equivalence applied to the constant-scalar
restriction of the slice module, with identical sections. Undo the slice equivalence by its
unit and the constant-scalar restriction by the counit of module sheafification, which is
invertible for the locally bijective constant-scalar unit. -/
def finiteCoefficientSliceRestrictionRealizationIso :
    finiteCoefficientSliceRestriction X B R φ V ⋙
        proEtaleSliceRealization X B ((toProEt X).obj V) ≅
      SheafOfModules.restrictScalars.{t + 1} ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ) ⋙
        SheafOfModules.overFunctor.{t + 1} (adicModuleRing X B) ((toProEt X).obj V) := by
  let U := (toProEt X).obj V
  let K := (ProEt.topology X).over U
  let A := ModuleCat.{t + 1} (ULift.{t + 1} B)
  have := ProEt.sliceDense X U
  let e := (ProEt.sliceEquiv X U).sheafCongr K (ProEt.topology U.left) A
  let rs := SheafOfModules.restrictScalars.{t + 1} ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)
  let ov := SheafOfModules.overFunctor.{t + 1} (adicModuleRing X B) U
  let α := proEtaleSliceScalarMap X B U
  let G := SheafOfModules.constantRingRestriction K (ULift.{t + 1} B) α
  let Q := sheafToPresheaf K A ⋙ ProEtale.finiteCoefficientModulePresheaf (Over U)
    (ULift.{t + 1} B) ⋙ PresheafOfModules.sheafification α
  let ι : finiteCoefficientSliceRestriction X B R φ V ≅ rs ⋙ ov ⋙ G ⋙ e.functor :=
    NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _)))
  let c : G ⋙ Q ≅ 𝟭 _ := NatIso.ofComponents
    (fun M ↦ (asIso (PresheafOfModules.sheafificationAdjunction α).counit).app M)
    (fun f ↦ (PresheafOfModules.sheafificationAdjunction α).counit.naturality f)
  exact Functor.isoWhiskerRight ι _ ≪≫
    Functor.isoWhiskerLeft (rs ⋙ ov ⋙ G)
      (Functor.isoWhiskerRight e.unitIso.symm Q ≪≫ Functor.leftUnitor Q) ≪≫
    Functor.isoWhiskerLeft (rs ⋙ ov) c ≪≫ Functor.rightUnitor _


/-- Countable colimits of pro-etale sheaves of modules, which define total tensor complexes. -/
instance ProEt.sheafModuleHasCountableColimits (T : Scheme.{t}) :
    HasColimitsOfSize.{0, 0} (Sheaf (ProEt.topology T) (ModuleCat.{t + 1} (ULift.{t + 1} B))) := by
  let : IsGrothendieckAbelian.{t + 1}
      (Sheaf (ProEt.topology T) (ModuleCat.{t + 1} (ULift.{t + 1} B))) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology _ T
  let : HasColimitsOfSize.{t + 1, t + 1}
      (Sheaf (ProEt.topology T) (ModuleCat.{t + 1} (ULift.{t + 1} B))) :=
    IsGrothendieckAbelian.hasColimits _
  exact hasColimitsOfSizeShrink.{0, 0, t + 1, t + 1} _

/-- Total tensor complexes of complexes of pro-etale sheaves of modules exist. -/
instance ProEt.sheafModuleHasMapBifunctorTensor (T : Scheme.{t})
    (P Q : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{t + 1} (ULift.{t + 1} B))) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor _) (.up ℤ) :=
  fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _ (ProEt.sheafModuleHasCountableColimits B T) _ _) _

/-- On pro-etale sheaves of `B`-modules, the acyclic tensor test implies K-flatness for the
class of quasi-isomorphisms.
Source: Stacks Project, Tag 06YN (auxiliary; not a blueprint node). -/
theorem ProEt.sheafModule_kFlat_of_acyclicTensorTest (T : Scheme.{t})
    (P : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{t + 1} (ULift.{t + 1} B))) ℤ)
    (hP : ∀ Z : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{t + 1} (ULift.{t + 1} B))) ℤ,
      Z.Acyclic → (CochainComplex.mapBifunctor Z P (curriedTensor _)).Acyclic) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P :=
  CochainComplex.kFlat_of_acyclicTensorTest P hP

/-- The fixed-scalar chart coordinates of a complex which is K-flat over the constant ring pass
the acyclic tensor test for K-flatness on the chart.
Source: Stacks Project, Cohomology on Sites, Tags 06YN and 0E8K
(auxiliary; not a blueprint node).

Proof: restriction to the slice preserves K-flatness of complexes of modules
(`SheafOfModules.ringedSite_restriction_exact_kflat`, Tag 0E8K). The slice realization is an
additive equivalence compatible with tensor products, so it preserves and reflects the
acyclic tensor test, and it carries the chart coordinates to the restricted complex. -/
theorem finiteCoefficientSliceRestriction_acyclicTensorTest
    (K : CochainComplex (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) ℤ)
    (hK : CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X B)
      ((Functor.mapHomologicalComplex (SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ))
          (.up ℤ)).obj K))
    (P : CochainComplex (Sheaf (ProEt.topology V.left) (ModuleCat.{t + 1} (ULift.{t + 1} B))) ℤ)
    (eP : P ≅ ((finiteCoefficientSliceRestriction X B R φ V).mapHomologicalComplex (.up ℤ)).obj K) :
    ∀ Z : CochainComplex (Sheaf (ProEt.topology V.left) (ModuleCat.{t + 1} (ULift.{t + 1} B))) ℤ,
      Z.Acyclic → (CochainComplex.mapBifunctor Z P (curriedTensor _)).Acyclic := by
  let U := (toProEt X).obj V
  let J := ProEt.topology X
  let R₀ := adicConstantRing X B
  let A := (sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R₀
  let rs := SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)
  let r := SheafOfModules.localizedSystemRestriction.{t + 1, t, 0} R₀ U
  let K₁ := (rs.mapHomologicalComplex (.up ℤ)).obj K
  have h₁ : CochainComplex.IsKFlatIndependentCoefficients (R := R₀.over U)
      ((r.mapHomologicalComplex (.up ℤ)).obj K₁) :=
    (SheafOfModules.ringedSite_restriction_exact_kflat.{t + 1, t, 0} J R₀ U).2.2 K₁ hK
  let H := proEtaleSliceRealization X B U
  have : H.Additive := Functor.additive_of_preserves_binary_products _
  have : rs.Additive := { map_add := rfl }
  have : r.Additive := { map_add := rfl }
  let eH : (H.mapHomologicalComplex (.up ℤ)).obj P ≅ (r.mapHomologicalComplex (.up ℤ)).obj K₁ :=
    (H.mapHomologicalComplex (.up ℤ)).mapIso eP ≪≫
    (Functor.mapHomologicalComplexCompIso
        (finiteCoefficientSliceRestrictionRealizationIso X B R φ V) (.up ℤ)).app K ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (rs ⋙ r)) (.up ℤ)).app K).symm
  let : MonoidalCategory (SheafOfModules.{t + 1} (A.over U)) :=
    SheafOfModules.monoidalCategory (R₀.over U)
  let : (curriedTensor (SheafOfModules.{t + 1} (A.over U))).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients (R₀.over U)
  let : ∀ M : SheafOfModules.{t + 1} (A.over U),
      ((curriedTensor (SheafOfModules.{t + 1} (A.over U))).obj M).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients (R₀.over U)
  obtain ⟨e⟩ := proEtaleSliceRealization_tensor X B U
  exact (CochainComplex.acyclicTensorTest_mapHomologicalComplex_iff H e P).1
    (CochainComplex.acyclicTensorTest_of_iso eH.symm h₁)

end AlgebraicGeometry.Scheme
