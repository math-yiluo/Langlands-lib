/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicImmersionModuleNormalization
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import all WeilConjectures.AlgebraicGeometry.AdicPerfectModelCompleteReduction
import all WeilConjectures.AlgebraicGeometry.CompletedPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.ConstantPullbackScalar
import all WeilConjectures.AlgebraicGeometry.SfbCompletionNormalization
import all WeilConjectures.AlgebraicGeometry.SfbPerfectModelComplexComparison
import WeilConjectures.CategoryTheory.ConstantInverseImageScalarNormalization
import WeilConjectures.CategoryTheory.ScalarInverseImageIndependent
import all WeilConjectures.SixFunctors.GeometricInverseImageConstantModule

/-! # Completed constant modules under the normalized immersion pullback

Source: Stacks Tags 03D2, 03EL and 099L; Bhatt--Scholze Lemma 6.5.8.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

/-- The module functor used termwise in sfbCompletedModel.
Source: Stacks Tags 093J and 099L
(auxiliary; not a blueprint node). -/
def sfbImmersionActualConstants (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :=
  adicLisseConstantModules X A ⋙ completedAdicChange X (CompletedConstantReduction.base X I)

/-- The module functor used termwise in adicResidueConstantPerfect.
Source: Stacks Tags 093J and 099L
(auxiliary; not a blueprint node). -/
def sfbImmersionModelConstants (S : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :=
  SheafOfModules.strictPerfectConstantSheaf (proEtaleModelTopology S) A ⋙
    SheafOfModules.restrictScalars
      (constantModuleHomRingIso (proEtaleModelTopology S) A).inv ⋙
    ConstantCompletion.change (ConstantCompletion.coefficientMap (proEtaleModelTopology S) A I)

/-- Additivity of the specified ordinary module functor.
Source: Stacks Tags 03D2 and 099L
(auxiliary; not a blueprint node). -/
instance sfbImmersionActualConstants_additive (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    (sfbImmersionActualConstants X I).Additive := by
  have := CompletedConstantReduction.constant_additive X A
  unfold sfbImmersionActualConstants
  infer_instance

/-- Additivity of the specified ordinary module functor.
Source: Stacks Tags 03D2 and 099L
(auxiliary; not a blueprint node). -/
instance sfbImmersionModelConstants_additive (S : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    (sfbImmersionModelConstants S I).Additive := by
  unfold sfbImmersionModelConstants
  infer_instance

private theorem completion_normalizations_eq (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    sfbModelCompletionIso X I = SfbCompletionNormalization.coefficients X I := by
  apply Iso.ext
  apply limit.hom_ext
  intro n
  change _ ≫ ConstantCompletion.projection _ A I n.unop =
    _ ≫ ConstantCompletion.projection _ A I n.unop
  rw [sfbModelCompletionIso_projection, SfbCompletionNormalization.projection]
  rfl

private def normalized_constants (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    sfbImmersionActualConstants X I ⋙ sfbImmersionNormalizeModules X I ≅
      commutativeSiteConstantModuleFunctor (proEtaleModelTopology X) A ⋙
        ConstantCompletion.change
          (ConstantCompletion.coefficientMap (proEtaleModelTopology X) A I) := by
  let e := SfbCompletionNormalization.coefficients X I
  let c := commutativeSiteConstantModuleFunctor (proEtaleModelTopology X) A ⋙
    ConstantCompletion.change
      (ConstantCompletion.coefficientMap (proEtaleModelTopology X) A I)
  have h : ConstantCompletion.res e.hom ⋙ ConstantCompletion.res e.inv ≅ 𝟭 _ :=
    AdicPerfectModel.scalarRestrictionComp e.inv e.hom ≪≫
      eqToIso (congrArg (fun f ↦ ConstantCompletion.res f) e.inv_hom_id) ≪≫
      scalarRestrictionIdIso _
  have t := completedRealizationIso X A I
  rw [completion_normalizations_eq X I] at t
  exact isoWhiskerRight t (ConstantCompletion.res e.inv) ≪≫
    isoWhiskerLeft c h ≪≫ Functor.rightUnitor c

private theorem pull_coefficient_square
    {C D : Type (u + 1)} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1))}
    (F : ConstantCompletion.InverseImageData L)
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    F.rings.map (ConstantCompletion.coefficientMap J A I) ≫
        ConstantCompletion.completedMap F A I =
      ConstantCompletion.constantMap F A ≫ ConstantCompletion.coefficientMap K A I := by
  apply limit.hom_ext
  intro n
  change _ ≫ ConstantCompletion.projection K A I n.unop =
    _ ≫ ConstantCompletion.projection K A I n.unop
  have hp : ConstantCompletion.completedMap F A I ≫
      ConstantCompletion.projection K A I n.unop =
      F.rings.map (ConstantCompletion.projection J A I n.unop) ≫
        F.constants.hom.app (CommRingCat.of (A ⧸ I ^ (n.unop + 1))) := limit.lift_π _ n
  rw [Category.assoc, hp, ← Category.assoc, ← Functor.map_comp]
  have hJ : ConstantCompletion.coefficientMap J A I ≫
      ConstantCompletion.projection J A I n.unop =
      ConstantCompletion.quotient J A I n.unop := limit.lift_π _ n
  have hK : ConstantCompletion.coefficientMap K A I ≫
      ConstantCompletion.projection K A I n.unop =
      ConstantCompletion.quotient K A I n.unop := limit.lift_π _ n
  rw [hJ, Category.assoc, hK]
  exact F.constants.hom.naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n.unop + 1))))

private theorem pull_scalar_square
    {C D : Type (u + 1)} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1))}
    (V : Sheaf K (Type (u + 1)) ⥤ Sheaf J (Type (u + 1))) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (F : ConstantCompletion.InverseImageData L)
    {R B : Sheaf J CommRingCat.{u + 1}} {R' B' : Sheaf K CommRingCat.{u + 1}}
    (φ : R ⟶ B) (ψ : R' ⟶ B') (r : F.rings.obj R ⟶ R')
    (b : F.rings.obj B ⟶ B') (hsq : F.rings.map φ ≫ b = r ≫ ψ) :
    Nonempty (ConstantCompletion.change φ ⋙ ConstantCompletion.pull F b ≅
      ConstantCompletion.pull F r ⋙ ConstantCompletion.change ψ) := by
  obtain ⟨e, _⟩ := SheafOfModules.ScalarIndependent.exists_scalarInverseImageIndependent
    L V adj (F.algebra R) (F.algebra B) φ (F.rings.map φ)
    (F.ring_naturality φ) (ConstantCompletion.change φ)
    (ConstantCompletion.change (F.rings.map φ))
    (AdicPerfectModel.scalarAdjunction φ)
    (AdicPerfectModel.scalarAdjunction (F.rings.map φ))
  exact ⟨isoWhiskerRight e (ConstantCompletion.change b) ≪≫
    isoWhiskerLeft (F.algebra R).modules
      (AdicPerfectModel.scalarChangeComp (F.rings.map φ) b ≪≫
        eqToIso (congrArg (fun f ↦ ConstantCompletion.change f) hsq) ≪≫
        (AdicPerfectModel.scalarChangeComp r ψ).symm)⟩

section ConstantModules

variable {C D : Type (u + 1)} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type (u + 1)} [CommRing A]

private def constants_underlying (J : GrothendieckTopology C) :
    commutativeSiteConstantModuleFunctor J A ⋙
        ConstantCompletion.underlying (ConstantCompletion.constant J A) ≅
      CategoryTheory.forget (ModuleCat.{u + 1} A) ⋙ constantSheaf J (Type (u + 1)) :=
  isoWhiskerLeft (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
    (constantCommuteCompose J (CategoryTheory.forget AddCommGrpCat.{u + 1}))

private theorem constants_scalar (J : GrothendieckTopology C)
    (M : ModuleCat.{u + 1} A) (a : A) :
    (commutativeSiteConstantModuleFunctor J A).map (constantScalar A M a) =
      ⟨PresheafOfModules.sectionsSMul
        ((commutativeSiteConstantModuleFunctor J A).obj M).val
        (ConstantCompletion.constantSection (J := J) a)⟩ := by
  have := (realizationRingUnit_locallyBijective J A).1
  have := (realizationRingUnit_locallyBijective J A).2
  apply (SheafOfModules.toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _
    ((SheafOfModules.toSheaf _).obj
      ((commutativeSiteConstantModuleFunctor J A).obj M)).property
  change _ ≫ sheafifyMap J _ = _
  rw [← toSheafify_naturality]
  ext U x
  exact ((PresheafOfModules.toSheafify (realizationRingUnit J A)
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) A).obj M).presheaf)).app
      U).hom.map_smul a x

private def constant_linear_map
    (M N : ConstantCompletion.Mod (ConstantCompletion.constant K A))
    (f : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj N)
    (hf : ∀ (U : Dᵒᵖ) (a : A) (x : M.val.obj U),
      f.hom.app U ((ConstantCompletion.constantSection (J := K) a).val U • x) =
        (ConstantCompletion.constantSection (J := K) a).val U •
          (show N.val.obj U from f.hom.app U x)) : M ⟶ N := by
  have := (realizationRingUnit_locallyBijective K A).2
  let g : (PresheafOfModules.restrictScalars (realizationRingUnit K A)).obj M.val ⟶
      (PresheafOfModules.restrictScalars (realizationRingUnit K A)).obj N.val :=
    PresheafOfModules.homMk f.hom hf
  exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    (realizationRingUnit K A) N.isSheaf).symm g⟩

private def constant_linear_natTrans
    (F G : ModuleCat.{u + 1} A ⥤ ConstantCompletion.Mod (ConstantCompletion.constant K A))
    (hF : ∀ M a, F.map (constantScalar A M a) =
      ⟨PresheafOfModules.sectionsSMul (F.obj M).val
        (ConstantCompletion.constantSection (J := K) a)⟩)
    (hG : ∀ M a, G.map (constantScalar A M a) =
      ⟨PresheafOfModules.sectionsSMul (G.obj M).val
        (ConstantCompletion.constantSection (J := K) a)⟩)
    (f : F ⋙ SheafOfModules.toSheaf _ ⟶ G ⋙ SheafOfModules.toSheaf _) : F ⟶ G where
  app M := constant_linear_map (F.obj M) (G.obj M) (f.app M) (by
    intro U a x
    have h := f.naturality (constantScalar A M a)
    change (SheafOfModules.toSheaf _).map (F.map _) ≫ f.app M =
      f.app M ≫ (SheafOfModules.toSheaf _).map (G.map _) at h
    rw [hF, hG] at h
    exact congrArg (fun k ↦ k.hom.app U x) h)
  naturality := by
    intro M N g
    apply (SheafOfModules.toSheaf _).map_injective
    exact f.naturality g

private def constant_pull_underlying
    {L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1))}
    (F : ConstantCompletion.InverseImageData L) :
    ConstantCompletion.pull F (ConstantCompletion.constantMap F A) ⋙
        ConstantCompletion.underlying (ConstantCompletion.constant K A) ≅
      ConstantCompletion.underlying (ConstantCompletion.constant J A) ⋙ L := by
  let e := F.constants.app (CommRingCat.of A)
  let r : ConstantCompletion.res e.inv ⋙
      ConstantCompletion.underlying (ConstantCompletion.constant K A) ≅
      ConstantCompletion.underlying (F.rings.obj (ConstantCompletion.constant J A)) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  exact isoWhiskerRight
      (isoWhiskerLeft (F.algebra (ConstantCompletion.constant J A)).modules
        (scalarChangeIso e.symm))
      (ConstantCompletion.underlying (ConstantCompletion.constant K A)) ≪≫
    isoWhiskerLeft (F.algebra (ConstantCompletion.constant J A)).modules r ≪≫
    (F.algebra (ConstantCompletion.constant J A)).moduleUnderlying

private def constant_pull_comparison
    {L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1))}
    (V : Sheaf K (Type (u + 1)) ⥤ Sheaf J (Type (u + 1))) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (F : ConstantCompletion.InverseImageData L)
    (hscalar : ∀ a : A, ConstantCompletion.transportedConstantSection F A a =
      ConstantCompletion.constantSection (J := K) a) :
    commutativeSiteConstantModuleFunctor J A ⋙
        ConstantCompletion.pull F (ConstantCompletion.constantMap F A) ≅
      commutativeSiteConstantModuleFunctor K A := by
  have : IsIso (ConstantCompletion.constantMap F A) := by
    change IsIso ((F.constants.app (CommRingCat.of A)).hom)
    infer_instance
  let P := ConstantCompletion.pull F (ConstantCompletion.constantMap F A)
  let H := commutativeSiteConstantModuleFunctor J A ⋙ P
  let G := commutativeSiteConstantModuleFunctor K A
  have : PreservesFiniteLimits P :=
    ConstantCompletion.pull_finiteLimits_of_isIso F (ConstantCompletion.constantMap F A)
  have : PreservesFiniteLimits (commutativeSiteConstantModuleFunctor J A) :=
    (commutativeSiteConstantModuleFunctor_exact J A).2.1
  have : PreservesFiniteLimits G :=
    (commutativeSiteConstantModuleFunctor_exact K A).2.1
  have : PreservesFiniteLimits H := comp_preservesFiniteLimits _ _
  have : PreservesColimitsOfSize.{u + 1, u + 1} L := adj.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (constantSheaf J (Type (u + 1))) := by dsimp [constantSheaf]; infer_instance
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (constantSheaf K (Type (u + 1))) := by dsimp [constantSheaf]; infer_instance
  let hJ := Types.isTerminalPUnit.isTerminalObj (constantSheaf J (Type (u + 1))) _
  let hK := Types.isTerminalPUnit.isTerminalObj (constantSheaf K (Type (u + 1))) _
  let point := (hJ.isTerminalObj L _).uniqueUpToIso hK
  let c := pointComparisonNatIso (constantSheaf J (Type (u + 1)) ⋙ L)
    (constantSheaf K (Type (u + 1))) point
  let s : H ⋙ ConstantCompletion.underlying (ConstantCompletion.constant K A) ≅
      G ⋙ ConstantCompletion.underlying (ConstantCompletion.constant K A) :=
    isoWhiskerLeft (commutativeSiteConstantModuleFunctor J A) (constant_pull_underlying F) ≪≫
      isoWhiskerRight (constants_underlying J) L ≪≫
      isoWhiskerLeft (CategoryTheory.forget (ModuleCat.{u + 1} A)) c ≪≫
      (constants_underlying K).symm
  have hH M a : H.map (constantScalar A M a) =
      ⟨PresheafOfModules.sectionsSMul (H.obj M).val
        (ConstantCompletion.constantSection (J := K) a)⟩ := by
    change P.map ((commutativeSiteConstantModuleFunctor J A).map _) = _
    rw [constants_scalar, ConstantCompletion.constantPullback_scalar, hscalar]
    rfl
  have hG M a : G.map (constantScalar A M a) =
      ⟨PresheafOfModules.sectionsSMul (G.obj M).val
        (ConstantCompletion.constantSection (J := K) a)⟩ := constants_scalar K M a
  have (U : Dᵒᵖ) : PreservesFiniteLimits ((sheafSections K AddCommGrpCat.{u + 1}).obj U) := by
    change PreservesFiniteLimits (sheafToPresheaf K AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation Dᵒᵖ AddCommGrpCat.{u + 1}).obj U)
    infer_instance
  have (U : Dᵒᵖ) : PreservesFiniteLimits
      ((H ⋙ SheafOfModules.toSheaf _) ⋙ (sheafSections K AddCommGrpCat).obj U) :=
    comp_preservesFiniteLimits _ _
  have (U : Dᵒᵖ) : PreservesFiniteLimits
      ((G ⋙ SheafOfModules.toSheaf _) ⋙ (sheafSections K AddCommGrpCat).obj U) :=
    comp_preservesFiniteLimits _ _
  let a := abelianLiftSetNatTrans K A (H ⋙ SheafOfModules.toSheaf _)
    (G ⋙ SheafOfModules.toSheaf _) s.hom
  let b := constant_linear_natTrans H G hH hG a
  have hb : Functor.whiskerRight b
      (ConstantCompletion.underlying (ConstantCompletion.constant K A)) = s.hom := by
    exact abelianLiftSetNatTrans_forget K A (H ⋙ SheafOfModules.toSheaf _)
      (G ⋙ SheafOfModules.toSheaf _) s.hom
  have (M : ModuleCat.{u + 1} A) : IsIso (b.app M) := by
    have : IsIso ((ConstantCompletion.underlying (ConstantCompletion.constant K A)).map
        (b.app M)) := by
      change IsIso ((Functor.whiskerRight b
        (ConstantCompletion.underlying (ConstantCompletion.constant K A))).app M)
      rw [hb]
      infer_instance
    exact isIso_of_reflects_iso _ (ConstantCompletion.underlying (ConstantCompletion.constant K A))
  exact NatIso.ofComponents (fun M ↦ asIso (b.app M)) (by intros; exact b.naturality _)

private theorem transported_scalars
    (G : C ⥤ D) [G.IsContinuous J K]
    (L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1)))
    (adj : L ⊣ G.sheafPushforwardContinuous (Type (u + 1)) J K)
    [PreservesFiniteLimits L] (F : ConstantCompletion.InverseImageData L) (a : A) :
    ConstantCompletion.transportedConstantSection F A a =
      ConstantCompletion.constantSection (J := K) a := by
  let R := ConstantCompletion.constant J A
  let S := ConstantCompletion.constant K A
  let ρ : R ⟶ (G.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj S :=
    ((sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv _ _).symm
      (Functor.whiskerLeft G.op
        (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))))
  have hρ : toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)) ≫ ρ.hom =
      Functor.whiskerLeft G.op
        (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))) :=
    ((sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  let T := Sheaf.terminal J Types.isTerminalPUnit
  let T' := Sheaf.terminal K Types.isTerminalPUnit
  let hT := (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).isTerminalObj L T
  have h : L.map (ConstantCompletion.constantSectionMap A a T) ≫
      (F.algebra R).ringUnderlying.hom ≫
      (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map
        (ConstantCompletion.constantMap F A) =
      ConstantCompletion.constantSectionMap A a (L.obj T) := by
    rw [ConstantCompletion.constantInverseImageScalarNormalization J K G L adj F A]
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    ext U x
    exact congrArg (fun f ↦ f.app U a) hρ
  apply Subtype.ext
  funext U
  exact congrArg (fun f ↦ f.hom.app U ((hT.from T').hom.app U PUnit.unit)) h

end ConstantModules

/-- Constant modules commute with the normalized completed immersion pullback.

Source: Stacks Tags 03D2, 03EL and 099L; Bhatt--Scholze Lemma 6.5.8
(auxiliary; not a blueprint node).

Proof: constant sheafification on the original site and on the AsSmall model
commutes with the site equivalence, naturally in the coefficient module. The
canonical constant-ring comparison identifies the two scalar actions. Geometric
inverse image preserves constant modules, since it preserves finite limits and
is left adjoint; the algebraic inverse-image data identifies their addition and
scalar multiplication on generalized sections. The normalization isomorphism
for the completed rings respects all finite quotient projections. These
projections identify the composite constant-to-completed coefficient map with
the coefficientMap on S. Reassociate the two scalar extensions using the map
s tensor (t tensor m) to st tensor m. Its inverse sends s tensor m to
s tensor (1 tensor m). The balancing relations show that the two maps are
inverse and natural in every A-linear map. Sheafification preserves these
identities. This proves the displayed natural isomorphism of module functors,
without a slice, a complex, or any perfectness or boundedness assumption.
For I=A both target coefficient rings are zero; for I=0 the same maps are
ordinary constant-module transport. -/
theorem sfbImmersion_constantModuleComparison
    {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    Nonempty ((sfbImmersionActualConstants X I ⋙ sfbImmersionNormalizeModules X I) ⋙
      sfbImmersionCompletedPullModules i I ≅ sfbImmersionModelConstants S I) := by
  let G : proEtaleSiteModel X ⥤ proEtaleSiteModel S :=
    coefficientProEtaleModelBaseChange.{u, 0} i
  have : G.IsContinuous (proEtaleModelTopology X) (proEtaleModelTopology S) := by
    dsimp only [G]
    infer_instance
  let adj : SfbAdicRestriction.inverse i ⊣
      G.sheafPushforwardContinuous (Type (u + 1))
        (proEtaleModelTopology X) (proEtaleModelTopology S) :=
    SfbAdicRestriction.adjunction i
  let F := sfbImmersionAlgebra i
  let qX := ConstantCompletion.coefficientMap (proEtaleModelTopology X) A I
  let qS := ConstantCompletion.coefficientMap (proEtaleModelTopology S) A I
  let c := ConstantCompletion.completedMap F A I
  let r := ConstantCompletion.constantMap F A
  let e := constant_pull_comparison (A := A) _ adj F
    (fun a ↦ transported_scalars G _ adj F a)
  obtain ⟨t⟩ := pull_scalar_square _ adj F qX qS r c (pull_coefficient_square F I)
  let eS : commutativeSiteConstantModuleFunctor (proEtaleModelTopology S) A ≅
      SheafOfModules.strictPerfectConstantSheaf (proEtaleModelTopology S) A ⋙
        SheafOfModules.restrictScalars
          (constantModuleHomRingIso (proEtaleModelTopology S) A).inv :=
    (AdicPerfectModel.constantPresentationIso (J := proEtaleModelTopology S) (A := A)).symm
  exact ⟨isoWhiskerRight (normalized_constants X I) (sfbImmersionCompletedPullModules i I) ≪≫
    isoWhiskerLeft (commutativeSiteConstantModuleFunctor (proEtaleModelTopology X) A) t ≪≫
    isoWhiskerRight e (ConstantCompletion.change qS) ≪≫
    isoWhiskerRight eS (ConstantCompletion.change qS)⟩

end AlgebraicGeometry.Scheme
