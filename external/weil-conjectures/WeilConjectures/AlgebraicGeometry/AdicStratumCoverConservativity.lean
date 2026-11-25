/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Sites.LocalProperties
import all WeilConjectures.AlgebraicGeometry.CompletedPullbackAdjunction
import all WeilConjectures.AlgebraicGeometry.NoetherianStratumDetection
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport

/-! # Joint conservativity on stratum covering slices

Source: Bhatt--Scholze, Remark 6.5.10 and Proposition 6.6.11; Stacks Project,
Tags 09AH and 05RU (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

open ConstantCompletion SheafOfModules SheafOfModules.GeometricConstruction in
private theorem pullInsertion_isIso
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)} (F : InverseImageData L)
    {R : Sheaf J CommRingCat.{v}} {S : Sheaf K CommRingCat.{v}}
    (c : F.rings.obj R ⟶ S) [IsIso c] (M : Mod R) :
    IsIso (pullInsertion F c M) := by
  have : (restriction c).IsEquivalence := ConstantCompletion.restrictScalars_equivalence
    ((sheafCompose K (forget₂ CommRingCat RingCat)).mapIso (asIso c))
  have := (tensorAdjunction c).isEquivalence_left_of_isEquivalence_right
  have hq : insertion c ((F.algebra R).modules.obj M) =
      tensorUnit c ((F.algebra R).modules.obj M) := by
    ext U m
    exact ((insertion_existsUnique c _).exists.choose_spec U m).trans
      (tensorUnit_apply c _ U m).symm
  dsimp only [pullInsertion]
  rw [hq]
  dsimp only [tensorUnit]
  infer_instance

private noncomputable def setsTerminal_of_moduleZero
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{v}) (M : ConstantCompletion.Mod R)
    (h : IsZero M) : IsTerminal ((ConstantCompletion.underlying R).obj M) := by
  have : PreservesFiniteLimits (ConstantCompletion.underlying R) :=
    SheafOfModules.moduleUnderlying_finiteLimits R
  exact h.isTerminal.isTerminalObj _ _

private theorem abZero_of_setsTerminal
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (M : Sheaf J AddCommGrpCat.{v})
    (h : IsTerminal
      ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{v})).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{v})).map_injective
  exact h.hom_ext _ _

set_option backward.defeqAttrib.useBackward true in
private noncomputable def modelForgetComparison {X Y : Scheme.{u}} (i : Y ⟶ X) :
    ((modelSheafEquivalence X AddCommGrpCat.{u + 1}).functor ⋙
      proEtaleSheafInverseImage i AddCommGrpCat.{u + 1} ⋙
      (modelSheafEquivalence Y AddCommGrpCat.{u + 1}).inverse) ⋙
        sheafCompose (proEtaleModelTopology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ≅
      sheafCompose (proEtaleModelTopology X) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ⋙
        ((modelSheafEquivalence X (Type (u + 1))).functor ⋙
          proEtaleSheafInverseImage i (Type (u + 1)) ⋙
          (modelSheafEquivalence Y (Type (u + 1))).inverse) := by
  let B := proEtaleModelBaseChange i
  let J := proEtaleModelTopology X
  let K := proEtaleModelTopology Y
  have : (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsEquivalence
  have : (AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).functor.IsEquivalence
  have : PreservesFiniteLimits B := by
    dsimp [B, proEtaleModelBaseChange]
    infer_instance
  have : RepresentablyFlat B := flat_of_preservesFiniteLimits B
  let e := (modelAdjunction i AddCommGrpCat.{u + 1}).leftAdjointUniq
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B
      AddCommGrpCat.{u + 1} J K)
  let e' := (modelAdjunction i (Type (u + 1))).leftAdjointUniq
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B (Type (u + 1)) J K)
  exact Functor.isoWhiskerRight e (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u + 1})) ≪≫
    sheafPullbackForgetIso J K B (CategoryTheory.forget AddCommGrpCat.{u + 1}) ≪≫
    Functor.isoWhiskerLeft (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u + 1})) e'.symm

private theorem coveringModules_detectZero
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (T : C) (hT : IsTerminal T) (V : Sieve T) (hV : V ∈ J T)
    (A : Type v) [CommRing A] (I : Ideal A)
    (G : ∀ U : C, ConstantCompletion.InverseImageData (J.overPullback (Type v) U))
    [∀ U, IsIso (ConstantCompletion.completedMap (G U) A I)]
    (M : ConstantCompletion.Mod (ConstantCompletion.completed J A I))
    (h : ∀ (U : C) (g : U ⟶ T), V g →
      IsZero ((ConstantCompletion.pull (G U)
        (ConstantCompletion.completedMap (G U) A I)).obj M)) : IsZero M := by
  let B := ConstantCompletion.completed J A I
  let ι := Σ U : C, {g : U ⟶ T // V g}
  let Y : ι → C := fun i ↦ i.1
  have hY : J.CoversTop Y := by
    apply (J.coversTop_iff_of_isTerminal T hT Y).mpr
    apply J.superset_covering _ hV
    intro U g hg
    exact ⟨⟨U, g, hg⟩, ⟨𝟙 U⟩⟩
  let := HasZeroObject.zero' (ConstantCompletion.Mod B)
  let f : M ⟶ 0 := 0
  have hf : IsIso ((ConstantCompletion.underlying B).map f) := by
    apply Sheaf.isIso_of_coversTop hY
    intro i
    let U := i.1
    let L := J.overPullback (Type v) U
    let B' := ConstantCompletion.completed (J.over U) A I
    have ht := setsTerminal_of_moduleZero (J.over U) B'
      ((ConstantCompletion.pull (G U) (ConstantCompletion.completedMap (G U) A I)).obj M)
      (h U i.2.1 i.2.2)
    have : IsIso (ConstantCompletion.pullInsertion (G U)
        (ConstantCompletion.completedMap (G U) A I) M) := pullInsertion_isIso _ _ _
    have hs : IsTerminal (L.obj ((ConstantCompletion.underlying B).obj M)) :=
      ht.ofIso (asIso (ConstantCompletion.pullInsertion (G U)
        (ConstantCompletion.completedMap (G U) A I) M)).symm
    have ht' := (setsTerminal_of_moduleZero J B 0 (isZero_zero _)).isTerminalObj L _
    exact isIso_of_isTerminal hs ht' _
  have : IsIso f := isIso_of_reflects_iso f (ConstantCompletion.underlying B)
  exact (isZero_zero _).of_iso (asIso f)

private theorem pull_exact
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
    (F : ConstantCompletion.InverseImageData L)
    (V : Sheaf K (Type v) ⥤ Sheaf J (Type v)) (adj : L ⊣ V)
    [PreservesFiniteLimits L]
    {R : Sheaf J CommRingCat.{v}} {S : Sheaf K CommRingCat.{v}}
    (c : F.rings.obj R ⟶ S) [IsIso c] :
    PreservesFiniteLimits (ConstantCompletion.pull F c) ∧
      PreservesFiniteColimits (ConstantCompletion.pull F c) := by
  refine ⟨ConstantCompletion.pull_finiteLimits_of_isIso F c, ?_⟩
  obtain ⟨G, _, aM, _⟩ := ConstantCompletion.module_adjunction_exists V adj F c
  have := aM.leftAdjoint_preservesColimits
  infer_instance

private noncomputable def pullDerivedIso
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
    (F : ConstantCompletion.InverseImageData L)
    (V : Sheaf K (Type v) ⥤ Sheaf J (Type v)) (adj : L ⊣ V)
    [PreservesFiniteLimits L]
    {R : Sheaf J CommRingCat.{v}} {S : Sheaf K CommRingCat.{v}}
    (c : F.rings.obj R ⟶ S) [IsIso c] :
    letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
    letI := HasDerivedCategory.standard (ConstantCompletion.Mod S)
    letI := (pull_exact F V adj c).1
    letI := (pull_exact F V adj c).2
    (ConstantCompletion.derivedPull F V adj c).functor ≅
      (ConstantCompletion.pull F c).mapDerivedCategory := by
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod S)
  have := (pull_exact F V adj c).1
  have := (pull_exact F V adj c).2
  let d := ConstantCompletion.derivedPull F V adj c
  let P := ConstantCompletion.pull F c
  let W := HomologicalComplex.quasiIso (ConstantCompletion.Mod R) (.up ℤ)
  have : d.functor.IsLeftDerivedFunctor d.comparison W := d.universal
  have : P.mapDerivedCategory.IsLeftDerivedFunctor P.mapDerivedCategoryFactors.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ P.mapDerivedCategoryFactors
  exact Functor.leftDerivedUnique P.mapDerivedCategory d.functor d.comparison
    P.mapDerivedCategoryFactors.hom W

private theorem strataModules_detectZero
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] (I : Ideal A)
    (s : FiniteLocallyClosedStratification X)
    (L : ∀ α : Fin s.n, Sheaf (proEtaleModelTopology X) (Type (u + 1)) ⥤
      Sheaf (proEtaleModelTopology (s.domain α)) (Type (u + 1)))
    (hL : ∀ α, Nonempty (L α ≅
      (modelSheafEquivalence X (Type (u + 1))).functor ⋙
        proEtaleSheafInverseImage (s.immersion α) (Type (u + 1)) ⋙
        (modelSheafEquivalence (s.domain α) (Type (u + 1))).inverse))
    (F : ∀ α, ConstantCompletion.InverseImageData (L α))
    [∀ α, IsIso (ConstantCompletion.completedMap (F α) A I)]
    (M : ConstantCompletion.Mod
      (ConstantCompletion.completed (proEtaleModelTopology X) A I))
    (h : ∀ α, IsZero ((ConstantCompletion.pull (F α)
      (ConstantCompletion.completedMap (F α) A I)).obj M)) : IsZero M := by
  let B := ConstantCompletion.completed (proEtaleModelTopology X) A I
  let R := (sheafCompose (proEtaleModelTopology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  let MAb := (SheafOfModules.toSheaf R).obj M
  let E := modelSheafEquivalence X AddCommGrpCat.{u + 1}
  let N := E.functor.obj MAb
  have hstr (α : Fin s.n) : IsZero
      ((proEtaleSheafInverseImage (s.immersion α) AddCommGrpCat.{u + 1}).obj N) := by
    let B' := ConstantCompletion.completed (proEtaleModelTopology (s.domain α)) A I
    have ht := setsTerminal_of_moduleZero _ B' _ (h α)
    have : IsIso (ConstantCompletion.pullInsertion (F α)
      (ConstantCompletion.completedMap (F α) A I) M) := pullInsertion_isIso _ _ _
    have htL := ht.ofIso (asIso (ConstantCompletion.pullInsertion (F α)
      (ConstantCompletion.completedMap (F α) A I) M)).symm
    let e := (hL α).some
    have htS := htL.ofIso (e.app ((ConstantCompletion.underlying B).obj M))
    let H := ((modelSheafEquivalence X AddCommGrpCat.{u + 1}).functor ⋙
      proEtaleSheafInverseImage (s.immersion α) AddCommGrpCat.{u + 1} ⋙
      (modelSheafEquivalence (s.domain α) AddCommGrpCat.{u + 1}).inverse).obj MAb
    have hzH : IsZero H := abZero_of_setsTerminal _ H
      (htS.ofIso ((modelForgetComparison (s.immersion α)).app MAb).symm)
    have hz := ((modelSheafEquivalence (s.domain α) AddCommGrpCat.{u + 1}).functor
      ).map_isZero hzH
    exact hz
  have : ∀ α, IsImmersion (s.immersion α) := s.isImmersion
  have : ∀ α, TopologicalSpace.NoetherianSpace (s.domain α) := fun α ↦
    (s.immersion α).isEmbedding.noetherianSpace
  have : ∀ α, QuasiCompact (s.immersion α) := fun α ↦ inferInstance
  have hzN : IsZero N := by
    rw [IsZero.iff_id_eq_zero]
    apply AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp
      s.immersion
    · intro x
      obtain ⟨α, hα⟩ := Set.mem_iUnion.mp (s.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
      exact ⟨α, (s.range_immersion α).symm ▸ hα⟩
    · intro α
      rw [(AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
        (s.immersion α)).map_id]
      exact (hstr α).eq_of_src _ _
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.toSheaf R).map_injective
  apply E.functor.map_injective
  exact hzN.eq_of_src _ _

/-- Exact algebraic inverse images followed by covering slice restrictions jointly
reflect isomorphisms in the unbounded derived category.

Source: Bhatt--Scholze, Remark 6.5.10 and Proposition 6.6.11; Stacks Project,
Tags 09AH and 05RU.
(auxiliary; not a blueprint node).

Proof: transport the small models to the original pro-etale sites. Forgetting a module
to its abelian sheaf is faithful and exact. The supplied underlying-set comparisons and
operation identities identify the algebraic module inverse image with geometric inverse
image followed by scalar extension. Since the coefficient maps are isomorphisms, scalar
extension is an equivalence. Thus vanishing after these module functors is exactly
vanishing of the geometric inverse-image abelian sheaf. A covering sieve gives a jointly
covering family of its arrows; the sheaf separation axiom detects vanishing on that
family. Apply Noetherian finite-stratum detection to the cohomology sheaves in each
integer degree. Exactness of inverse image identifies their pullbacks with cohomology
of the given derived pullbacks. The latter are computed termwise because the coefficient
maps are isomorphisms. This proves joint detection of zero derived objects. Complete
the given morphism to a distinguished triangle. Its image cones vanish since all image
morphisms are isomorphisms; zero detection makes its original cone zero, and the
triangle criterion gives invertibility. The empty scheme and empty covering families
are included by the empty-cover sheaf axiom, with no boundedness assumption.
-/
theorem adicStratumCoverConservativity
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] (I : Ideal A)
    (s : FiniteLocallyClosedStratification X)
    (V : ∀ α : Fin s.n,
      Sieve ((AsSmall.up : (s.domain α).ProEt ⥤ proEtaleSiteModel (s.domain α)).obj
        (⊤_ (s.domain α).ProEt)))
    (hV : ∀ α : Fin s.n, V α ∈ proEtaleModelTopology (s.domain α)
      ((AsSmall.up : (s.domain α).ProEt ⥤ proEtaleSiteModel (s.domain α)).obj
        (⊤_ (s.domain α).ProEt)))
    (L : ∀ α : Fin s.n,
      Sheaf (proEtaleModelTopology X) (Type (u + 1)) ⥤
        Sheaf (proEtaleModelTopology (s.domain α)) (Type (u + 1)))
    (R : ∀ α : Fin s.n,
      Sheaf (proEtaleModelTopology (s.domain α)) (Type (u + 1)) ⥤
        Sheaf (proEtaleModelTopology X) (Type (u + 1)))
    (adj : ∀ α, L α ⊣ R α)
    [∀ α, PreservesFiniteLimits (L α)]
    (hL : ∀ α, Nonempty (L α ≅
      (AsSmall.up.sheafPushforwardContinuous (Type (u + 1))
        (ProEt.topology X) (proEtaleModelTopology X)) ⋙
      proEtaleSheafInverseImage (s.immersion α) (Type (u + 1)) ⋙
      (AsSmall.down.sheafPushforwardContinuous (Type (u + 1))
        (proEtaleModelTopology (s.domain α)) (ProEt.topology (s.domain α)))))
    (F : ∀ α, ConstantCompletion.InverseImageData (L α))
    [∀ α, IsIso (ConstantCompletion.completedMap (F α) A I)]
    (G : ∀ (α : Fin s.n) (U : proEtaleSiteModel (s.domain α)),
      ConstantCompletion.InverseImageData
        ((proEtaleModelTopology (s.domain α)).overPullback (Type (u + 1)) U))
    (W : ∀ (α : Fin s.n) (U : proEtaleSiteModel (s.domain α)),
      Sheaf ((proEtaleModelTopology (s.domain α)).over U) (Type (u + 1)) ⥤
        Sheaf (proEtaleModelTopology (s.domain α)) (Type (u + 1)))
    (adjW : ∀ α U,
      (proEtaleModelTopology (s.domain α)).overPullback (Type (u + 1)) U ⊣ W α U)
    [∀ α U, IsIso (ConstantCompletion.completedMap (G α U) A I)] :
    ∀ (M N : ConstantCompletion.D
        (ConstantCompletion.completed (proEtaleModelTopology X) A I)) (f : M ⟶ N),
      (∀ (α : Fin s.n) (U : proEtaleSiteModel (s.domain α))
        (g : U ⟶ (AsSmall.up : (s.domain α).ProEt ⥤
          proEtaleSiteModel (s.domain α)).obj (⊤_ (s.domain α).ProEt)), V α g →
        IsIso (((ConstantCompletion.derivedPull (F α) (R α) (adj α)
            (ConstantCompletion.completedMap (F α) A I)).functor ⋙
          (ConstantCompletion.derivedPull (G α U) (W α U) (adjW α U)
            (ConstantCompletion.completedMap (G α U) A I)).functor).map f)) → IsIso f := by
  classical
  let B := ConstantCompletion.completed (proEtaleModelTopology X) A I
  let Bₛ := fun α ↦ ConstantCompletion.completed (proEtaleModelTopology (s.domain α)) A I
  let Bᵤ := fun α U ↦
    ConstantCompletion.completed ((proEtaleModelTopology (s.domain α)).over U) A I
  let P := fun α ↦ ConstantCompletion.pull (F α) (ConstantCompletion.completedMap (F α) A I)
  let Q := fun α U ↦ ConstantCompletion.pull (G α U)
    (ConstantCompletion.completedMap (G α U) A I)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod B)
  let : ∀ α, HasDerivedCategory (ConstantCompletion.Mod (Bₛ α)) :=
    fun α ↦ HasDerivedCategory.standard _
  let : ∀ α U, HasDerivedCategory (ConstantCompletion.Mod (Bᵤ α U)) :=
    fun α U ↦ HasDerivedCategory.standard _
  have : ∀ α, PreservesFiniteLimits (P α) := fun α ↦ (pull_exact _ _ (adj α) _).1
  have : ∀ α, PreservesFiniteColimits (P α) := fun α ↦ (pull_exact _ _ (adj α) _).2
  have : ∀ α U, PreservesFiniteLimits (Q α U) :=
    fun α U ↦ (pull_exact _ _ (adjW α U) _).1
  have : ∀ α U, PreservesFiniteColimits (Q α U) :=
    fun α U ↦ (pull_exact _ _ (adjW α U) _).2
  have hmod (M : ConstantCompletion.Mod B)
      (hM : ∀ (α : Fin s.n) (U : proEtaleSiteModel (s.domain α))
        (g : U ⟶ (AsSmall.up : (s.domain α).ProEt ⥤
          proEtaleSiteModel (s.domain α)).obj (⊤_ (s.domain α).ProEt)),
        V α g → IsZero (((P α) ⋙ Q α U).obj M)) : IsZero M := by
    apply strataModules_detectZero X A I s L hL F M
    intro α
    have : (AsSmall.up : (s.domain α).ProEt ⥤
        proEtaleSiteModel (s.domain α)).IsEquivalence :=
      inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1}
        (C := (s.domain α).ProEt)).functor.IsEquivalence
    apply coveringModules_detectZero (proEtaleModelTopology (s.domain α)) _
      (terminalIsTerminal.isTerminalObj
        (AsSmall.up : (s.domain α).ProEt ⥤ proEtaleSiteModel (s.domain α)) _)
      (V α) (hV α) A I (G α) ((P α).obj M)
    exact hM α
  have hzero (M : DerivedCategory (ConstantCompletion.Mod B))
      (hM : ∀ (α : Fin s.n) (U : proEtaleSiteModel (s.domain α))
        (g : U ⟶ (AsSmall.up : (s.domain α).ProEt ⥤
          proEtaleSiteModel (s.domain α)).obj (⊤_ (s.domain α).ProEt)),
        V α g → IsZero
        ((((P α) ⋙ Q α U).mapDerivedCategory).obj M)) : IsZero M := by
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro q
    apply hmod
    intro α U g hg
    exact ((DerivedCategory.homologyFunctor _ q).map_isZero (hM α U g hg)).of_iso
      ((((P α) ⋙ Q α U).mapDerivedCategoryHomologyFunctorIso q).app M)
  intro M N f hf
  have hPf (α : Fin s.n) (U : proEtaleSiteModel (s.domain α))
      (g : U ⟶ (AsSmall.up : (s.domain α).ProEt ⥤
        proEtaleSiteModel (s.domain α)).obj (⊤_ (s.domain α).ProEt))
      (hg : V α g) : IsIso (((P α) ⋙ Q α U).mapDerivedCategory.map f) := by
    let e₁ := pullDerivedIso (F α) (R α) (adj α)
      (ConstantCompletion.completedMap (F α) A I)
    let e₂ := pullDerivedIso (G α U) (W α U) (adjW α U)
      (ConstantCompletion.completedMap (G α U) A I)
    have hi := (NatIso.isIso_map_iff (NatIso.hcomp e₁ e₂) f).mp (hf α U g hg)
    exact (NatIso.isIso_map_iff (Functor.mapDerivedCategoryCompIso (P α) (Q α U)) f).mp hi
  obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  apply (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1
  apply hzero
  intro α U a ha
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    (((P α) ⋙ Q α U).mapDerivedCategory.map_distinguished _ hT)).2 (hPf α U a ha)

end AlgebraicGeometry.Scheme
