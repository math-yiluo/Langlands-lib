/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicImmersionResidueComparisonCore
import WeilConjectures.CategoryTheory.ConstantInverseImageScalarNormalization
import all WeilConjectures.CategoryTheory.RingedPullbackPresentationOnSites
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Residue comparisons for the specified completed immersion pullback

Source: Stacks Tags 03A0, 03CY, 06YY, 099L and 099R.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private local instance modelSheafify (S : Scheme.{u}) :
    HasSheafify (proEtaleModelTopology S) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u + 1, u + 1}

private local instance modelLocallyBijective (S : Scheme.{u}) :
    (proEtaleModelTopology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u + 1, u + 1}

attribute [local instance 50000] modelSheafify modelLocallyBijective

private local instance standardDerived {D : Type (u + 1)} [SmallCategory D]
    {J : GrothendieckTopology D} (O : Sheaf J CommRingCat.{u + 1}) :
    HasDerivedCategory (ConstantCompletion.Mod O) := HasDerivedCategory.standard _

private noncomputable local instance modelAbelian (S : Scheme.{u})
    (R : Sheaf (proEtaleModelTopology S) CommRingCat.{u + 1}) :
    Abelian (ConstantCompletion.Mod R) :=
  SheafOfModules.instAbelian.{u + 1, u + 1, u + 1, u + 1} _

attribute [local instance 40000] modelAbelian standardDerived

-- The CommRingCat and RingCat sheafification units define the same constant action.
private lemma restriction_smul
    {D : Type (u + 1)} [SmallCategory D] (J : GrothendieckTopology D)
    (k : Type (u + 1)) [CommRing k]
    (M : ConstantCompletion.Mod (ConstantCompletion.constant J k))
    (U : Dᵒᵖ) (a : k) (x : M.val.obj U) :
    a • (show ((ConstantScalarRestriction.restriction J k).obj M).obj.obj U from x) =
      (toSheafify J ((Functor.const Dᵒᵖ).obj (CommRingCat.of k))).app U a • x := by
  let e := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of k)
  have h : Functor.whiskerRight
      (toSheafify J ((Functor.const Dᵒᵖ).obj (CommRingCat.of k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫ e.hom.hom =
      toSheafify J ((Functor.const Dᵒᵖ).obj (RingCat.of k)) := by
    dsimp only [e, Iso.app_hom]
    rw [constantCommuteCompose_hom_app_hom, ← Category.assoc, sheafComposeIso_inv_fac]
    exact (toSheafify_naturality J
      (Functor.constComp Dᵒᵖ (CommRingCat.of k)
        (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)
  have hu := congrArg (fun f ↦ f.app U a) h
  have hi := congrArg (fun f ↦ f.hom.app U) e.hom_inv_id
  change e.inv.hom.app U
    ((toSheafify J ((Functor.const Dᵒᵖ).obj (RingCat.of k))).app U a) • x = _
  erw [← hu]
  exact congrArg (fun b ↦ b • x) (ConcreteCategory.congr_hom hi _)

-- The canonical direct-image coefficient map is fixed by its values on constant sections.
private def comparisonRingMap (S : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, 0} S) k ⟶
      ((smallModelComparisonInclusion.{u, 0} S).sheafPushforwardContinuous
        CommRingCat.{u + 1} (smallModelComparisonEtaleTopology.{u, 0} S)
        (proEtaleModelTopology S)).obj
          (ConstantCompletion.constant (proEtaleModelTopology S) k) :=
  ((sheafificationAdjunction (smallModelComparisonEtaleTopology.{u, 0} S)
    CommRingCat.{u + 1}).homEquiv _ _).symm
      (Functor.whiskerLeft (smallModelComparisonInclusion.{u, 0} S).op
        (toSheafify (proEtaleModelTopology S)
          ((Functor.const (proEtaleSiteModel S)ᵒᵖ).obj (CommRingCat.of k))))

private def comparisonDirect (S : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology S) k) ⥤
      ConstantCompletion.Mod
        (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, 0} S) k) :=
  SheafOfModules.pushforward.{u + 1} (F := smallModelComparisonInclusion.{u, 0} S)
    (J := smallModelComparisonEtaleTopology.{u, 0} S) (K := proEtaleModelTopology S)
    (S := siteModuleRings
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, 0} S) k))
    (R := siteModuleRings (ConstantCompletion.constant (proEtaleModelTopology S) k))
    ((sheafCompose (smallModelComparisonEtaleTopology.{u, 0} S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (comparisonRingMap S k))

-- Restriction to constant scalars commutes with this concrete continuous direct image.
private def comparisonDirectIso (S : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    comparisonDirect S k ⋙
        ConstantScalarRestriction.restriction (smallModelComparisonEtaleTopology.{u, 0} S) k ≅
      ConstantScalarRestriction.restriction (proEtaleModelTopology S) k ⋙
        (smallModelComparisonInclusion.{u, 0} S).sheafPushforwardContinuous
          (ModuleCat.{u + 1} k) (smallModelComparisonEtaleTopology.{u, 0} S)
          (proEtaleModelTopology S) := by
  let J := smallModelComparisonEtaleTopology.{u, 0} S
  let K := proEtaleModelTopology S
  let G := smallModelComparisonInclusion.{u, 0} S
  have hc (U : (smallModelComparisonEtaleSite.{u, 0} S)ᵒᵖ) (a : k) :
      (comparisonRingMap S k).hom.app U
          ((toSheafify J ((Functor.const _).obj (CommRingCat.of k))).app U a) =
        (toSheafify K ((Functor.const _).obj (CommRingCat.of k))).app (G.op.obj U) a :=
    congrArg (fun f ↦ f.app U a)
      (((sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv
        ((Functor.const _).obj (CommRingCat.of k))
        ((G.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj
          (ConstantCompletion.constant K k))).apply_symm_apply
        (Functor.whiskerLeft G.op
          (toSheafify K ((Functor.const _).obj (CommRingCat.of k)))))
  let f (M : ConstantCompletion.Mod (ConstantCompletion.constant K k)) :
      ((comparisonDirect S k ⋙ ConstantScalarRestriction.restriction J k).obj M) ⟶
        ((ConstantScalarRestriction.restriction K k ⋙
          G.sheafPushforwardContinuous (ModuleCat.{u + 1} k) J K).obj M) :=
    { hom :=
      { app := fun U ↦ ConcreteCategory.ofHom (C := ModuleCat.{u + 1} k)
          { toFun := id
            map_add' := by intros; rfl
            map_smul' := by
              intro a x
              rw [restriction_smul J k, restriction_smul K k]
              change (comparisonRingMap S k).hom.app U
                  ((toSheafify J ((Functor.const _).obj (CommRingCat.of k))).app U a) •
                    (show M.val.obj (G.op.obj U) from x) =
                (toSheafify K ((Functor.const _).obj (CommRingCat.of k))).app
                  (G.op.obj U) a • (show M.val.obj (G.op.obj U) from x)
              rw [hc] }
        naturality := by intros; ext x; rfl } }
  have hf (M : ConstantCompletion.Mod (ConstantCompletion.constant K k)) : IsIso (f M) := by
    have (U : (smallModelComparisonEtaleSite.{u, 0} S)ᵒᵖ) : IsIso ((f M).hom.app U) :=
      (ConcreteCategory.isIso_iff_bijective _).2 Function.bijective_id
    have : IsIso (f M).hom := NatIso.isIso_of_isIso_app _
    have : IsIso ((sheafToPresheaf J (ModuleCat.{u + 1} k)).map (f M)) :=
      inferInstanceAs (IsIso (f M).hom)
    exact isIso_of_reflects_iso (f M) (sheafToPresheaf J (ModuleCat.{u + 1} k))
  exact NatIso.ofComponents (fun M ↦ asIso (f M)) (by intros; ext U x; rfl)

-- Normalize the supplied algebraic lift, then restrict the geometric adjunction to modules.
private theorem comparisonPullAdjunction (S : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    Nonempty (ConstantCompletion.pull (adicResidueComparisonData.{u, 0} S)
        (ConstantCompletion.constantMap (adicResidueComparisonData.{u, 0} S) k) ⊣
      comparisonDirect S k) := by
  let J := smallModelComparisonEtaleTopology.{u, 0} S
  let K := proEtaleModelTopology S
  let G := smallModelComparisonInclusion.{u, 0} S
  let L := smallModelComparisonPullback.{u, 0} S
  let a := smallModelProEtaleComparison.{u, 0} S
  let F := adicResidueComparisonData.{u, 0} S
  let R := ConstantCompletion.constant J k
  let T := ConstantCompletion.constant K k
  let c := ConstantCompletion.constantMap F k
  let f := SheafOfModules.RingedPresentationOnSites.siteContinuousRingedTopos G L a T R
    (comparisonRingMap S k)
  have hc : (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map c =
      (F.algebra R).ringUnderlying.inv ≫ f.ringMap := by
    have h := ConstantCompletion.constantInverseImageScalarNormalization J K G L a F k
    apply (cancel_epi (F.algebra R).ringUnderlying.hom).mp
    change (F.algebra R).ringUnderlying.hom ≫
      (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map c = f.ringMap at h
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h
  exact SheafOfModules.RingedPresentationOnSites.supplied_adjunction
    f (F.rings.obj R) (F.algebra R) c hc

-- Compare left adjoints through their identified right adjoints, including AsSmall transport.
private theorem comparisonOrdinaryIso (S : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    Nonempty ((sfbEtaleResidueModel S k).functor ⋙
        ConstantCompletion.pull (adicResidueComparisonData.{u, 0} S)
          (ConstantCompletion.constantMap (adicResidueComparisonData.{u, 0} S) k) ≅
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) S ⋙
        (SfbAdicRestriction.modelEquivalence S (ModuleCat.{u + 1} k)).inverse ⋙
          (ConstantScalarRestriction.restriction
            (proEtaleModelTopology S) k).asEquivalence.inverse) := by
  let J := smallModelComparisonEtaleTopology.{u, 0} S
  let K := proEtaleModelTopology S
  let G := smallModelComparisonInclusion.{u, 0} S
  let EJ := (ConstantScalarRestriction.restriction J k).asEquivalence.symm
  let EK := (ConstantScalarRestriction.restriction K k).asEquivalence.symm
  let aT := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    G (ModuleCat.{u + 1} k) J K
  obtain ⟨ap⟩ := comparisonPullAdjunction S k
  let a₁ := EJ.toAdjunction.comp ap
  let a₂ := aT.comp EK.toAdjunction
  let e := (a₁.ofNatIsoRight (comparisonDirectIso S k)).leftAdjointUniq a₂
  let E := sfbImmersionEtaleModel S k
  let P := SfbAdicRestriction.modelEquivalence S (ModuleCat.{u + 1} k)
  let b₁ := E.toAdjunction.comp aT
  let b₂ := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} k) S).comp
    P.symm.toAdjunction
  let b := (b₁.ofNatIsoRight (Iso.refl _)).leftAdjointUniq b₂
  exact ⟨Functor.isoWhiskerLeft E.functor e ≪≫ Functor.isoWhiskerRight b EK.functor⟩

attribute [-instance] coefficientModelAdditiveSheafify coefficientEtaleModelAdditiveSheafify
  ConstantScalarRestriction.ringAbelian ConstantScalarRestriction.fixedAbelian
  ConstantScalarRestriction.ringGrothendieck ConstantScalarRestriction.fixedGrothendieck
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective in
/-- The etale-origin residue comparison, isolated from the fixed completed-model clause.
Source: Stacks Tags 03A0, 03CY, 06YY, 099L and 099R; Bhatt--Scholze, Lemma 6.5.8
(auxiliary; not a blueprint node).
Proof: constant-scalar restriction identifies the continuous module direct
image with fixed-coefficient direct image. Scalar normalization and the
ringed inverse-image adjunction identify the supplied algebraic pullback with
the fixed-coefficient comparison inverse image, by uniqueness of left adjoints.
Conjugate the etale/pro-etale pullback square by these identifications and the
AsSmall equivalences. This comparison makes the algebraic pullback left exact;
its adjunction also makes it right exact. Its termwise functor therefore
preserves quasi-isomorphisms, so the universal left-derived comparison is an
isomorphism. Compose its inverse with the exact functor's derived-category
factorization and the termwise square. This is the second clause of the parent
comparison statement; no completed-complex clause is used.
-/
theorem sfbImmersion_residueComparison_etale
    {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    letI := HasDerivedCategory.standard
      (ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology S)
        (A ⧸ I ^ (0 + 1))))
    ∀ C : CochainComplex
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ,
      Nonempty ((Functor.mapDerivedCategory.{u + 1, u + 2}
          (SfbResidueComparisonCore.sfbFixedResiduePull i (A ⧸ I ^ (0 + 1)))).obj
          (DerivedCategory.Q.obj
            (((ProEtale.comparisonUpperStar.{u + 2, u}
              (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) X).mapHomologicalComplex
                (.up ℤ)).obj C)) ≅
        (adicResidueComparison.{u, 0} S (A ⧸ I ^ (0 + 1))).obj
          (sfbImmersionResidue i I C)) := by
  intro C
  let k := A ⧸ I ^ (0 + 1)
  let F := adicResidueComparisonData.{u, 0} S
  let c := ConstantCompletion.constantMap F k
  let D := ConstantCompletion.derivedPull F (smallModelComparisonPushforward.{u, 0} S)
    (smallModelProEtaleComparison.{u, 0} S) c
  let T := ConstantCompletion.pull F c
  let P := SfbResidueComparisonCore.sfbFixedResiduePull i k
  let N := (SfbAdicRestriction.modelEquivalence S (ModuleCat.{u + 1} k)).inverse ⋙
    (ConstantScalarRestriction.restriction (proEtaleModelTopology S) k).asEquivalence.inverse
  obtain ⟨eS⟩ := comparisonOrdinaryIso S k
  let e : ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X ⋙ P ≅
      sfbImmersionResidueFunctor i k ⋙ T :=
    Functor.isoWhiskerRight
      (ProEtale.comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} k) i) N ≪≫
        Functor.isoWhiskerLeft (Etale.upperStar (ModuleCat.{u + 1} k) i)
          eS.symm
  let C' := ((sfbImmersionResidueFunctor i k).mapHomologicalComplex (.up ℤ)).obj C
  have hT : PreservesFiniteLimits T := by
    let E := sfbEtaleResidueModel S k
    let V := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) S ⋙ N
    have hV : PreservesFiniteLimits V := by
      dsimp only [V, N]
      infer_instance
    let h : T ≅ E.inverse ⋙ V :=
      (Functor.isoWhiskerRight E.counitIso T).symm ≪≫
        Functor.isoWhiskerLeft E.inverse eS
    exact preservesFiniteLimits_of_natIso h.symm
  have hT' : PreservesFiniteColimits T := by
    obtain ⟨ap⟩ := comparisonPullAdjunction S k
    have := ap.leftAdjoint_preservesColimits
    exact inferInstanceAs (PreservesFiniteColimits T)
  let W := HomologicalComplex.quasiIso
    (ConstantCompletion.Mod
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, 0} S) k)) (.up ℤ)
  have : D.functor.IsLeftDerivedFunctor D.comparison W := D.universal
  have hi : W.IsInvertedBy (T.mapHomologicalComplex (.up ℤ) ⋙
      ConstantCompletion.Q (ConstantCompletion.constant (proEtaleModelTopology S) k)) := by
    intro M M' f hf
    have : QuasiIso f := hf
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map
      ((T.mapHomologicalComplex (.up ℤ)).map f)))
  have : IsIso D.comparison :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts D.functor D.comparison hi
  have hD : IsIso (D.comparison.app C') := NatIso.isIso_app_of_isIso D.comparison C'
  let eC := (NatIso.mapHomologicalComplex e (.up ℤ)).app C
  exact ⟨P.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso eC ≪≫
    (asIso (D.comparison.app C')).symm⟩

end AlgebraicGeometry.Scheme
