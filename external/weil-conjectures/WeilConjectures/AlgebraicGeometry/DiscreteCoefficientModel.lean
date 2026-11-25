/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.AlgebraicGeometry.DiscreteCoefficientLocalModels
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonPresentation
import all WeilConjectures.AlgebraicGeometry.IntegralModelsCompletionTransport
import all WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
import all WeilConjectures.AlgebraicGeometry.NoetherianGlobalConstructibility
import all WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
import WeilConjectures.CategoryTheory.RingedCocontinuousMonoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-! # Normalized models for discrete constant coefficients

Source: Stacks Tags 03CY, 00YV and 09AJ.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint

namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

/-- The constant additive sheaf comparison, before reconstructing scalar actions.
Source: Stacks Tags 03CY and 00YV
(auxiliary; not a blueprint node). -/
def discreteCoefficientAbelianIso (X : Scheme.{u}) (A : Type u) [CommRing A] :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)) ≅ condensedRingObj (discreteObj A) X :=
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  letI : (coherentTopology Profinite.{u}).PreservesSheafification V :=
    GrothendieckTopology.instPreservesSheafification (coherentTopology Profinite.{u}) V
  (constantSchemeIso X).app (AddCommGrpCat.of (ULift.{u + 1} A)) ≪≫
    (upperStarFromPoint X).mapIso
      (((constantCommuteCompose (coherentTopology Profinite.{u}) V).app
        (CommRingCat.of (ULift.{u + 1} A))).symm)

attribute [local irreducible] discreteCoefficientAbelianIso

@[irreducible] private def coefficientRingIso (X : Scheme.{u}) (A : Type u) [CommRing A]
    (k : Type (u + 1)) [CommRing k] (e : ULift.{u + 1} A ≃+* k) :
    ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj (discreteObj A) X) :=
  (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    CommRingCat.{u + 1}).mapIso (e.symm.toCommRingCatIso) ≪≫
  ((Scheme.CompletedConstantAlgebra.constantsIso X).app
    (CommRingCat.of (ULift.{u + 1} A))).symm ≪≫
  ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous
    CommRingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).mapIso
        (discreteRingIso A X)

/-- Normalization fixes the reconstructed coefficient map on every constant section.
The scalar relabelling is specified by e, rather than an arbitrary residue-field automorphism.
Source: Stacks Tags 03CY and 00YV
(auxiliary; not a blueprint node). -/
def DiscreteCoefficientNormalized (X : Scheme.{u}) (A : Type u) [CommRing A]
    (k : Type (u + 1)) [CommRing k] (e : ULift.{u + 1} A ≃+* k)
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj (discreteObj A) X)) : Prop :=
  ∀ (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) (a : ULift.{u + 1} A),
    c.hom.hom.app (op U)
        ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          ((Functor.const _).obj (CommRingCat.of k))).app (op U) (e a)) =
      (discreteCoefficientAbelianIso X A).hom.hom.app (op (AsSmall.down.obj U))
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app
            (op (AsSmall.down.obj U)) a)

private theorem coefficientRingIso_normalized (X : Scheme.{u}) (A : Type u) [CommRing A]
    (k : Type (u + 1)) [CommRing k] (e : ULift.{u + 1} A ≃+* k) :
    DiscreteCoefficientNormalized X A k e (coefficientRingIso X A k e) := by
  intro U a
  have hn := ConcreteCategory.congr_hom (congr_app
    (toSheafify_naturality (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      ((Functor.const _).map (CommRingCat.ofHom e.symm.toRingHom))) (op U)) (e a)
  have hu := Scheme.CompletedConstantAlgebra.constantsIso_unit X
    (ULift.{u + 1} A) (op U) a
  have hi := ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app (op U))
    ((Scheme.CompletedConstantAlgebra.constantsIso X).app
      (CommRingCat.of (ULift.{u + 1} A))).hom_inv_id)
      ((toSheafify (Scheme.ProEt.topology X) ((Functor.const _).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app (op (AsSmall.down.obj U)) a)
  delta coefficientRingIso
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  change (discreteRingIso A X).hom.hom.app (op (AsSmall.down.obj U))
    (((Scheme.CompletedConstantAlgebra.constantsIso X).app
      (CommRingCat.of (ULift.{u + 1} A))).inv.hom.app (op U)
      (((constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        CommRingCat.{u + 1}).map (CommRingCat.ofHom e.symm.toRingHom)).hom.app (op U)
          ((toSheafify _ ((Functor.const _).obj (CommRingCat.of k))).app (op U) (e a)))) = _
  have hn' : ((constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      CommRingCat.{u + 1}).map (CommRingCat.ofHom e.symm.toRingHom)).hom.app (op U)
        ((toSheafify _ ((Functor.const _).obj (CommRingCat.of k))).app (op U) (e a)) =
      (toSheafify _ ((Functor.const _).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app (op U) a := by
    change (toSheafify _ ((Functor.const _).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app (op U) (e.symm (e a)) =
      ((constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        CommRingCat.{u + 1}).map (CommRingCat.ofHom e.symm.toRingHom)).hom.app (op U)
          ((toSheafify _ ((Functor.const _).obj (CommRingCat.of k))).app (op U) (e a)) at hn
    rw [e.symm_apply_apply] at hn
    exact hn.symm
  rw [hn']
  have hu' : ((Scheme.CompletedConstantAlgebra.constantsIso X).app
      (CommRingCat.of (ULift.{u + 1} A))).inv.hom.app (op U)
        ((toSheafify _ ((Functor.const _).obj
          (CommRingCat.of (ULift.{u + 1} A)))).app (op U) a) =
      (toSheafify (Scheme.ProEt.topology X) ((Functor.const _).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app (op (AsSmall.down.obj U)) a := by
    change ((Scheme.CompletedConstantAlgebra.constantsIso X).app
        (CommRingCat.of (ULift.{u + 1} A))).inv.hom.app (op U)
          ((ConstantCompletion.constantSection (J :=
            Scheme.CompletedConstantAlgebra.smallTopology X) a).val (op U)) =
      (X.adicLisseConstantUnit (ULift.{u + 1} A)).app
        (AsSmall.down.op.obj (op U)) a
    rw [← hu]
    exact hi
  rw [hu', discreteRingIso_unit]
  delta discreteCoefficientAbelianIso
  rfl

/-- Normalization uniquely determines the coefficient ring isomorphism.
Source: the sheafification universal property, Stacks Tag 03CY
(auxiliary; not a blueprint node).
Proof: precompose both maps with the constant-presheaf sheafification unit. Their components
agree on e(a) by normalization, and every scalar has this form because e is surjective.
The sheafification universal property gives equality of the maps and hence of the isomorphisms.
-/
theorem discreteCoefficientNormalized_unique (X : Scheme.{u}) (A : Type u) [CommRing A]
    (k : Type (u + 1)) [CommRing k] (e : ULift.{u + 1} A ≃+* k)
    {c d : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj (discreteObj A) X)}
    (hc : DiscreteCoefficientNormalized X A k e c)
    (hd : DiscreteCoefficientNormalized X A k e d) : c = d := by
  apply Iso.ext
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.coefficientProEtaleModelTopology.{u, u} X) _ _
    (smallRing X (condensedRingObj (discreteObj A) X)).property
  ext U a
  obtain ⟨b, rfl⟩ := e.surjective a
  exact (hc U.unop b).trans (hd U.unop b).symm

/-- Section-action transport, small-site precomposition, and the specified scalar restriction.
All three functors are existing constructions; no object is selected from an existence theorem.
Source: Stacks Tags 00YV, 09A5 and 03CY
(auxiliary; not a blueprint node). -/
def discreteCoefficientModel (X : Scheme.{u}) (A : Type u) [CommRing A]
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj (discreteObj A) X)) :=
  smallModules X (condensedRingObj (discreteObj A) X) ⋙ ConstantCompletion.res c.hom

private theorem scalar_restriction_equivalence
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence := by
  let e := CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars c.hom)
    (SheafOfModules.restrictScalars c.inv)
    (ConstantScalarRestriction.restrictCancelIso J c.inv c.hom c.inv_hom_id).symm
    (ConstantScalarRestriction.restrictCancelIso J c.hom c.inv c.hom_inv_id)
  exact e.isEquivalence_functor

/-- The specified discrete model is an equivalence for every coefficient ring isomorphism.
Source: section reconstruction, site equivalence and restriction along a ring isomorphism
(auxiliary; not a blueprint node).
Proof: compose the existing section-action equivalence, the pushforward equivalence of the
small and original sites, and the inverse scalar-restriction equivalence. -/
instance discreteCoefficientModel_isEquivalence (X : Scheme.{u}) (A : Type u) [CommRing A]
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj (discreteObj A) X)) :
    (discreteCoefficientModel X A k c).IsEquivalence := by
  let : (smallModules X (condensedRingObj (discreteObj A) X)).IsEquivalence :=
    smallModules_equivalence X (condensedRingObj (discreteObj A) X)
  let : (ConstantCompletion.res c.hom).IsEquivalence := scalar_restriction_equivalence
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)
  exact inferInstanceAs
    (smallModules X (condensedRingObj (discreteObj A) X) ⋙
      ConstantCompletion.res c.hom).IsEquivalence

/-- Discrete coefficient transport is additive, since all its maps retain the section maps.
Source: section-action and scalar restriction
(auxiliary; not a blueprint node).
Proof: section reconstruction and site precomposition are additive sectionwise, and scalar
restriction changes only the action, so their composite preserves sums of morphisms. -/
instance discreteCoefficientModel_additive (X : Scheme.{u}) (A : Type u) [CommRing A]
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj (discreteObj A) X)) :
    (discreteCoefficientModel X A k c).Additive := by
  have := smallModules_additive X (condensedRingObj (discreteObj A) X)
  exact inferInstanceAs
    (smallModules X (condensedRingObj (discreteObj A) X) ⋙
      ConstantCompletion.res c.hom).Additive

attribute [local irreducible] discreteCoefficientModel smallModules
  InternalAbelianSheafModule.sectionModuleFunctor
  InternalAbelianSheafModule.sectionRingSheaf

attribute [local instance] SheafOfModules.monoidalCategory
  Sheaf.monoidalCategory Sheaf.symmetricCategory

attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientRingSheafify in
/-- Discrete coefficients admit a normalized exact monoidal section-action model, preserving
finite constructible local models. This is a statement about module sheaves, with no complexes,
integral completion, residue reduction, or Tor predicate.

Source: Stacks Tags 03CY, 00YV, 09A5 and 09AJ; blueprint integral-models proof (1)--(2).
(auxiliary; not a blueprint node).

Proof: the monoidal constant-sheaf comparison identifies the pulled-back discrete ring with
its constant sheaf on X. Reconstruct its section ring and precompose with AsSmall.down.
The constant-sheaf precomposition comparison and e give c. Its map on constants is the
formula in DiscreteCoefficientNormalized; local surjectivity of sheafification makes this
formula determine c uniquely. Section reconstruction, precomposition along the site
equivalence, and restriction along c are additive equivalences. The section tensor comparison
and the pure-tensor isomorphisms for the other factors supply the strong monoidal structure.
On each stratum a finite presentation is the cokernel of a finite scalar matrix. Each factor
carries that matrix and its cokernel to the identical presentation, relabelled by e. The same
cover therefore trivializes the model in either direction. Convert covering families to their
generated covering sieves, and conversely refine a covering sieve by a covering family.
The Noetherian global constructibility theorem identifies the resulting finite global
stratification with the affine-local predicate. The inverse comparisons retain the same
strata and finitely presented modules. Empty schemes and zero rings use the same constructions.
-/
theorem discrete_coefficient_model (X : Scheme.{u}) [IsNoetherian X]
    (A : Type u) [CommRing A] (k : Type (u + 1)) [CommRing k] [IsNoetherianRing k]
    (e : ULift.{u + 1} A ≃+* k) :
    ∃ c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
        smallRing X (condensedRingObj (discreteObj A) X),
      DiscreteCoefficientNormalized X A k e c ∧
      Nonempty (discreteCoefficientModel X A k c).Monoidal ∧
      ∀ N, IsConstantModelConstructible (discreteObj A) X N ↔
        Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, u} X k
          ((discreteCoefficientModel X A k c).obj N) := by
  let c := coefficientRingIso X A k e
  refine ⟨c, coefficientRingIso_normalized X A k e, ?_, ?_⟩
  · let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
    let hsf : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
      WeilConjectures.integralCoefficientAbSheafify.{u, 0} X
    let : (Scheme.ProEt.topology X).WEqualsLocallyBijective Ab.{u + 1} :=
      WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
    let R := condensedRingObj (discreteObj A) X
    let S := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R
    let F : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt := AsSmall.down
    let : F.IsEquivalence :=
      inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsEquivalence
    let : F.IsDenseSubsite (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (Scheme.ProEt.topology X) := by
      change F.IsDenseSubsite (F.inducedTopology (Scheme.ProEt.topology X))
        (Scheme.ProEt.topology X)
      infer_instance
    let a : (sheafCompose (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k) ≅
        (F.sheafPushforwardContinuous RingCat.{u + 1}
          (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).obj
            ((sheafCompose (Scheme.ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
      (sheafCompose (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
    let H := SheafOfModules.pushforward.{u + 1} (F := F)
      (J := Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (K := Scheme.ProEt.topology X)
      (R := (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) a.hom
    let E := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor
    have hcomm : IsCommMonObj R := by
      exact isCommMonObj_condensedRingObj (discreteObj A) X
    let : E.Monoidal := (@sectionMonoidal_exists.{u + 1, u, u + 1} X.ProEt inferInstance
      (Scheme.ProEt.topology X) inferInstance hsf inferInstance R
      inferInstance hcomm).some
    let : H.Monoidal := (SheafOfModules.ringed_cocontinuous_monoidal F
      (ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k)
      S a).some
    let : (E ⋙ H).Monoidal := inferInstance
    let B := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
    let T := (F.sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).obj B
    let P := SheafOfModules.pushforward.{u + 1} (F := F)
      (J := Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (K := Scheme.ProEt.topology X) (R := B) (𝟙 T)
    let j : P ⋙ ConstantCompletion.res c.hom ≅ H :=
      SheafOfModules.pushforwardComp (F := 𝟭 (Scheme.coefficientProEtaleSiteModel.{u, u} X))
        (G := F) (J := Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (K := Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (K' := Scheme.ProEt.topology X) (R := T) (R' := B) a.hom (𝟙 T)
    let i : E ⋙ H ≅ discreteCoefficientModel X A k c := by
      delta discreteCoefficientModel smallModules
      exact (Functor.isoWhiskerLeft E j).symm ≪≫ (Functor.associator E P
        (ConstantCompletion.res c.hom)).symm
    exact ⟨Functor.Monoidal.transport i⟩
  · intro N
    delta discreteCoefficientModel
    have hqc : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
    rw [IsConstantModelConstructible, ite_eq_left hqc]
    rw [Scheme.proEtale_noetherian_global_constructibility.{u, u} X k]
    constructor
    · rintro ⟨S, hS⟩
      refine ⟨S, S.isConstructible_stratum, ?_⟩
      intro a
      apply (Scheme.finiteLocalModels_iff_presentation _ k _).mp
      exact (discrete_coefficient_local_models (S.immersion a) A k e c N).mp (hS a)
    · rintro ⟨S, _, hS⟩
      refine ⟨S, ?_⟩
      intro a
      apply (discrete_coefficient_local_models (S.immersion a) A k e c N).mpr
      exact (Scheme.finiteLocalModels_iff_presentation _ k _).mpr (hS a)

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
