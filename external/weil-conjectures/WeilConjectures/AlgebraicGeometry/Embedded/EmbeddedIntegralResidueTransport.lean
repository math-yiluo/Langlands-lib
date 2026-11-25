/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.Embedded.EmbeddedIntegralResidueSquare
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible

/-! # Transport of embedded integral coefficients

Source: the integral-models Stacks comparison, Stacks Tag 09C1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  IntegralModelsStacks.smallDerivedObject IntegralModelsStacks.smallModules
  IntegralModelsStacks.smallMap

private def inverseRestrictionEquivalence
    {C : Type*} [Category C] [MonoidalCategory C]
    {R S : C} [MonObj R] [MonObj S]
    (e : R ≅ S) [IsMonHom e.hom] [IsMonHom e.inv] :
    Mod C R ≌ Mod C S :=
  CategoryTheory.Equivalence.mk (Mod.comap e.inv) (Mod.comap e.hom)
    ((Mod.comapId R).symm ≪≫ Mod.comapCongr e.hom_inv_id.symm ≪≫
      Mod.comapComp e.hom e.inv)
    ((Mod.comapComp e.inv e.hom).symm ≪≫ Mod.comapCongr e.inv_hom_id ≪≫
      Mod.comapId S)

private theorem residueProperty_iso
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (e : K ≅ L)
    (h : (∀ n : ℤ, IsConstantModelConstructible Λ X
      ((DerivedCategory.homologyFunctor _ n).obj K)) ∧
      _root_.DerivedCategory.finiteTorAmplitude _ K) :
    (∀ n : ℤ, IsConstantModelConstructible Λ X
      ((DerivedCategory.homologyFunctor _ n).obj L)) ∧
      _root_.DerivedCategory.finiteTorAmplitude _ L := by
  exact ⟨fun n ↦ constructible_iso ((DerivedCategory.homologyFunctor _ n).mapIso e)
    (h.1 n), (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e h.2⟩

private theorem residueProperty_coefficientIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u})
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    ((∀ n : ℤ, IsConstantModelConstructible Λ X
      ((DerivedCategory.homologyFunctor _ n).obj K)) ∧
      _root_.DerivedCategory.finiteTorAmplitude _ K) ↔
    ((∀ n : ℤ, IsConstantModelConstructible Λ' X
      ((DerivedCategory.homologyFunctor _ n).obj
        ((Mod.comap ((upperStarFromPoint X).map e.inv.hom)).mapDerivedCategory.obj K))) ∧
      _root_.DerivedCategory.finiteTorAmplitude _
        ((Mod.comap ((upperStarFromPoint X).map e.inv.hom)).mapDerivedCategory.obj K)) := by
  have forward {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
      [MonObj A] [MonObj B] [IsCommMonObj A] [IsCommMonObj B]
      (d : Mon.mk A ≅ Mon.mk B) (L : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X)))
      (h : (∀ n : ℤ, IsConstantModelConstructible A X
        ((DerivedCategory.homologyFunctor _ n).obj L)) ∧
        _root_.DerivedCategory.finiteTorAmplitude _ L) :
      (∀ n : ℤ, IsConstantModelConstructible B X
        ((DerivedCategory.homologyFunctor _ n).obj
          ((Mod.comap ((upperStarFromPoint X).map d.inv.hom)).mapDerivedCategory.obj L))) ∧
        _root_.DerivedCategory.finiteTorAmplitude _
          ((Mod.comap ((upperStarFromPoint X).map d.inv.hom)).mapDerivedCategory.obj L) := by
    obtain ⟨a, b, hab⟩ := h.2
    have hb : DerivedCategory.TStructure.t.bounded L :=
      (DerivedCategory.exists_homologyConcentratedIn_iff_bounded L).mp
        ⟨a, b, DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hab⟩
    have hc := constantModelCtf_coefficientIso d X ⟨L, ⟨⟨hb, h.1⟩, h.2⟩⟩
    exact ⟨hc.1.2, hc.2⟩
  refine ⟨forward e K, fun h ↦ ?_⟩
  let i : condensedRingObj Λ X ≅ condensedRingObj Λ' X :=
    (upperStarFromPoint X).mapIso ((Mon.forget _).mapIso e)
  have : IsMonHom i.hom := inferInstanceAs
    (IsMonHom ((upperStarFromPoint X).map e.hom.hom))
  have : IsMonHom i.inv := inferInstanceAs
    (IsMonHom ((upperStarFromPoint X).map e.inv.hom))
  let E := inverseRestrictionEquivalence i
  have : E.functor.Additive := inferInstanceAs (Mod.comap i.inv).Additive
  have : E.inverse.Additive := inferInstanceAs (Mod.comap i.hom).Additive
  exact residueProperty_iso X (E.mapDerivedCategory.unitIso.app K).symm
    (forward e.symm _ h)

private def derivedResidueSquare (X : Scheme.{u})
    {A B T U : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj A] [MonObj B] [MonObj T] [MonObj U]
    [IsCommMonObj A] [IsCommMonObj B] [IsCommMonObj T] [IsCommMonObj U]
    (d : A ≅ B) [IsMonHom d.hom] [IsMonHom d.inv]
    (r : T ≅ U) [IsMonHom r.hom] [IsMonHom r.inv]
    (q : A ⟶ T) [IsMonHom q] (q' : B ⟶ U) [IsMonHom q']
    (h : d.hom ≫ q' = q ≫ r.hom) :
    (Mod.extendScalars q).leftDerivedFunctor ⋙ (Mod.comap r.inv).mapDerivedCategory ≅
      (Mod.comap d.inv).mapDerivedCategory ⋙ (Mod.extendScalars q').leftDerivedFunctor := by
  let D := inverseRestrictionEquivalence d
  let R := inverseRestrictionEquivalence r
  have : D.functor.Additive := inferInstanceAs (Mod.comap d.inv).Additive
  have : D.inverse.Additive := inferInstanceAs (Mod.comap d.hom).Additive
  have : R.functor.Additive := inferInstanceAs (Mod.comap r.inv).Additive
  have : R.inverse.Additive := inferInstanceAs (Mod.comap r.hom).Additive
  let rightSquare : Mod.comap q' ⋙ D.inverse ≅ R.inverse ⋙ Mod.comap q :=
    (Mod.comapComp d.hom q').symm ≪≫ Mod.comapCongr h ≪≫ Mod.comapComp q r.hom
  let rightDerivedSquare :
      (Mod.comap q').mapDerivedCategory ⋙ D.inverse.mapDerivedCategory ≅
        R.inverse.mapDerivedCategory ⋙ (Mod.comap q).mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso rightSquare ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
  let adj := (D.toAdjunction.mapDerivedCategoryAdjunction).comp
    (Mod.derivedExtendMapDerivedCategoryAdjunction q')
  let adj' := ((Mod.derivedExtendMapDerivedCategoryAdjunction q).comp
    R.toAdjunction.mapDerivedCategoryAdjunction).ofNatIsoRight rightDerivedSquare.symm
  exact adj'.leftAdjointUniq adj

private theorem inverse_square {C : Type*} [Category C]
    {A B R S : C} (a : A ≅ B) (b : R ≅ S) (f : A ⟶ R) (g : B ⟶ S)
    (h : a.hom ≫ g = f ≫ b.hom) : a.inv ≫ f = g ≫ b.inv := by
  apply (cancel_epi a.hom).mp
  apply (cancel_mono b.hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using h.symm

private theorem map_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B R S : C} (a : A ⟶ B) (b : B ⟶ S)
    (c : A ⟶ R) (d : R ⟶ S) (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  simpa only [Functor.map_comp] using congrArg F.map h

/-- A continuous coefficient ring isomorphism preserves the first-residue condition.

Source: integral-models-stacks, first-quotient transport; Stacks Tag 09C1
(blueprint: lem-sfb-embedded-integral-residue-transport).

Proof: evaluating e on the point gives an isomorphism of the integer rings, and
naturality on points identifies its action on all continuous functions. It carries
constant functions to constant functions and the maximal ideal to the maximal ideal.
Since pi generates this ideal, the first quotients are isomorphic, and their quotient
maps commute with the integer-ring isomorphism. Apply constant sheafification and exact
inverse image to this square. Associativity of scalar extension and uniqueness of its
left derived functor identify the two first reductions after the scalar restrictions.
Restriction along the quotient-ring isomorphism is exact, so it commutes with homology
and preserves finite constant models: transport the scalar finite presentation, the
local model on the same cover and each stratum of the same finite stratification.
Its inverse reflects the same properties. The relative tensor comparison along a ring
isomorphism identifies tensoring with every test module on each slice. Exact restriction
preserves and reflects homology vanishing, and hence preserves and reflects each Tor
interval. Combining the cohomology and Tor comparisons proves the iff. No completeness
or boundedness of K is used.
-/
theorem embeddedIntegralResidueTransport
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)]
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (e : Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E.val) ≅
      sfbCondensedIntegers ℓ (ULift.{u} E.val))
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E))) :
    IntegralModelsEmbedded.residueConstructible ℓ E π X
      ((IntegralModelsEmbedded.restriction ℓ E X).obj K) ↔
    IntegralModelsStacks.residueCondition ℓ (ULift.{u} E.val) X
      ((IntegralModelsStacks.restriction ℓ (ULift.{u} E.val) X).obj
        ((Mod.comap ((upperStarFromPoint X).map
            e.inv.hom)).mapDerivedCategory.obj
          K)) := by
  obtain ⟨d, r, hd, hr⟩ := embeddedIntegralResidueSquare ℓ E π hπ e
  let A := IntegralModelsEmbedded.discreteObj.{u} (PadicAlgCl.integers ℓ E.1)
  let B := IntegralModelsStacks.discreteObj
    (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val))
  let T := IntegralModelsEmbedded.discreteObj.{u} (completedResidue ℓ E π 0)
  let U := IntegralModelsStacks.discreteObj
    (Padic.coefficientExtensionRing ℓ (ULift.{u} E.val) 1)
  let di : condensedRingObj A X ≅ condensedRingObj B X :=
    (upperStarFromPoint X).mapIso ((Mon.forget _).mapIso d)
  let ri : condensedRingObj T X ≅ condensedRingObj U X :=
    (upperStarFromPoint X).mapIso ((Mon.forget _).mapIso r)
  have : IsMonHom di.hom := inferInstanceAs
    (IsMonHom ((upperStarFromPoint X).map d.hom.hom))
  have : IsMonHom di.inv := inferInstanceAs
    (IsMonHom ((upperStarFromPoint X).map d.inv.hom))
  have : IsMonHom ri.hom := inferInstanceAs
    (IsMonHom ((upperStarFromPoint X).map r.hom.hom))
  have : IsMonHom ri.inv := inferInstanceAs
    (IsMonHom ((upperStarFromPoint X).map r.inv.hom))
  let q := IntegralModelsEmbedded.residueMap ℓ E π X
  let q' := IntegralModelsStacks.residueMap ℓ (ULift.{u} E.val) X
  have hq : di.hom ≫ q' = q ≫ ri.hom := by
    exact map_square (upperStarFromPoint X) _ _ _ _ hr
  let reductionSquare := derivedResidueSquare X di ri q q' hq
  let ce : integralCoefficientObject X ℓ E ≅
      condensedRingObj (IntegralModelsStacks.integersObj ℓ (ULift.{u} E.val)) X :=
    (upperStarFromPoint X).mapIso ((Mon.forget _).mapIso e)
  have : IsMonHom ce.inv := inferInstanceAs
    (IsMonHom ((upperStarFromPoint X).map e.inv.hom))
  have hs : di.inv ≫ IntegralModelsEmbedded.scalarMap ℓ E X =
      IntegralModelsStacks.scalarMap ℓ (ULift.{u} E.val) X ≫ ce.inv := by
    apply inverse_square di ce
    exact map_square (upperStarFromPoint X) _ _ _ _ hd
  let scalarSquare : IntegralModelsEmbedded.restriction ℓ E X ⋙
      (Mod.comap di.inv).mapDerivedCategory ≅
      (Mod.comap ce.inv).mapDerivedCategory ⋙
        IntegralModelsStacks.restriction ℓ (ULift.{u} E.val) X :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso
        ((Mod.comapComp di.inv (IntegralModelsEmbedded.scalarMap ℓ E X)).symm ≪≫
          Mod.comapCongr hs ≪≫ Mod.comapComp
            (IntegralModelsStacks.scalarMap ℓ (ULift.{u} E.val) X) ce.inv) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
  let L := (IntegralModelsEmbedded.restriction ℓ E X).obj K
  let comparison := reductionSquare.app L ≪≫
    (Mod.extendScalars q').leftDerivedFunctor.mapIso (scalarSquare.app K)
  exact (residueProperty_coefficientIso r X
    ((Mod.extendScalars q).leftDerivedFunctor.obj L)).trans
      ⟨fun h ↦ residueProperty_iso X comparison h,
        fun h ↦ residueProperty_iso X comparison.symm h⟩

end AlgebraicGeometry.ProEtale
