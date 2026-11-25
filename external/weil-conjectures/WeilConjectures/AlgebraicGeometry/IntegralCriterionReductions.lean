/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowers
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import WeilConjectures.AlgebraicGeometry.ExtendedCechCompletionModel
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientTerminal
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteRestrictionEncoding
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.AlgebraicGeometry.RingedLocalizationRestriction
import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Equivalence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
import WeilConjectures.CategoryTheory.NativeRingedRestrictionSlices
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparison
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all WeilConjectures.SixFunctors.ProEtale.IntegralCompletionPresentation
import WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares
import WeilConjectures.SixFunctors.ProEtale.IntegralSectionProjectionNormalization

/-!
# Constructibility of all integral reductions from the first

md
(blueprint: lemma-bounds-finite-reductions).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

-- In live this instance came globally from the Sheaf copy of InternalSectionTensorComparison;
-- the tip makes it local there.
attribute [local instance] Sheaf.monoidalCategory

/-- Derived completeness, constructibility of every positive reduction and a common
finite cohomological interval. The reduction index n denotes the exponent n+1.
There is no Tor-amplitude condition and no boundedness requirement on K itself.
The predicate is intrinsic to X and E; the global convention l != p has no role in it.
Source: Weil blueprint, order 1459, and the final paragraph of
sk-prop-integral-criterion-reductions
(blueprint: lemma-bounds-finite-reductions). -/
def continuousIntegralConstructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : ObjectProperty (DerivedCategory (AdicCompletion.Modules l E X)) :=
  fun K ↦ IsDerivedComplete l E X K ∧
    (∀ n : ℕ, constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1))
      X ((AdicCompletion.derivedReduction l E X n).obj K)) ∧
    ∃ r s : ℤ, r ≤ s ∧ ∀ (n : ℕ) (q : ℤ), q < r ∨ s < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X n).obj K))

private theorem finiteConstantEndomorphism (X : Scheme.{u})
    (h : sfbFiniteConstantSets X ⟶ sfbFiniteConstantSets X) : h = 𝟙 _ := by
  let J := Scheme.ProEt.topology X
  let O := FintypeCat.of (ULift.{u} Unit)
  let F := sfbFiniteConstantSets X
  have ht : IsTerminal (ULift.{u + 1, u} (ULift.{u} Unit)) :=
    (Types.isTerminalEquivUnique _).symm inferInstance
  have ht' : IsTerminal (F.obj O) :=
    (ht.isTerminalObj (constantSheaf J (Type (u + 1))) _).isTerminalObj
      (sheafToPresheaf J (Type (u + 1))) _
  have hO : h.app O = 𝟙 _ := ht'.hom_ext _ _
  apply NatTrans.ext
  funext T
  apply sheafify_hom_ext J _ _
    (((constantSheaf J (Type (u + 1))).obj (ULift.{u + 1, u} T)).property)
  ext V x
  let k : O ⟶ T := FintypeCat.homMk fun _ ↦ x.down
  let z := (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
    (ULift.{u + 1, u} (ULift.{u} Unit)))).app V (ULift.up (ULift.up ()))
  have hn := congrArg (fun t ↦ t.app V) (h.naturality k)
  rw [hO, Category.id_comp] at hn
  have hc : (F.map k).app V z =
      (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1, u} T))).app V x := by
    exact (congrArg (fun t ↦ t.app V
      (ULift.up (ULift.up () : ULift.{u} Unit))) (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map
        (uliftFunctor.{u + 1, u}.map ((forget FintypeCat).map k))))).symm
  change (h.app T).app V
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1, u} T))).app V x) =
    (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (ULift.{u + 1, u} T))).app V x
  rw [← hc]
  exact congrArg (fun t ↦ t z) hn

private theorem finiteRepresentation_unique (X : Scheme.{u})
    (a b : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X) : a = b := by
  apply Iso.ext
  have h := finiteConstantEndomorphism X (a.hom ≫ b.inv)
  have h' := congrArg (fun f ↦ f ≫ b.hom) h
  simpa using h'

/-- The projection-normalized comparison is independent of all auxiliary finite-set
representations and limit-cone witnesses. SfbIntegralComparison retains the unit
and all reduction equations, not just existence of an isomorphism.
Source: blueprint integral-limit clause 3; integral-criterion proof step 8
(blueprint: lemma-bounds-finite-reductions).
Proof: existence is sfb_integral_coefficient_limit. For uniqueness, the finite-label
representation is unique: on a singleton both sheaves are terminal, and naturality
with every singleton-to-finite-set inclusion fixes each constant label; sheafification
then fixes the whole natural transformation. For each cone witness the composite
j followed by its nth projection is the specified quotient on every integer, so
changing the cone changes none of these maps. The adjunction-mate normalization
therefore gives the same nth projection for both comparisons on every profinite
test object and continuous integer-valued function. The adjunction and Yoneda
identify the maps; finally the limit projections jointly distinguish them. -/
theorem integralLimitAbComparison_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃! e : (coefficientRing X (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E X,
      SfbIntegralComparison l E X e := by
  obtain ⟨a, c, j, hq, hc, _, _, _, e, he, hu⟩ :=
    sfb_integral_coefficient_limit l E X
  refine ⟨e, ⟨he.1, he.2.1, a, c, j, hq, hc, he.2.2⟩, ?_⟩
  intro e' he'
  obtain ⟨hm, hi, b, d, k, hq', hd, hn⟩ := he'
  have hab : b = a := finiteRepresentation_unique X b a
  subst b
  apply hu e'
  refine ⟨hm, hi, ?_⟩
  intro S f n
  rw [hn]
  congr 2
  apply ConcreteCategory.hom_ext
  intro x
  exact (hq' n (f x)).trans (hq n (f x)).symm

/-- The unique integral-limit comparison with the published adjunction-mate and
finite-projection normalization. No finite representation or equivalence is selected
from a bare existence statement.
Source: blueprint integral-limit clause 3; integral-criterion proof step 8
(blueprint: lemma-bounds-finite-reductions). -/
def integralLimitAbComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :=
  (integralLimitAbComparison_existsUnique l E X).exists.choose

private theorem continuousRingSheaf_topology_eq (T : Type u) [Ring T]
    (t₁ t₂ : TopologicalSpace T) (h : t₁ = t₂)
    (h₁ : @IsTopologicalRing T t₁ _) (h₂ : @IsTopologicalRing T t₂ _) :
    @Profinite.continuousMapRingSheafOfUniverse.{u, u} T t₁ _ h₁ =
      @Profinite.continuousMapRingSheafOfUniverse.{u, u} T t₂ _ h₂ := by
  subst t₂
  rfl

private theorem integralPointMon_eq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon.mk (DerivedNakayama.integerRing l E) = sfbCondensedIntegers l E := by
  have hm : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht := congrArg (fun m : PseudoMetricSpace E ↦
    m.toUniformSpace.toTopologicalSpace) hm.symm
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  have hs := continuousRingSheaf_topology_eq
    (Padic.coefficientExtensionIntegers l E) _ _ hti
    (by let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField; infer_instance)
    (by let := spectralNorm.normedField (Padic l) E; infer_instance)
  let F : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} →
      Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := fun R ↦
    Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)
  exact congrArg F hs

/-- The coefficient presentations have the same underlying abelian sheaves.
Source: blueprint integral-limit clause 3 and integral-criterion proof step 8
(blueprint: lemma-bounds-finite-reductions).
Proof: the section-ring construction keeps the additive group and restriction maps
of the internal ring. On the point the two continuous-function constructions have
identical sections and restrictions: the extending absolute value is the spectral
norm, hence defines the same topology. Presheaf extensionality and proof irrelevance
identify these sheaves, and applying the same point inverse image preserves equality.
The completed commutative ring sheaf retains the ring data of the completed ring
sheaf; forgetting its commutativity and multiplication keeps exactly its additive
groups and restrictions. Sheaf extensionality gives the second equality. -/
theorem integralSectionAbIdentifications (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) (AdicCompletion.ring l E X)) =
        (coefficientRing X (sfbCondensedIntegers l E)).X ∧
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E X) =
        sfbCompletedIntegersAb l E X := by
  constructor
  · change (upperStarFromPoint X).obj (DerivedNakayama.integerRing l E) =
      (upperStarFromPoint X).obj (sfbCondensedIntegers l E).X
    exact congrArg (fun R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ↦
      (upperStarFromPoint X).obj R.X) (integralPointMon_eq l E)
  · rfl

private theorem ringPresheafMon_eq
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (R : Sheaf J RingCat.{u + 1}) :
    (sheafToPresheaf J Ab.{u + 1}).monObjObj
      ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R) =
        R.obj.monObjCompForget₂ := by
  apply MonObj.ext
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let : MonObj A.obj := R.obj.monObjCompForget₂
  exact Sheaf.μ_comp_map_mul A

private theorem liftSectionRingIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (A : Sheaf J Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (S : Sheaf J CommRingCat.{u + 1})
    (a : A ≅ (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    [IsMonHom a.hom] :
    ∃! e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A ≅ S,
      (sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.hom = a.hom := by
  let F := (Monoidal.monFunctorCategoryEquivalence Cᵒᵖ Ab.{u + 1}).functor
  let h := Functor.whiskerRight
    (F.map ((sheafToPresheaf J Ab.{u + 1}).mapMon.map (Mon.ofHom a.hom)))
    InternalAbelianSheafModule.monToRing
  let k := Functor.whiskerRight
    (F.map ((sheafToPresheaf J Ab.{u + 1}).mapMon.map (Mon.ofHom a.inv)))
    InternalAbelianSheafModule.monToRing
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let B := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hmon : (sheafToPresheaf J Ab.{u + 1}).monObjObj B = R.obj.monObjCompForget₂ :=
    ringPresheafMon_eq J R
  let BP := F.obj ((sheafToPresheaf J Ab.{u + 1}).mapMon.obj (Mon.mk B)) ⋙
    InternalAbelianSheafModule.monToRing
  let b : BP ≅ R.obj := by
    refine NatIso.ofComponents (fun U ↦ ?_) (fun _ ↦ ?_)
    · refine @RingEquiv.toRingCatIso (BP.obj U) (R.obj.obj U)
        (RingCat.ring _) (RingCat.ring _) ?_
      refine { toEquiv := Equiv.refl _, map_add' := fun _ _ ↦ rfl, map_mul' := ?_ }
      intro x y
      change (((sheafToPresheaf J Ab.{u + 1}).monObjObj B).mul.app U).hom
        (TensorProduct.tmul ℤ x y) = _
      have hh := congrArg (fun m : MonObj B.obj ↦ m.mul) hmon
      rw [hh]
      rfl
    · ext x
      rfl
  let d : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A ≅ S :=
    { hom := ⟨{ app := fun U ↦
                  @CommRingCat.ofHom
                    ((InternalAbelianSheafModule.sectionRingSheaf J A).obj.obj U)
                    (S.obj.obj U) _ _ ((h ≫ b.hom).app U).hom
                naturality := fun U V f ↦ by
                  apply (forget₂ CommRingCat RingCat).map_injective
                  exact (h ≫ b.hom).naturality f }⟩
      inv := ⟨{ app := fun U ↦
                  @CommRingCat.ofHom (S.obj.obj U)
                    ((InternalAbelianSheafModule.sectionRingSheaf J A).obj.obj U)
                    _ _ ((b.inv ≫ k).app U).hom
                naturality := fun U V f ↦ by
                  apply (forget₂ CommRingCat RingCat).map_injective
                  exact (b.inv ≫ k).naturality f }⟩
      hom_inv_id := by
        ext U x
        have hh := congr_app (congrArg (fun f : A ⟶ A ↦ f.hom) a.hom_inv_id) U
        exact ConcreteCategory.congr_hom hh x
      inv_hom_id := by
        ext U x
        have hh := congr_app (congrArg (fun f : B ⟶ B ↦ f.hom) a.inv_hom_id) U
        exact ConcreteCategory.congr_hom hh x }
  have hd : (sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map d.hom = a.hom := by
    ext U x
    rfl
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Iso.ext
  apply (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  exact he.trans hd.symm

/-- Reconstructing section rings retains the unique projection-normalized coefficient
comparison. After the endpoint identifications, forgetting to abelian sheaves fixes
the entire underlying additive map.
Source: blueprint integral-limit clause 3 and integral-criterion proof step 8
(blueprint: lemma-bounds-finite-reductions).
Proof: the spectral absolute value defining DerivedNakayama.integerRing is the
spectral norm defining sfbCondensedIntegers, so the continuous-function sheaves and
their point pullbacks agree. The chosen abelian comparison is a monoid homomorphism
in both directions by sfb_integral_coefficient_limit. Evaluating its multiplication
and unit identities reconstructs a commutative-ring isomorphism on sections.
Naturality is unchanged. Forgetting to abelian sheaves is faithful, so the fixed
underlying comparison determines this ring isomorphism uniquely. -/
theorem integralSectionRingIso_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃! e : CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (AdicCompletion.ring l E X) ≅
        WeilConjectures.completedIntegralCommRingSheafUnrestricted l E X,
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.hom =
          eqToHom (integralSectionAbIdentifications l E X).1 ≫
            (integralLimitAbComparison l E X).hom ≫
              eqToHom (integralSectionAbIdentifications l E X).2.symm := by
  let J := Scheme.ProEt.topology X
  let A := AdicCompletion.ring l E X
  let B := sfbCompletedIntegersAb l E X
  let c := eqToIso (congrArg (coefficientRing X) (integralPointMon_eq l E))
  have hm : IsMonHom (integralLimitAbComparison l E X).hom :=
    (integralLimitAbComparison_existsUnique l E X).exists.choose_spec.1
  let := hm
  let am := c ≪≫ Mon.mkIso' (integralLimitAbComparison l E X)
  let a : A ≅ B := (Mon.forget _).mapIso am
  have ha : IsMonHom a.hom := am.hom.isMonHom_hom
  let := ha
  let S := WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E X
  obtain ⟨d, hd, _⟩ := liftSectionRingIso J A S a
  have hn : (sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map d.hom =
      eqToHom (integralSectionAbIdentifications l E X).1 ≫
        (integralLimitAbComparison l E X).hom ≫
          eqToHom (integralSectionAbIdentifications l E X).2.symm := by
    rw [hd]
    dsimp only [a, am, Iso.trans_hom, Functor.mapIso_hom, c, eqToIso.hom]
    rw [Functor.map_comp]
    change (Mon.forget _).map (eqToHom _) ≫ _ = _
    rw [eqToHom_map]
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  refine ⟨d, hn, ?_⟩
  intro e he
  apply Iso.ext
  apply (sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  exact he.trans hn.symm

/-- The ring comparison fixed by the published finite-projection normalization.
Source: blueprint integral-criterion proof step 8
(blueprint: lemma-bounds-finite-reductions). -/
def integralSectionRingIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :=
  (integralSectionRingIso_existsUnique l E X).exists.choose

/-- The actual section-action functor, followed by scalar transport along the inverse
of the specified coefficient isomorphism. Neither functor is chosen by existence.
Source: Stacks 00YV; blueprint integral-criterion proof step 8
(blueprint: lemma-bounds-finite-reductions). -/
def integralSectionFunctor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    AdicCompletion.Modules l E X ⥤ WeilConjectures.scalarReductionSource.{u, u} l E X :=
  (CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (AdicCompletion.ring l E X)).functor ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralSectionRingIso l E X).inv)

private noncomputable def restrictionRoundTrip
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{u + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private theorem restrictionTriangle
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) (M : SheafOfModules.{u + 1} S) :
    (SheafOfModules.restrictScalars c.hom).map ((restrictionRoundTrip c).inv.app M) ≫
      (restrictionRoundTrip c.symm).hom.app
        ((SheafOfModules.restrictScalars c.hom).obj M) = 𝟙 _ := by
  ext U x
  rfl

private noncomputable def restrictionEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp := restrictionTriangle c

private theorem restriction_isEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence :=
  (restrictionEquivalence c).isEquivalence_functor

/-- The prescribed section-action comparison is an additive equivalence.
Source: Stacks 00YV, 03DA; blueprint integral-criterion proof step 8
(blueprint: lemma-bounds-finite-reductions).
Proof: sectionModuleEquivalence is the existing exact equivalence with the same
underlying abelian sheaves. Restriction along the inverse coefficient isomorphism
has inverse restriction along its forward map. The unit and counit are the identity
on sections, with the two scalar actions identified by the inverse equations.
Both functors preserve addition on every section, so their composite is additive. -/
theorem integralSectionFunctor_properties (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    (integralSectionFunctor l E X).Additive ∧
      (integralSectionFunctor l E X).IsEquivalence := by
  let c := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (integralSectionRingIso l E X).symm
  let : (SheafOfModules.restrictScalars c.hom).IsEquivalence := restriction_isEquivalence c
  let F := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (AdicCompletion.ring l E X)
  let : F.functor.IsEquivalence := F.isEquivalence_functor
  constructor
  · dsimp only [integralSectionFunctor]
    infer_instance
  · exact inferInstanceAs (F.functor ⋙ SheafOfModules.restrictScalars c.hom).IsEquivalence

/-- Additivity of the actual section-action functor.
Source: blueprint integral-criterion proof step 8
(blueprint: lemma-bounds-finite-reductions). -/
instance integralSectionFunctor_additive (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : (integralSectionFunctor l E X).Additive :=
  (integralSectionFunctor_properties l E X).1

/-- Equivalence of the actual section-action functor.
Source: blueprint integral-criterion proof step 8
(blueprint: lemma-bounds-finite-reductions). -/
instance integralSectionFunctor_isEquivalence (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : (integralSectionFunctor l E X).IsEquivalence :=
  (integralSectionFunctor_properties l E X).2

private def integralEncoding (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) : IntegralPresentation.Encoding l E X where
  ringIso := integralSectionRingIso l E X
  modules := (integralSectionFunctor l E X).asEquivalence
  functor_eq := rfl
  additive := by
    change (integralSectionFunctor l E X).Additive
    infer_instance
  inverseAdditive := by
    let : (integralSectionFunctor l E X).asEquivalence.functor.Additive :=
      inferInstanceAs (integralSectionFunctor l E X).Additive
    infer_instance

private theorem finiteTopology_discrete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have hm : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht := congrArg (fun m : PseudoMetricSpace E ↦
    m.toUniformSpace.toTopologicalSpace) hm
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  apply QuotientAddGroup.discreteTopology
  apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
  have hb := (Padic.coefficientExtension_integers_coset_basis l E 0).mem_of_mem
    (i := n) trivial
  change @Membership.mem (Set (Padic.coefficientExtensionIntegers l E)) _ _
    (@nhds _ (TopologicalSpace.induced _ _) 0) _ at hb
  change @Membership.mem (Set (Padic.coefficientExtensionIntegers l E)) _ _
    (@nhds _ (TopologicalSpace.induced _ _) 0) _
  rw [← hti]
  have he : {y : Padic.coefficientExtensionIntegers l E |
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) y =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) 0} =
      (Padic.coefficientExtensionIdeal l E (n + 1)).toAddSubgroup := by
    ext y
    change _ = _ ↔ y ∈ Padic.coefficientExtensionIdeal l E (n + 1)
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
  rw [he] at hb
  exact hb

attribute [local irreducible] WeilConjectures.scalarReductionExistence
  WeilConjectures.scalarReductionDerivedExistence

private theorem reductionAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

private theorem reductionAbLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

private theorem reductionRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  hasSheafifyEssentiallySmallSite _ _

private theorem reductionSiteSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance] reductionSiteSmall

attribute [local instance] reductionAbSheafify reductionAbLocallyBijective reductionRingSheafify

attribute [local instance] WeilConjectures.scalarReductionExtensionAdditive
  WeilConjectures.scalarReductionRestrictionLimits
  WeilConjectures.scalarReductionRestrictionColimits
  Scheme.proEtaleRingRestrictScalars_preservesFiniteLimits
  Scheme.proEtaleRingRestrictScalars_preservesFiniteColimits

end AlgebraicGeometry.ProEtale
