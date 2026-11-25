/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalRealizationData
public import WeilConjectures.AlgebraicGeometry.RationalConeModels.RationalRealizationFiniteConeModels
import WeilConjectures.AlgebraicGeometry.RationalStratum.RationalStratumIntegralModels
import WeilConjectures.AlgebraicGeometry.ContinuousRational.RationalContinuousFiniteFreeCriterion
import all WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import all WeilConjectures.AlgebraicGeometry.Rational.RationalModuleRealizationFunctor
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! # Integral quotient models for a rational sheaf filtration

Source: Bhatt--Scholze, Lemma 6.8.13 and Proposition 6.8.14(2)
(blueprint: lem-per-rational-continuous-filtration-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
private def coefficientEncoding (X : Scheme.{u}) :
    AlgebraicGeometry.ProEtale.latticeCoefficientSheaf X
      (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅
      rationalCoefficientSheaf l X E := by
  let := coefficientExtensionNormedField l E
  let e := WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E)
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have hei : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  exact
    { hom := ⟨{
        app := fun _ ↦ CommRingCat.ofHom
          { toFun := fun f ↦ ⟨fun x ↦ ULift.up (e (f.down x)),
                continuous_uliftUp.comp (he.continuous.comp f.down.continuous)⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun _ ↦ CommRingCat.ofHom
          { toFun := fun f ↦ ULift.up ⟨fun x ↦ e.symm (f x).down,
                hei.continuous.comp (continuous_uliftDown.comp f.continuous)⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by ext V f; rfl
      inv_hom_id := by ext V f; rfl }

private theorem coefficientEncoding_normalization (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (f : C(U.unop.left, WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
    (x : U.unop.left) :
    rationalCoefficientValue l E X U ((coefficientEncoding l E X).hom.hom.app U (ULift.up f)) x
      = WithAbs.ofAbs (f x) := by
  rfl

private def exactDerivedSingle (X : Base.{u} l)
    (s : RationalModuleRealization l E X.scheme)
    (M : pbcModules X.scheme (pbcAdicCompletion X.scheme (pbcIntegralDatum l E))) :
    (pbcDerivedExtend (s.integralIso.hom ≫ s.inclusion)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((pbcExtend (s.integralIso.hom ≫ s.inclusion)).obj M) := by
  have := s.ordinary_exact.1
  have := s.ordinary_exact.2
  let T := pbcExtend (s.integralIso.hom ≫ s.inclusion)
  let D := pbcDerivedExtend (s.integralIso.hom ≫ s.inclusion)
  let ε := pbcExtensionCounit (s.integralIso.hom ≫ s.inclusion)
  let V := HomotopyCategory.quasiIso
    (pbcModules X.scheme (pbcAdicCompletion X.scheme (pbcIntegralDatum l E))) (.up ℤ)
  have : D.IsLeftDerivedFunctor ε V := pbcDerivedExtension_universal _
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom V :=
    Functor.isLeftDerivedFunctor_of_inverts V _ T.mapDerivedCategoryFactorsh
  let e := Functor.leftDerivedNatIso D T.mapDerivedCategory ε
    T.mapDerivedCategoryFactorsh.hom V (Iso.refl _)
  exact e.app _ ≪≫ (T.mapDerivedCategorySingleFunctor 0).app M

private def integralEncoding (X : Scheme.{u}) :
    AlgebraicGeometry.ProEtale.latticeCoefficientSheaf X
        (AlgebraicGeometry.ProEtale.latticeCoefficientIntegers l E) ⟶
      integralCoefficientSheaf l X E := by
  let := coefficientExtensionNormedField l E
  let e := WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E)
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  exact ⟨{
    app := fun _ ↦ CommRingCat.ofHom
      { toFun := fun f ↦ ⟨fun x ↦ ULift.up ⟨e (f.down x).val, (f.down x).property⟩,
          continuous_uliftUp.comp
            ((he.continuous.comp (continuous_subtype_val.comp f.down.continuous)).subtype_mk _)⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    naturality := fun _ _ _ ↦ rfl }⟩

private theorem finiteIso_eq (X : Base.{u} l)
    (s : RationalModuleRealization l E X.scheme) (n : ℕ) :
    s.finiteIso n = AlgebraicGeometry.ProEtale.RationalStratum.finiteComparison l E X.scheme n := by
  let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  apply Iso.ext
  apply (cancel_epi (pbcLevelConstantComparison X.scheme (pbcIntegralDatum l E) n).hom).mp
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (finiteContinuousCoefficientSheaf l X.scheme E n).property
  ext U a
  apply ContinuousMap.ext
  intro x
  have hu := congrArg (fun z ↦ z.app U)
    (rationalFiniteScalars_constantUnit (pbcIntegralDatum l E) X.scheme n)
  have hu' := ConcreteCategory.congr_hom hu a
  have hf := s.finite_normalization n U a x
  rw [hu'] at hf
  change finiteContinuousCoefficientValue l E X.scheme n U
    (((pbcLevelConstantComparison X.scheme (pbcIntegralDatum l E) n).hom ≫
      (s.finiteIso n).hom).hom.app U
        ((toSheafify (ProEt.topology X.scheme)
          ((Functor.const X.scheme.ProEtᵒᵖ).obj
            (CommRingCat.of (PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1))))
            ).app U a)) x = _ at hf
  have hq := congrArg (fun f ↦ f.app U (integralCoefficientULift l E n a))
    (continuousCoefficientConstantComparison_unit X.scheme (finiteCoefficientRing l E n))
  have hqx := congrArg
    (fun z : C(U.unop.left, finiteCoefficientRing l E n) ↦ z x) hq
  apply ULift.ext
  change (finiteContinuousCoefficientValue l E X.scheme n U _ x).down = _
  refine (congrArg ULift.down hf).trans ?_
  dsimp only [AlgebraicGeometry.ProEtale.RationalStratum.finiteComparison, Iso.trans_hom,
    Iso.symm_hom]
  simp only [Iso.hom_inv_id_assoc, Functor.mapIso_hom]
  have hn := ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality (ProEt.topology X.scheme)
      ((Functor.const X.scheme.ProEtᵒᵖ).map
        (integralCoefficientULift l E n).toCommRingCatIso.hom)) U) a
  change _ = (finiteContinuousCoefficientValue l E X.scheme n U
    (((discreteContinuousCoefficientIso X.scheme).app
      (finiteCoefficientRing l E n)).hom.hom.app U
      ((constantSheaf (ProEt.topology X.scheme) CommRingCat.{u + 1}).map
        (integralCoefficientULift l E n).toCommRingCatIso.hom |>.hom.app U
          ((toSheafify (ProEt.topology X.scheme)
            ((Functor.const X.scheme.ProEtᵒᵖ).obj (CommRingCat.of
              (PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1))))).app U a))) x).down
  erw [← hn]
  exact (congrArg ULift.down hqx).symm

private theorem modelScalarComparison (X : Base.{u} l)
    (s : RationalModuleRealization l E X.scheme)
    (N : SheafOfModules.{u + 1} (AlgebraicGeometry.ProEtale.latticeModuleRing X.scheme
      (AlgebraicGeometry.ProEtale.latticeCoefficientIntegers l E)))
    (b : pbcAdicCompletion X.scheme (pbcIntegralDatum l E) ≅
      AlgebraicGeometry.ProEtale.latticeCoefficientSheaf X.scheme
        (AlgebraicGeometry.ProEtale.latticeCoefficientIntegers l E))
    (hb : ∀ (n : ℕ) (W : X.scheme.ProEt)
      (z : (AlgebraicGeometry.ProEtale.latticeCoefficientSheaf X.scheme
        (AlgebraicGeometry.ProEtale.latticeCoefficientIntegers l E)).obj.obj (op W))
      (x : W.left),
      (finiteContinuousCoefficientValue l E X.scheme n (op W)
        ((b.inv ≫ pbcAdicProjection X.scheme (pbcIntegralDatum l E) n ≫
          (AlgebraicGeometry.ProEtale.RationalStratum.finiteComparison l E X.scheme n).hom).hom.app
            (op W) z) x).down =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
          ⟨WithAbs.ofAbs (z.down x).val, (z.down x).property⟩) :
    Nonempty ((pbcExtend (s.integralIso.hom ≫ s.inclusion)).obj
        ((pbcRestrict b.hom).obj N) ≅
      (pbcRestrict (coefficientEncoding l E X.scheme).inv).obj
        (AlgebraicGeometry.ProEtale.integralModelRationalize l E X.scheme N)) := by
  let := coefficientExtensionNormedField l E
  let c := integralEncoding l E X.scheme
  have hb' : b.inv ≫ s.integralIso.hom = c := by
    apply (cancel_mono s.integralIso.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply limit.hom_ext
    intro n
    let : TopologicalSpace (finiteCoefficientRing l E n.unop) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l E n.unop) := ⟨rfl⟩
    apply (cancel_mono (s.finiteIso n.unop).hom).mp
    apply Sheaf.hom_ext
    ext U z
    apply ContinuousMap.ext
    intro x
    apply ULift.ext
    change (finiteContinuousCoefficientValue l E X.scheme n.unop U
      ((b.inv ≫ pbcAdicProjection X.scheme (pbcIntegralDatum l E) n.unop ≫
        (s.finiteIso n.unop).hom).hom.app U z) x).down = _
    conv_lhs => rw [finiteIso_eq l E X s]
    refine (hb n.unop U.unop z x).trans ?_
    exact (s.integral_normalization n.unop U (c.hom.app U z) x).symm
  let a := AlgebraicGeometry.ProEtale.integralLatticeCoefficientMap X.scheme l E
  let e := coefficientEncoding l E X.scheme
  let α := s.integralIso.hom ≫ s.inclusion
  have hsq : b.inv ≫ α = a ≫ e.hom := by
    rw [← Category.assoc, hb']
    apply Sheaf.hom_ext
    ext U z
    apply ContinuousMap.ext
    intro x
    apply ULift.ext
    exact s.inclusion_normalization U.unop (c.hom.app U z) x
  let eb := WeilConjectures.restrictionEquivalence ((adicLisseForget X.scheme).mapIso b)
  let ee := WeilConjectures.restrictionEquivalence ((adicLisseForget X.scheme).mapIso e.symm)
  let adj₁ := eb.toAdjunction.comp (pbcScalarAdjunction α)
  let adj₂ := (pbcScalarAdjunction a).comp ee.toAdjunction
  let r := pbcRestrictComp b.inv α (b.inv ≫ α) rfl ≪≫
    (pbcRestrictComp a e.hom (b.inv ≫ α) hsq.symm).symm
  let v := (adj₁.ofNatIsoRight r).leftAdjointUniq adj₂
  exact ⟨v.app N ≪≫ (pbcRestrict e.inv).mapIso
    (eqToIso (reductionChange_obj_eq X.scheme a N))⟩

/-- Retain the finite stratum filtration as degree-zero completed integral quotient models
for the specified raw rational realization.
Source: Bhatt--Scholze, Lemma 6.8.13 and the proof of Proposition 6.8.14(2)
(blueprint: lem-per-rational-continuous-filtration-models).

Proof: identify the published continuous coefficient presentation with the WithAbs
presentation by the pointwise field equivalence. The finite free criterion makes F
continuous constructible. Apply the stratum integral-model theorem, which gives a finite
filtration, integral stratum lattices, constructible extensions of these lattices, and
normalized rational quotient isomorphisms. Transport the filtration back along the
coefficient equivalence, an exact equivalence, so cokernels and monomorphisms are preserved.
For each integral piece N the completed-model certificate identifies single(N) with an
object of the completed constructible category by restriction along the normalized
completed coefficient isomorphism. Give this object to the Filtration.model field.
The realization's object equality and exact scalar-extension cohomology comparison
identify its realization with single of the rationalization of N. Compose with the
specified rationalization/extension comparison and the cokernel identification from
the stratum theorem. All arrows in Filtration are the transported original filtration
arrows; exactness preserves its zero start and final isomorphism. This constructs the
required data without choosing a derived object from a mere essential-image assertion. -/
theorem rationalContinuousFiltrationModels (X : Base.{u} l)
    (s : RationalModuleRealization l E X.scheme)
    (F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
    (hF : ∃ t : FiniteLocallyClosedStratification X.scheme, ∀ i : Fin t.n,
      ((proEtaleModuleInverseImage (t.immersion i)
        (rationalCoefficientSheaf l X.scheme E)).obj F).IsFiniteLocallyFree) :
    Nonempty (RationalConeModels.Filtration l E X.scheme s F) := by
  classical
  let e := coefficientEncoding l E X.scheme
  let T := pbcRestrict e.inv
  let q := (WeilConjectures.restrictionRoundTrip
    ((adicLisseForget X.scheme).mapIso e)).app F
  have hconstruct := (rationalContinuousFiniteFreeCriterion l E X e
    (coefficientEncoding_normalization l E X.scheme) F).mpr hF
  obtain ⟨m, H, a, d, ha, hz, hf, hc, hd, U, S, t, hS, L, N,
    hgeom, hdim, hL, hN, hpiece, hcomplete, α, c, j, hj, β, hβ⟩ :=
    AlgebraicGeometry.ProEtale.RationalStratum.exists_filtration_integral_models l E
      X.scheme X.dimension X.prime_unit ((pbcRestrict e.hom).obj F) hconstruct
  let P (k : Fin m) := (AlgebraicGeometry.ProEtale.RationalStratum.piece (U k) (t k)
    (AlgebraicGeometry.ProEtale.latticeCoefficientIntegers l E)).obj (N k)
  let b (k : Fin m) := (hcomplete k).choose
  let M (k : Fin m) := (pbcRestrict (b k).hom).obj (P k)
  let K (k : Fin m) : RationalConeModels.Integral l E X.scheme :=
    ⟨(DerivedCategory.singleFunctor _ 0).obj (M k), (hcomplete k).choose_spec.2⟩
  have hm (k : Fin m) : Nonempty
      ((pbcExtend (s.integralIso.hom ≫ s.inclusion)).obj (M k) ≅
        T.obj (AlgebraicGeometry.ProEtale.integralModelRationalize l E X.scheme (P k))) :=
    modelScalarComparison l E X s (P k) (b k) (hcomplete k).choose_spec.1
  refine ⟨{
    length := m
    H := fun k ↦ T.obj (H k)
    inclusion := fun k ↦ T.map (a k) ≫ q.hom
    step := fun k ↦ T.map (d k)
    mono := ?_
    start := T.map_isZero hz
    finish := ?_
    commutes := ?_
    step_mono := ?_
    model := K
    degreeZero := fun k ↦ ⟨M k, ⟨Iso.refl _⟩⟩
    quotient := fun k ↦ ?_ }⟩
  · intro k
    have := ha k
    infer_instance
  · have := hf
    infer_instance
  · intro k
    rw [← Category.assoc, ← T.map_comp, hc]
  · intro k
    have := hd k
    infer_instance
  · let v := (hm k).some
    exact eqToIso (s.objects (K k)) ≪≫ exactDerivedSingle l E X s (M k) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (v ≪≫ T.mapIso (β k ≪≫ (c k).symm) ≪≫ PreservesCokernel.iso T (d k))

end AlgebraicGeometry.Scheme.ContinuousRational
