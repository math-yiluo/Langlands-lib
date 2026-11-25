/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueAlgebraTower
import WeilConjectures.AlgebraicGeometry.AdicEtaleStalkLevels
import all WeilConjectures.AlgebraicGeometry.AdicPerfectModelCompleteReduction
import WeilConjectures.AlgebraicGeometry.LisseCoefficientConstructible

/-! # Normalized algebraic stalk towers on a weakly contractible covering

Source: Stacks Project, proetale.tex, Tag 09C6, before algebraic reconstruction.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

/-- Tensoring with a quotient commutes with exact restriction to the actual slice. -/
private theorem adicResidue_scalar_slice
    {D : Type w} [SmallCategory D] (T : GrothendieckTopology D)
    {R S : Sheaf T CommRingCat.{w}} (φ : R ⟶ S) (U : D)
    (M : CategoryTheory.ConstantCompletion.D R) :
    Nonempty
      ((adicResidueRestriction S U).obj ((CategoryTheory.ConstantCompletion.extend φ).obj M) ≅
        (CategoryTheory.ConstantCompletion.extend ((T.overPullback CommRingCat U).map φ)).obj
          ((adicResidueRestriction R U).obj M)) := by
  classical
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod S)
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod (R.over U))
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod (S.over U))
  let r : CategoryTheory.ConstantCompletion.Mod R ⥤
      CategoryTheory.ConstantCompletion.Mod (R.over U) :=
    SheafOfModules.overFunctor.{w} (siteModuleRings R) U
  let s : CategoryTheory.ConstantCompletion.Mod S ⥤
      CategoryTheory.ConstantCompletion.Mod (S.over U) :=
    SheafOfModules.overFunctor.{w} (siteModuleRings S) U
  have : r.Additive := ringedOverFunctor_additive R U
  have : s.Additive := ringedOverFunctor_additive S U
  have : PreservesFiniteLimits r := ringedSite_overFunctor_limits T R U
  have : PreservesFiniteColimits r := ringedSite_overFunctor_colimits T R U
  have : PreservesFiniteLimits s := ringedSite_overFunctor_limits T S U
  have : PreservesFiniteColimits s := ringedSite_overFunctor_colimits T S U
  let P₀ := (CategoryTheory.ConstantCompletion.Q R).objPreimage M
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P₀
  have := hf
  let eP : (CategoryTheory.ConstantCompletion.Q R).obj P ≅ M :=
    asIso ((CategoryTheory.ConstantCompletion.Q R).map f) ≪≫
      (CategoryTheory.ConstantCompletion.Q R).objObjPreimageIso M
  have hk : P.IsKFlatTensor :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP
  have hU := (SheafOfModules.ringedSite_restriction_exact_kflat T R U).2.2 P hP
  have hkU : ((AdicPerfectModel.overComplex R U).obj P).IsKFlatTensor :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp hU
  let φU := (T.overPullback CommRingCat U).map φ
  have hcomp : IsIso ((CategoryTheory.ConstantCompletion.extendComparison φ).app P) :=
    (CategoryTheory.ConstantCompletion.derivedExtension φ).computation P hk
  have hcompU : IsIso ((CategoryTheory.ConstantCompletion.extendComparison φU).app
      ((AdicPerfectModel.overComplex R U).obj P)) :=
    (CategoryTheory.ConstantCompletion.derivedExtension φU).computation _ hkU
  let e₁ := (adicResidueRestriction S U).mapIso
    ((CategoryTheory.ConstantCompletion.extend φ).mapIso eP.symm ≪≫
      asIso ((CategoryTheory.ConstantCompletion.extendComparison φ).app P)) ≪≫
        s.mapDerivedCategoryFactors.app
          (((CategoryTheory.ConstantCompletion.change φ).mapHomologicalComplex (.up ℤ)).obj P)
  let e₂ := (CategoryTheory.ConstantCompletion.extend φU).mapIso
    ((adicResidueRestriction R U).mapIso eP.symm ≪≫ r.mapDerivedCategoryFactors.app P) ≪≫
      asIso ((CategoryTheory.ConstantCompletion.extendComparison φU).app
        ((AdicPerfectModel.overComplex R U).obj P)) ≪≫
      (CategoryTheory.ConstantCompletion.Q (S.over U)).mapIso
        (AdicPerfectModel.changeOverComplexIso φ U P)
  exact ⟨e₁ ≪≫ e₂.symm⟩

/-- The finite reductions admit normalized algebraic stalk towers on one covering.
No complex over the complete base ring is constructed here; A need not be J-complete.
Source: Stacks Project, proetale.tex, Tag 09C6, first paragraph through the choice
of an affine weakly contractible covering; Tags 09C2, 094I, 09BI and 090K.
(auxiliary; not a blueprint node).

Proof: Restrict M along the constant-to-completed coefficient map. The constant
completion equivalence preserves its local derived completeness and identifies all
finite reductions. The bounded lisse residue is constructible by the one-stratum
stratification. Apply adic_constructible_finite_reductions to obtain the etale
complexes C_n and their normalized consecutive quotient maps. Cover X by connected
clopen components of affine Noetherian charts. Restrict the specified finite
complexes and their quotient maps to those charts; the finite-reduction construction
has already been made globally, so no local preservation of completion is needed.
The ideal J/J^(n+1) in
the Noetherian quotient ring is nilpotent. Nilpotent-reduction lissity makes every
C_n lisse, with the common boundedness and Tor interval. Fix a geometric point of
each nonempty connected chart. Exact tensor-compatible stalks give the algebraic
levels E_n and consecutive reduction isomorphisms. Take their adjoint transposes
for the transitions; the canonical scalar-extension adjunctions are the tower's
extension fields. Connected etale perfect constancy proves E_0 perfect and
identifies the pullback of every C_n on every affine weakly contractible object
with constant E_n. Apply an affine weakly contractible cover to each chart, using
localization and the coefficient-sized model equivalences to identify its slices.
Transitivity assembles these into a covering of the final object. Retain E_n and
their normalized transitions on each member. Empty charts use the empty covering.
Only individual level isomorphisms are asserted, so no compatible markings are
chosen on the weakly contractible objects. No inverse limit over A is used. -/
theorem adicResidue_stalk_tower_family
    (X : Scheme.{u}) [IsNoetherian X]
    {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A)
    (M : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A J))
    (_hcomplete : CategoryTheory.ConstantCompletion.IsComplete
      (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X) A
        J 0) M)
    (C : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A J 0))
    (_hbounded : ∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (_hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) (A ⧸ J ^ (0 + 1))
      ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (a b : ℤ) (_hab : a ≤ b)
    (_htor : ∀ P : CategoryTheory.ConstantCompletion.Cx
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := smallModelComparisonEtaleTopology.{u, v} X)
        (R := CategoryTheory.ConstantCompletion.finite
          (smallModelComparisonEtaleTopology.{u, v} X) A J 0) P →
      Nonempty ((CategoryTheory.ConstantCompletion.Q
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)).obj P ≅ C) →
      ∀ (N : CategoryTheory.ConstantCompletion.Mod
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0))
        (q : ℤ), q < a ∨ b < q →
        IsZero (adicResidueTensorCohomology.{max v (u + 1)}
          (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X)
            A J 0) P N q))
    (_hres : Nonempty
      ((CategoryTheory.ConstantCompletion.extend
        (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X)
          A J 0)).obj M ≅
        (adicResidueComparison.{u, v} X (A ⧸ J ^ (0 + 1))).obj C)) :
    ∃ (I : Type (max v (u + 1)))
      (V : I → coefficientProEtaleSiteModel.{u, v} X)
      (f : ∀ i : I, V i ⟶
        (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj (⊤_ X.ProEt)),
      Sieve.ofArrows V f ∈ coefficientProEtaleModelTopology.{u, v} X _ ∧
      ∀ i : I,
        IsAffine ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj
          (V i)).left ∧
        AdicResidueSliceWeaklyContractible.{u, v} X (V i) ∧
        ∃ T : AdicResidueAlgebraTower J,
          ∀ n : ℕ, Nonempty
            ((adicResidueFiniteConstant.{u, v} X J (V i) n).obj (T.level n) ≅
              (adicResidueLocalReduction.{u, v} X J (V i) n).obj
                ((adicResidueRestriction
                  (CategoryTheory.ConstantCompletion.completed
                    (coefficientProEtaleModelTopology.{u, v} X) A J) (V i)).obj M)) := by
  classical
  let T := coefficientProEtaleModelTopology.{u, v} X
  let φ := CategoryTheory.ConstantCompletion.coefficientMap T A J
  obtain ⟨e, ⟨he⟩⟩ := CategoryTheory.ConstantCompletion.equivalence T A J
  let N := (e.functor.obj ⟨M, _hcomplete⟩).obj
  let eN : N ≅ (CategoryTheory.ConstantCompletion.dres φ).obj M := he.app ⟨M, _hcomplete⟩
  have hc : adicFiniteComplete X A J N := (e.functor.obj ⟨M, _hcomplete⟩).property
  have e₀ : (adicFinitePullback X (adicFiniteCoeff J 0)).obj C ≅
      adicFiniteReduction X J N 0 := by
    let h := _hres.some
    let d := (CategoryTheory.ConstantCompletion.finiteDerivedComparison T A J 0).choose
    exact h.symm ≪≫ (d.app M).symm ≪≫
      (CategoryTheory.ConstantCompletion.extend
        (CategoryTheory.ConstantCompletion.quotient T A J 0)).mapIso eN.symm
  have hC : IsCoefficientBoundedConstructibleEtale X (adicFiniteCoeff J 0) C := by
    refine ⟨fun q ↦ lisseCoefficient_constructible X _ _ (_hlisse q), ?_⟩
    obtain ⟨c, d, hv⟩ := _hbounded
    exact ⟨min c d, d, min_le_right c d, fun q hq ↦ hv q
      (hq.elim (fun h ↦ Or.inl (h.trans_le (min_le_left c d))) Or.inr)⟩
  obtain ⟨_, _, _, Cn, alpha, beta, hcon, htor, hzero, hcoc, hnorm⟩ :=
    adic_constructible_finite_reductions X A J N hc C hC e₀ a b _hab ⟨_hab, _htor⟩
  have hlisse₀ : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteCoeff J 0)
      ((adicResidueCohomology
        (CategoryTheory.ConstantCompletion.finite
          (smallModelComparisonEtaleTopology.{u, v} X) A J 0) q).obj (Cn 0)) := by
    obtain ⟨hz, _⟩ := hzero
    simpa only [hz] using _hlisse
  obtain ⟨I, V, f, hcover, hlocal⟩ := adicEtale_stalk_levels X J Cn hcon a b htor
    hlisse₀ (fun n ↦ beta (Nat.le_succ n))
  refine ⟨I, V, f, hcover, ?_⟩
  intro i
  obtain ⟨haff, hwc, E, hperf, hstep, hconst⟩ := hlocal i
  let L (n : ℕ) := ConstantScalarRealization.moduleDerivedExtension
    (Ideal.Quotient.mk (J ^ (n + 1)))
  let adj (n : ℕ) : L n ⊣ DerivedCategory.adicLevelRestriction J n :=
    ConstantScalarRealization.moduleDerivedAdjunction (Ideal.Quotient.mk (J ^ (n + 1)))
  let Ls (n : ℕ) := ConstantScalarRealization.moduleDerivedExtension
    (Ideal.Quotient.factorPowSucc J (n + 1))
  let adjs (n : ℕ) : Ls n ⊣ DerivedCategory.adicStepRestriction J n :=
    ConstantScalarRealization.moduleDerivedAdjunction (Ideal.Quotient.factorPowSucc J (n + 1))
  let Talg : AdicResidueAlgebraTower J :=
    { level := E
      transition := fun n ↦ (adjs n).homEquiv _ _ (hstep n).some.hom
      extension := L
      adjunction := adj
      stepExtension := Ls
      stepAdjunction := adjs
      normalized := fun n ↦ by
        rw [Equiv.symm_apply_apply]
        infer_instance
      residuePerfect := hperf }
  refine ⟨haff, hwc, Talg, ?_⟩
  intro n
  obtain ⟨d, _⟩ := CategoryTheory.ConstantCompletion.finiteDerivedComparison T A J n
  let er : adicFiniteReduction X J N n ≅
      (CategoryTheory.ConstantCompletion.extend
        (CategoryTheory.ConstantCompletion.projection T A J n)).obj M :=
    (CategoryTheory.ConstantCompletion.extend
      (CategoryTheory.ConstantCompletion.quotient T A J n)).mapIso eN ≪≫ d.app M
  exact ⟨(hconst n).some ≪≫
    (adicResidueRestriction (CategoryTheory.ConstantCompletion.finite T A J n) (V i)).mapIso
      (alpha n ≪≫ er) ≪≫
    (adicResidue_scalar_slice T
      (CategoryTheory.ConstantCompletion.projection T A J n) (V i) M).some⟩

end AlgebraicGeometry.Scheme
