/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientData
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Topology.Algebra.Group.Quotient
import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelQuotientChartComparison
import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelQuotientCohomologyDescent
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite reductions of integral scalar-model constructible sheaves -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ZeroObject
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteModelQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance] quotientModuleCategory quotientModuleAbelian quotientModuleDerived

private theorem finiteTopology_discrete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) :
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
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

private def double_homology_kernel
    {C : Type*} [Category C] [Abelian C] {X Y : C} (f : X ⟶ Y) :
    (HomologicalComplex.double f (c := ComplexShape.up ℤ)
      (i₀ := -1) (i₁ := 0) (by decide)).homology (-1) ≅ kernel f := by
  let K := HomologicalComplex.double f (c := ComplexShape.up ℤ)
    (i₀ := -1) (i₁ := 0) (by decide)
  let S : ShortComplex C := ShortComplex.mk (0 : (0 : C) ⟶ X) f (by simp)
  let e : K.sc' (-2) (-1) 0 ≅ S := ShortComplex.isoMk
    (eqToIso (by simp [K, S, HomologicalComplex.double]))
    (HomologicalComplex.doubleXIso₀ f (c := ComplexShape.up ℤ) (by decide))
    (HomologicalComplex.doubleXIso₁ f (c := ComplexShape.up ℤ) (by decide) (by decide))
    (by simp [K, S, HomologicalComplex.double])
    (by simp [K, S, HomologicalComplex.double_d, Category.assoc])
  exact ShortComplex.homologyMapIso
    (K.isoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫ e) ≪≫
    (S.asIsoHomologyπ rfl).symm ≪≫ S.cyclesIsoKernel

private def double_homology_cokernel
    {C : Type*} [Category C] [Abelian C] {X Y : C} (f : X ⟶ Y) :
    (HomologicalComplex.double f (c := ComplexShape.up ℤ)
      (i₀ := -1) (i₁ := 0) (by decide)).homology 0 ≅ cokernel f := by
  let K := HomologicalComplex.double f (c := ComplexShape.up ℤ)
    (i₀ := -1) (i₁ := 0) (by decide)
  let S : ShortComplex C := ShortComplex.mk f (0 : Y ⟶ (0 : C)) (by simp)
  let e : K.sc' (-1) 0 1 ≅ S := ShortComplex.isoMk
    (HomologicalComplex.doubleXIso₀ f (c := ComplexShape.up ℤ) (by decide))
    (HomologicalComplex.doubleXIso₁ f (c := ComplexShape.up ℤ) (by decide) (by decide))
    (eqToIso (by simp [K, S, HomologicalComplex.double]))
    (by simp [K, S, HomologicalComplex.double_d, Category.assoc])
    (by simp [K, S, HomologicalComplex.double])
  exact ShortComplex.homologyMapIso
    (K.isoSc' (-1) 0 1 (by simp) (by simp) ≪≫ e) ≪≫
    S.asIsoHomologyι rfl ≪≫ S.opcyclesIsoCokernel

private theorem differential_finite (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) [Finite (R l E n)] :
    Finite ↥(kernel (differential l E n a b v)) ∧
      Finite ↥(cokernel (differential l E n a b v)) := by
  constructor
  · exact Finite.of_equiv _
      (ModuleCat.kernelIsoKer (differential l E n a b v)).symm.toLinearEquiv.toEquiv
  · let : Finite ((Fin b → ULift.{u + 1} (R l E n)) ⧸
        (differential l E n a b v).hom.range) :=
      Finite.of_surjective _ (Submodule.mkQ_surjective _)
    exact Finite.of_equiv _
      (ModuleCat.cokernelIsoRangeQuotient (differential l E n a b v)).symm.toLinearEquiv.toEquiv

private def ordinary_homology_kernel (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) :
    (DerivedCategory.homologyFunctor _ (-1)).obj (ordinaryComplex l E T n a b v) ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
          (kernel (differential l E n a b v)) := by
  let F := constantSheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))
  let K := scalarComplex l E n a b v
  exact (DerivedCategory.homologyFunctorFactors _ (-1)).app _ ≪≫
    (K.sc (-1)).mapHomologyIso F ≪≫
    F.mapIso (double_homology_kernel (differential l E n a b v))

private def ordinary_homology_cokernel (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) :
    (DerivedCategory.homologyFunctor _ 0).obj (ordinaryComplex l E T n a b v) ≅
      (constantSheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
          (cokernel (differential l E n a b v)) := by
  let F := constantSheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))
  let K := scalarComplex l E n a b v
  exact (DerivedCategory.homologyFunctorFactors _ 0).app _ ≪≫
    (K.sc 0).mapHomologyIso F ≪≫
    F.mapIso (double_homology_cokernel (differential l E n a b v))

private theorem local_calculation (V : Scheme.{u}) (M : AdicCompletion.Modules l E V)
    (n : ℕ) [Finite (R l E n)] (enc : ∀ T : Scheme.{u}, Encoding l E n T) :
    LocalCalculation l E V M n enc := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  constructor
  intro S C i j P hP eP a b v w hinj hexact hsurj
  obtain ⟨e⟩ := chart_comparison l E V ((C i).X j) ((C i).f j ≫ S.immersion i)
    M n (enc _) P eP a b v w hinj hexact hsurj
  let h := (derivedEncoding l E n ((C i).X j) (enc ((C i).X j))).functor.mapIso e ≪≫
    (derivedEncoding l E n ((C i).X j) (enc ((C i).X j))).counitIso.app
      (ordinaryComplex l E _ n a b v)
  obtain ⟨hk, hc⟩ := differential_finite l E n a b v
  let := hk
  let := hc
  refine ⟨⟨e⟩, ⟨(ordinaryHomology l E n ((C i).X j) (-1)).mapIso h ≪≫
    ordinary_homology_kernel l E _ n a b v⟩,
    ⟨(ordinaryHomology l E n ((C i).X j) 0).mapIso h ≪≫
      ordinary_homology_cokernel l E _ n a b v⟩, hk, hc, ?_, ?_⟩
  · exact Module.finitePresentation_of_finite _ _
  · exact Module.finitePresentation_of_finite _ _

private theorem bounded_from_vanishing
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C)
    (h : ∀ q : ℤ, q ≠ -1 → q ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) :
    DerivedCategory.TStructure.t.bounded K := by
  refine ⟨⟨-1, (DerivedCategory.isGE_iff K (-1)).2 ?_⟩,
    ⟨0, (DerivedCategory.isLE_iff K 0).2 ?_⟩⟩
  · intro q hq
    exact h q (by omega) (by omega)
  · intro q hq
    exact h q (by omega) (by omega)

/-- Finite reductions of integral constructible scalar models, including the prescribed
matrix calculation. No completeness or geometric condition on the prime is assumed.

Source: blueprint main-20261015, localizing-closure ctf-equals-bc proof, Local models,
Locality and Strata; Stacks Tags 093M, 093J, 06YQ, 06YY, 0G7E and 09AJ
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible).

Proof:
1. The integral scalar ring is a DVR with finite residue field
(lem-weil-l-adic-extension-integers-dvr). Its positive quotients are finite by
lem-weil-valued-dvr-finite-quotients. The open coset basis of
lem-sfb-integers-coset-basis makes their quotient topology discrete. The constant
integral sheaf maps flatly to B, with quotient k_n, by
lemma-integral-models--1 and
lemma-comparison-completed-coefficients--1. Use
lem-sf-module-object-ordinary-coefficient-equivalence for the finite encoding.
2. For stratum and cover restrictions, sk-def-sfb-pullback-from-point-comp identifies
the coefficient rings and their actual quotient maps. Exactness follows from
lemma-inverse-image-coefficient-sheaves and lem-sfb-internal-module-operations-transport.
A flat-term K-flat resolution (lem-pc-kflat-resolution) remains such after pullback
(lem-weil-pbc-ringed-topos-kflat-pullback). The balanced comparisons of
lem-sfb-scalar-inverse-image-tower-diagram and lem-pur-derived-change-of-rings
identify reduction before and after restriction, compatibly for composites.
3. On a chosen cover chart take the specified exact scalar resolution; such resolutions
exist by lem-sfb-scalar-finite-free-resolutions. Flat extension preserves that exact
sequence with its original matrix, by lem-sfb-constant-finite-free-presentation-extension.
4. The resulting two-term free complex is K-flat by
lem-sfb-ringed-finite-free-resolution-tensor. Tensoring with the quotient computes the
derived reduction in its own coefficient category (lem-pur-derived-change-of-rings).
Its differential on basis vectors is the entrywise image of the original matrix under
the actual quotient homomorphism.
5. Exact constant realization and lem-weil-pbc-exact-functor-complex-cohomology identify
the cohomology with constant kernel and cokernel. Both are finite: one is a subset of
a finite power and the other a quotient. A finite module over a finite ring has a finite
presentation: use all elements as generators and all elements of its finite kernel as
relations. Rank zero and the zero module are included.
6. For other degrees the cohomology vanishes on each cover and stratum. Use
lem-sfb-proetale-object-inverse-image-restriction and lem-sfb-sheaf-cover-local-isomorphism
to descend from covers. Use lem-fix-constructible-open-closed-refinement to refine the
finite constructible partition to a finite open/closed tree. Induct upward using
proposition-extension-zero-restriction-closed-subscheme. Thus the interval [-1,0] is uniform in n.
7. Keep the original strata and covers. The finite kernel and cokernel models are
internal finite scalar models by lem-pe-finite-discrete-scalar-constant-models and
lem-pe-finite-discrete-encoding-pullback-fixed. They are ordinary locally constant
sheaves with finite stalks by lem-weil-pbc-proetale-finite-model-stalks. The two recorded
constructibility definitions give both bounded constructibility conclusions. Empty
strata have only the zero sheaf. No completion property of M is used. -/
theorem finite_model_sheaf_quotient_constructible
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (M : AdicCompletion.Modules l E V)
    (hM : IsConstantModelConstructible (DerivedNakayama.integerRing l E) V M) :
    ∀ n : ℕ, ∃ hf : Finite (R l E n),
      @DiscreteTopology (R l E n) (AdicCompletion.finiteTopology l E (n + 1)) ∧
      (∀ q : ℤ, q ≠ -1 → q ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj (reduction l E V M n))) ∧
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) V
        (reduction l E V M n) ∧
      (∃ enc : ∀ T : Scheme.{u}, Encoding l E n T,
        OrdinaryConclusion l E V M n hf (enc V) ∧ LocalCalculation l E V M n enc) := by
  classical
  intro n
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : Finite (R l E n) := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  have hd := finiteTopology_discrete l E n
  let := hd
  let enc : ∀ T : Scheme.{u}, Encoding l E n T := fun T ↦
    (FiniteDiscreteOrdinary.encoding_exists (R l E n) T).some
  have hcalc := local_calculation l E V M n enc
  obtain ⟨hv, hc, ho⟩ := cohomology_descent l E V M hM n inferInstance hd enc hcalc
  have hb := bounded_from_vanishing (reduction l E V M n) hv
  refine ⟨inferInstance, hd, hv, ⟨hb, hc⟩, enc, ?_, hcalc⟩
  let F := (enc V).ordinary.functor ⋙ (enc V).fixed.functor
  exact ⟨F.bounded_mapDerivedCategory_obj hb, ho⟩

end AlgebraicGeometry.ProEtale.FiniteModelQuotient
