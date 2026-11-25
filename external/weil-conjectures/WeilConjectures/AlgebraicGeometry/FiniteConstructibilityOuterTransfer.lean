/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteResidueNormalization
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteScalarBoundedTransport
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteScalarLocalTransport
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import all WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude

/-! Scalar restriction for the finite integral coefficient triangle. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

/-- Finite constant local models on one fixed stratum, in a form independent of the
finite quotient presentation. -/
def scalarFiniteLocalModelsOnStratum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (S : Scheme.Stratification X) (i : Fin S.n)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) : Prop :=
  ∀ q : ℤ, HasFiniteConstantLocalModel Λ (S.domain i)
    ((CondensedRing.upperStar Λ (S.immersion i)).obj
      ((DerivedCategory.homologyFunctor _ q).obj L))

private theorem scalarLocal_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (S : Scheme.Stratification X) (i : Fin S.n)
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (e : K ≅ L)
    (h : scalarFiniteLocalModelsOnStratum Λ X S i K) :
    scalarFiniteLocalModelsOnStratum Λ X S i L := by
  intro q
  obtain ⟨C, hC⟩ := h q
  refine ⟨C, fun j ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC j
  let F := CondensedRing.upperStar Λ (S.immersion i) ⋙
    CondensedRing.upperStar Λ (C.f j)
  exact ⟨P, hP, ⟨F.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso e.symm) ≪≫ eP⟩⟩

private theorem scalarLocal_transport
    (A B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [Finite A] [Finite B] [DiscreteTopology A] [DiscreteTopology B]
    (a : A →+* B)
    (ρ : FiniteDiscreteOrdinary.coefficient A ⟶ FiniteDiscreteOrdinary.coefficient B)
    [IsMonHom ρ]
    (hρ : FiniteDiscreteOrdinary.pointConstants A ≫ ρ.hom =
      (Functor.const Profinite.{u}ᵒᵖ).map
        (AddCommGrpCat.ofHom a.ulift.{u + 1, u + 1}.toAddMonoidHom) ≫
          FiniteDiscreteOrdinary.pointConstants B)
    (X : Scheme.{u}) [IsNoetherian X] (S : Scheme.Stratification X) (i : Fin S.n)
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal B X))
    (hK : scalarFiniteLocalModelsOnStratum (FiniteDiscreteOrdinary.coefficient B) X S i K) :
    scalarFiniteLocalModelsOnStratum (FiniteDiscreteOrdinary.coefficient A) X S i
      ((Mod.comap ((upperStarFromPoint X).map ρ)).mapDerivedCategory.obj K) :=
  FiniteDiscreteOrdinary.finite_scalar_local_transport A B a ρ hρ X S i K hK

private theorem native_transition_bounded
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (n : ℕ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n)))
    (hK : constantModelBoundedConstructible
      (DerivedNakayama.quotientRing l E (n + 1)) X K) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 2)) X
      ((Mod.comap (AdicCompletion.transition l E X n)).mapDerivedCategory.obj K) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : Finite (Padic.coefficientExtensionRing l E (n + 2)) :=
    Padic.finite_coefficientExtensionRing l E (n + 2) (by omega)
  let := DerivedNakayama.quotientDiscrete l E (n + 1)
  let := DerivedNakayama.quotientDiscrete l E (n + 2)
  apply FiniteDiscreteOrdinary.finite_scalar_bounded_transport
    (Padic.coefficientExtensionRing l E (n + 2))
    (Padic.coefficientExtensionRing l E (n + 1))
    (Padic.coefficientExtensionTransition l E (n + 1))
    (AdicCompletion.transitionRing l E n) ?_ X K hK
  ext U r
  rfl

private theorem native_transition_local
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (n : ℕ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n)))
    (S : Scheme.Stratification X) (i : Fin S.n)
    (hK : scalarFiniteLocalModelsOnStratum
      (DerivedNakayama.quotientRing l E (n + 1)) X S i K) :
    scalarFiniteLocalModelsOnStratum (DerivedNakayama.quotientRing l E (n + 2)) X S i
      ((Mod.comap (AdicCompletion.transition l E X n)).mapDerivedCategory.obj K) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : Finite (Padic.coefficientExtensionRing l E (n + 2)) :=
    Padic.finite_coefficientExtensionRing l E (n + 2) (by omega)
  let := DerivedNakayama.quotientDiscrete l E (n + 1)
  let := DerivedNakayama.quotientDiscrete l E (n + 2)
  exact scalarLocal_transport
    (Padic.coefficientExtensionRing l E (n + 2))
    (Padic.coefficientExtensionRing l E (n + 1))
    (Padic.coefficientExtensionTransition l E (n + 1))
    (AdicCompletion.transitionRing l E n) (by ext U r; rfl) X S i K hK

private theorem native_residue_bounded
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (n : ℕ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X 0)))
    (hK : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X K) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X
      ((Mod.comap (integralResidueTransition l E X n)).mapDerivedCategory.obj K) := by
  induction n with
  | zero =>
    let e := Functor.mapDerivedCategoryNatIso
      (Mod.comapId (AdicCompletion.finiteRing l E X 0)) ≪≫
      Functor.mapDerivedCategoryIdIso _
    have := (constantModelConstructibleFiniteTor_wellDefined
      (DerivedNakayama.quotientRing l E 1) X).2.1
    exact ObjectProperty.prop_of_iso _ (e.app K).symm hK
  | succ n ih =>
    have h := native_transition_bounded l E X n _ ih
    let e := Mod.mapDerivedCategoryComapCompIso (AdicCompletion.transition l E X n)
      (integralResidueTransition l E X n) (integralResidueTransition l E X (n + 1)) rfl
    have := (constantModelConstructibleFiniteTor_wellDefined
      (DerivedNakayama.quotientRing l E (n + 2)) X).2.1
    exact ObjectProperty.prop_of_iso _ (e.app K) h

private theorem native_residue_local
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (n : ℕ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X 0)))
    (S : Scheme.Stratification X) (i : Fin S.n)
    (hK : scalarFiniteLocalModelsOnStratum
      (DerivedNakayama.quotientRing l E 1) X S i K) :
    scalarFiniteLocalModelsOnStratum (DerivedNakayama.quotientRing l E (n + 1)) X S i
      ((Mod.comap (integralResidueTransition l E X n)).mapDerivedCategory.obj K) := by
  induction n with
  | zero =>
    let e := Functor.mapDerivedCategoryNatIso
      (Mod.comapId (AdicCompletion.finiteRing l E X 0)) ≪≫
      Functor.mapDerivedCategoryIdIso _
    exact scalarLocal_of_iso _ X S i (e.app K).symm hK
  | succ n ih =>
    have h := native_transition_local l E X n _ S i ih
    let e := Mod.mapDerivedCategoryComapCompIso (AdicCompletion.transition l E X n)
      (integralResidueTransition l E X n) (integralResidueTransition l E X (n + 1)) rfl
    exact scalarLocal_of_iso _ X S i (e.app K) h

private theorem finite_bounded_triangle
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A] (X : Scheme.{u}) [IsNoetherian X]
    (Δ : CategoryTheory.Pretriangulated.Triangle
      (DerivedCategory (FiniteDiscreteOrdinary.Internal A X))) (hΔ : Δ ∈ distTriang _)
    (h₁ : constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X Δ.obj₁)
    (h₃ : constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X Δ.obj₃) :
    constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X Δ.obj₂ := by
  obtain ⟨e, he⟩ := FiniteDiscreteOrdinary.finiteCoefficientModelComparison A X
  let P := FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X
  have hP : P = fun K : Scheme.proEtaleDerivedCategory X A ↦
      Set.Finite {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ q).obj K)} ∧
        ∀ q : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf X A
          ((DerivedCategory.homologyFunctor _ q).obj K) := by
    funext K
    apply propext
    exact and_congr (Scheme.finite_homology_support_iff_bounded X A K).symm Iff.rfl
  have : P.IsClosedUnderIsomorphisms := by
    rw [hP]
    exact (Scheme.proEtale_bounded_constructible_isTriangulated X A).1
  have : P.IsTriangulated := by
    rw [hP]
    exact (Scheme.proEtale_bounded_constructible_isTriangulated X A).2
  apply (he.boundedConstructible Δ.obj₂).mpr
  let F := e.ordinary.functor.mapDerivedCategory
  exact P.ext_of_isTriangulatedClosed₂ (F.mapTriangle.obj Δ)
    (F.map_distinguished Δ hΔ)
    ((he.boundedConstructible Δ.obj₁).mp h₁) ((he.boundedConstructible Δ.obj₃).mp h₃)

/-- The middle vertex of the native quotient-linear distinguished triangle is bounded
constructible when both original outer complexes are.
Source: blueprint latest, integral-finite-levels, first paragraph.
(blueprint: lem-pe-finite-constructibility-outer-transfer).

Proof: positive native quotients are finite and discrete. Their consecutive transition
maps commute with pointwise constant sections, so normalized finite scalar restriction
preserves bounded constructibility. Iterate this assertion for the residue composite,
using the exact derived restriction-composition isomorphism. Transport across the two
given outer isomorphisms. Encode the resulting distinguished triangle as ordinary
constant-ring modules; bounded constructible cohomology is a triangulated property there.
Its middle-term closure and the inverse coefficient comparison give the conclusion. -/
theorem finite_constructibility_outer_transfer
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (n : ℕ)
    (L₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X 0)))
    (Lₙ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n)))
    (Δ : CategoryTheory.Pretriangulated.Triangle
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X (n + 1)))))
    (hΔ : Δ ∈ distTriang _)
    (e₀ : Δ.obj₁ ≅
      (Mod.comap (integralResidueTransition l E X (n + 1))).mapDerivedCategory.obj L₀)
    (eₙ : Δ.obj₃ ≅
      (Mod.comap (AdicCompletion.transition l E X n)).mapDerivedCategory.obj Lₙ)
    (h₀ : constantModelBoundedConstructible
      (DerivedNakayama.quotientRing l E 1) X L₀)
    (hₙ : constantModelBoundedConstructible
      (DerivedNakayama.quotientRing l E (n + 1)) X Lₙ) :
    constantModelBoundedConstructible
      (DerivedNakayama.quotientRing l E (n + 2)) X Δ.obj₂ := by
  have h₁ := native_residue_bounded l E X (n + 1) L₀ h₀
  have h₃ := native_transition_bounded l E X n Lₙ hₙ
  have := (constantModelConstructibleFiniteTor_wellDefined
    (DerivedNakayama.quotientRing l E (n + 2)) X).2.1
  have h₁' := ObjectProperty.prop_of_iso _ e₀.symm h₁
  have h₃' := ObjectProperty.prop_of_iso _ eₙ.symm h₃
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : Finite (Padic.coefficientExtensionRing l E (n + 2)) :=
    Padic.finite_coefficientExtensionRing l E (n + 2) (by omega)
  let := DerivedNakayama.quotientDiscrete l E (n + 2)
  exact finite_bounded_triangle (Padic.coefficientExtensionRing l E (n + 2))
    X Δ hΔ h₁' h₃'

end AlgebraicGeometry.ProEtale
