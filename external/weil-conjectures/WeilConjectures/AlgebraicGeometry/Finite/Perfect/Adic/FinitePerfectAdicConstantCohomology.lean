/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleLevelData
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleUniversalNormalization
import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction

/-! # The constant half of the finite perfect normalization diagram

Source: Stacks Project, Tags 09C6, 06YY and 093J.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Coefficient transport along the lifted ring equivalence is an equivalence.
Source: Stacks Tag 05RU.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
instance finitePerfectAdicLiftRestrictEquivalence (B : Type t) [CommRing B] :
    (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).IsEquivalence :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t + 1}
    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B)).isEquivalence_functor

/-- Coefficient transport along the lifted ring equivalence preserves limits.
Source: Stacks Tag 05RU.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
instance finitePerfectAdicLiftRestrictLimits (B : Type t) [CommRing B] :
    PreservesLimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
  Adjunction.isEquivalencePreservesLimits _

/-- Coefficient transport along the lifted ring equivalence preserves colimits.
Source: Stacks Tag 05RU.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
instance finitePerfectAdicLiftRestrictColimits (B : Type t) [CommRing B] :
    PreservesColimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
  Adjunction.isEquivalence_preservesColimits _

/-- The coefficient-universe lift commutes with restriction of scalars.
Source: Stacks Tag 05RU; both termwise functors have the identical lifted action.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
def finitePerfectAdicAlgebraLiftRestrict {B D : Type t} [CommRing B] [CommRing D]
    (q : B →+* D) :
    finitePerfectAdicAlgebraLift D ⋙ normalizationModuleRestrict (RingHom.ulift q) ≅
      (ModuleCat.restrictScalars.{t} q).mapDerivedCategory ⋙
        finitePerfectAdicAlgebraLift B := by
  let L (R : Type t) [CommRing R] := ModuleCat.uliftFunctor.{t + 1, t} R ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} R ≃+* R).toRingHom
  let e : ModuleCat.restrictScalars.{t} q ⋙ L B ≅
      L D ⋙ ModuleCat.restrictScalars.{t + 1} (RingHom.ulift q) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  exact (Functor.mapDerivedCategorySquareIso e).symm

/-- Lift the specified algebraic transition, using the coefficient interchange.
Source: Stacks Tag 09C6, the arrows of the normalized algebraic diagram.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
def finitePerfectAdicLiftedTransition {A : Type t} [CommRing A]
    {d : AdicCoefficientDatum A} (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :
    (finitePerfectAdicAlgebraLift _).obj (T.level (n + 1)) ⟶
      (normalizationModuleRestrict
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj
          ((finitePerfectAdicAlgebraLift _).obj (T.level n)) :=
  (finitePerfectAdicAlgebraLift _).map (T.transition n) ≫
    (finitePerfectAdicAlgebraLiftRestrict
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).inv.app (T.level n)

/-- The actual constant etale model of an algebraic level.
Source: Stacks Tags 09C6 and 093J.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
def finitePerfectAdicEtaleConstant (Y : Scheme.{t}) {A : Type t} [CommRing A]
    {d : AdicCoefficientDatum A} (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :=
  (normalizationConstant Y.smallEtaleTopology).obj
    ((finitePerfectAdicAlgebraLift _).obj (T.level n))

/-- The specified normalization arrow between the constant etale models.
Source: Stacks Tags 09C6 and 06YY.
(blueprint: def-weil-pbc-finite-perfect-adic-constant-normalization). -/
def finitePerfectAdicEtaleConstantTransition (Y : Scheme.{t})
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :=
  normalizationConstantArrow Y.smallEtaleTopology _ (finitePerfectAdicLiftedTransition T n)

/-- Constant realization of a perfect algebraic level is bounded with finite lisse
cohomology. This uses only the perfect level, and no actual quotient or marking.
Source: Stacks Tags 093J and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-constant-cohomology).
Proof: perfectness bounds algebraic cohomology. Exact universe lift and constants
preserve these bounds and commute with cohomology. The algebraic cohomology is finite
over the finite quotient ring; its lifted constant sheaf is finite locally constant. -/
theorem finitePerfectAdicEtaleConstant_cohomology (Y : Scheme.{t})
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ)
    (hp : DerivedCategory.IsPerfect (T.level n)) :
    (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero
      ((DerivedCategory.homologyFunctor _ i).obj (finitePerfectAdicEtaleConstant Y T n))) ∧
    (∀ i : ℤ, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor _ i).obj (finitePerfectAdicEtaleConstant Y T n))) := by
  let B := A ⧸ d.ideal ^ (n + 1)
  let : Finite B := d.quotientFinite n
  let L := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
  let F := constantSheaf Y.smallEtaleTopology (ModuleCat.{t + 1} (ULift.{t + 1} B))
  constructor
  · obtain ⟨a, b, ha, hb⟩ := hp.exists_homologyConcentratedIn
    refine ⟨a, b, fun i hi ↦ ?_⟩
    have hz : IsZero ((DerivedCategory.homologyFunctor _ i).obj (T.level n)) := by
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff _ a).mp ha i hi
      · exact (DerivedCategory.isLE_iff _ b).mp hb i hi
    exact F.isZero_homologyFunctor_mapDerivedCategory_obj
      (L.isZero_homologyFunctor_mapDerivedCategory_obj hz)
  · intro i
    let H := (DerivedCategory.homologyFunctor _ i).obj (T.level n)
    let : Module.Finite B H := hp.finite_homology i
    let : Finite H := Module.finite_of_finite B
    let : Finite (L.obj H) := by
      change Finite (ULift.{t + 1} H)
      infer_instance
    let : Module.Finite (ULift.{t + 1} B) (L.obj H) := Module.Finite.of_finite
    have e : F.obj (L.obj H) ≅
        (DerivedCategory.homologyFunctor _ i).obj (finitePerfectAdicEtaleConstant Y T n) :=
      F.mapIso ((L.mapDerivedCategoryHomologyFunctorIso i).app (T.level n)) ≪≫
        (F.mapDerivedCategoryHomologyFunctorIso i).app
          ((finitePerfectAdicAlgebraLift B).obj (T.level n))
    exact IsFiniteLocallyConstantSheaf.of_iso e

end AlgebraicGeometry.Scheme
