/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteSquare
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalOrdinaryRootRouteSquare
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicTargetTranspose
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Quotient.DiagonalQuotientTargetTranspose
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalShiftedRootInsertionComparison

/-! # The positive-root endpoint of cyclic coefficient continuation

Source: diagonal tower coefficient changes (1), root projections and tensor units.
(blueprint: lem-diagonal-cyclic-uniformizer-target).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

attribute [local irreducible] derivedScalars quotientLine cyclicLine
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors HasDerivedCategory.standard
  DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory.singleFunctorIsoCompQ
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf spIntegralTwist geoCartierLine
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  UniformizerSquareData.inverse_additive

attribute [local semireducible] UniformizerSquareData.comparison

private theorem restrictionMate_transpose
    {C D K : Type*} [Category C] [Category D] [Category K]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C ⥤ K} {R' : K ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (H : K ⥤ D) (s : R' ≅ H ⋙ R)
    (X : C) {Y : K} (f : L'.obj X ⟶ Y) :
    a.homEquiv _ _ ((UniformizerSquareData.restrictionMate a b H s).app X ≫ H.map f) =
      b.homEquiv _ _ f ≫ s.hom.app Y := by
  rw [Adjunction.homEquiv_naturality_right]
  unfold UniformizerSquareData.restrictionMate
  change a.homEquiv _ _ ((a.homEquiv _ _).symm
      (b.unit.app X ≫ s.hom.app (L'.obj X))) ≫ R.map (H.map f) = _
  rw [Equiv.apply_symm_apply, Category.assoc]
  have hn := s.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← hn, b.homEquiv_unit X Y f, Category.assoc]

private theorem restrictionMate_endpoint
    {C D K : Type*} [Category C] [Category D] [Category K]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C ⥤ K} {R' : K ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (H : K ⥤ D) (s : R' ≅ H ⋙ R)
    (X : C) {Y : K} {Z Z' : D} (f : L'.obj X ⟶ Y) (g : L.obj X ⟶ Z)
    (k : H.obj Y ⟶ Z') (h : Z ⟶ Z')
    (v : X ⟶ R'.obj Y) (w : X ⟶ R.obj Z)
    (hf : b.homEquiv _ _ f = v) (hg : a.homEquiv _ _ g = w)
    (hh : v ≫ s.hom.app Y ≫ R.map k = w ≫ R.map h) :
    (UniformizerSquareData.restrictionMate a b H s).app X ≫ H.map f ≫ k = g ≫ h := by
  have ht := restrictionMate_transpose a b H s X f
  rw [Adjunction.homEquiv_naturality_right] at ht
  apply (a.homEquiv _ _).injective
  rw [← Category.assoc]
  simp only [Adjunction.homEquiv_naturality_right]
  rw [ht, hf, hg]
  simpa only [Category.assoc] using hh

-- Read the endpoint predicate from the proved criterion's stored type.
-- The emitted signature is its ordinary quantified endpoint formula.
local elab "criterionHypothesis% " i:num f:term:max : term => do
  let e ← Lean.Elab.Term.elabTerm f none
  let mut t ← Lean.Meta.inferType e
  for _ in [:i.getNat] do
    let .forallE _ _ body _ ← Lean.Meta.whnf t
      | throwError "criterion has fewer proof arguments"
    t := body
  let .forallE _ domain _ _ ← Lean.Meta.whnf t
    | throwError "criterion has fewer proof arguments"
  if domain.hasLooseBVars then
    throwError "endpoint predicate depends on an earlier proof"
  return domain

/-- The mate of any underlying-identity restriction comparison has the prescribed
positive-root endpoint. No constant-source or diagonal-class equation is assumed.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md (1), root projection and derived
scalar transitivity; parent coefficient-square proof, step 2.
(blueprint: lem-diagonal-cyclic-uniformizer-target).

Proof: transpose the two target maps through the actual scalar adjunctions.
Endpoint.normalization identifies their transposes with the single of the
prescribed semilinear maps. On underlying sheaves, the normalization of the
restriction comparison cancels the inverse realization counits. IntegralRoots
projections identify integralLineMap with the bottom-to-E transition on every
finite root projection. The scalar extension units and the two LineEndpoint
normalizations therefore identify both maps on pure root tensors with the n-th
root projection followed by coefficient extension. FiniteRoots comparisons
coincide since their composites with the monic kernel inclusion coincide.
The supplied line_normalization identifies coefficient extension on these root
tensors with maps.line. At the bottom field, each coefficient-root module is the root sheaf itself:
free extension over Z/l^(r+1) is an isomorphism on an l^(r+1)-torsion sheaf.
Consequently the bottom IntegralRoots map is an isomorphism, by the limit
universal property. Precomposing the bottom-to-E transition with this map gives
the E-root map, since every projection agrees. Thus it suffices to compare the
two transposed arrows on this bottom root sheaf. The finite root calculation
and balanced-tensor unit equations above give exactly that comparison.
The derived adjunction is compatible with shifts; naturality of the exact single
and shift comparisons translates the transposed equality to TargetEquation.
Adjunction injectivity completes the proof. No property of the initial arrow,
no finite evaluation detection of arbitrary derived morphisms, and no flatness
of A over the cyclic ring is needed. The same tensor calculation includes n=0,
the empty base, and the zero target ring. -/
private theorem diagonalCyclic_uniformizerTarget_proof
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :
    criterionHypothesis% 1 (UniformizerSquareData.endpointSquare l Y E π n A hA q) := by
  intro s hs
  let M := ((DerivedCategory.singleFunctor
    (Modules (Profinite.continuousMapRingObj ℤ_[l]) (diagonalSurface Y)) 0).obj
      (zlLine l (diagonalSurface Y)))⟦(2 : ℤ)⟧
  have hf : q.quotientAdjunction.homEquiv M _ q.quotientTarget =
      shiftedRootInsertion q.quotientRight q.quotientRootInsertion :=
    diagonalQuotientTargetTranspose l Y E π n A hA q
  have hg : q.cyclicAdjunction.homEquiv M _ q.cyclicTarget =
      shiftedRootInsertion q.cyclicRight q.cyclicRootInsertion :=
    diagonalCyclicTargetTranspose l Y E π n A hA q
  have hh := shiftedRootInsertion_comparison q.quotientRight q.cyclicRight q.restriction s
      q.quotientRootInsertion q.cyclicRootInsertion q.lineMap
      (diagonalOrdinaryRootRouteSquare l Y E π n A hA q s hs)
  refine restrictionMate_endpoint
    (a := q.cyclicAdjunction) (b := q.quotientAdjunction)
    (H := q.restriction.mapDerivedCategory)
    (s := Functor.mapDerivedCategoryNatIso s ≪≫
      (Functor.mapDerivedCategoryCompIso q.restriction q.cyclicRight).symm)
    (X := M) (f := q.quotientTarget) (g := q.cyclicTarget)
    (v := shiftedRootInsertion q.quotientRight q.quotientRootInsertion)
    (w := shiftedRootInsertion q.cyclicRight q.cyclicRootInsertion)
    (hf := hf) (hg := hg) (hh := hh)

theorem diagonalCyclic_uniformizerTarget
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :
    criterionHypothesis% 1 (UniformizerSquareData.endpointSquare l Y E π n A hA q)
      := diagonalCyclic_uniformizerTarget_proof l Y E π n A hA q

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
