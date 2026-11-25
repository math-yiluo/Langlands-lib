/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.FiniteRealization.DiagonalRootRouteInsertions
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalRootLimitCompatibility
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteRootCoefficientComparison

/-! # The ordinary coefficient square on root insertions

Source: diagonal tower coefficient changes (1), root projection normalizations.
(blueprint: lem-diagonal-ordinary-root-route-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
attribute [local instance] UniformizerSquareData.inverse_additive
attribute [local irreducible] spIntegralTwist
attribute [local irreducible] derivedScalars quotientLine cyclicLine
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors HasDerivedCategory.standard
  geoCartierLine UniformizerSquareData.cyclicRootInsertion
  UniformizerSquareData.quotientRootInsertion FiniteRealization.rootInsertion

private def inverseUnderlyingNatIso
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X) :
    e.F.asEquivalence.inverse ⋙ Mod.forget _ ≅
      sheafCompose (Scheme.ProEt.topology X) (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1}) :=
  (Functor.isoWhiskerLeft e.F.asEquivalence.inverse e.underlying).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e.F.asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _

private theorem inverseUnderlyingNatIso_app
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
    (inverseUnderlyingNatIso e).app M = UniformizerSquareData.inverseUnderlying e M := by
  apply Iso.ext
  apply Sheaf.hom_ext
  ext V x
  rfl

private theorem inverseUnderlying_naturality
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X)
    {M N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)} (f : M ⟶ N) :
    (e.F.asEquivalence.inverse.map f).hom ≫
      (UniformizerSquareData.inverseUnderlying e N).hom =
    (UniformizerSquareData.inverseUnderlying e M).hom ≫
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} B) Ab.{u + 1})).map f := by
  have h := (inverseUnderlyingNatIso e).hom.naturality f
  have hm := congrArg Iso.hom (inverseUnderlyingNatIso_app e M)
  have hn := congrArg Iso.hom (inverseUnderlyingNatIso_app e N)
  change (e.F.asEquivalence.inverse.map f).hom ≫ (inverseUnderlyingNatIso e).hom.app N =
    (inverseUnderlyingNatIso e).hom.app M ≫ _ at h
  exact (congrArg₂ (· ≫ ·) rfl hn.symm).trans
    (h.trans (congrArg₂ (· ≫ ·) hm rfl))

private theorem root_square
    {C : Type*} [Category C] {U B I Q CR RA RR RCA TA TR F : C}
    (r : U ⟶ B) [Epi r] (t : U ⟶ I) (i : B ⟶ I) (p : I ⟶ Q) (c : B ⟶ CR)
    (u : B ⟶ RA) (v : B ⟶ RR) (a : Q ⟶ RA) (b : CR ⟶ RR)
    (vA : RA ≅ TA) (vR : RR ≅ TR) (vRA : RCA ≅ TA)
    (s : RA ⟶ RCA) (f : RR ⟶ RCA) (m : TR ⟶ TA)
    (a₀ : Q ⟶ TA) (b₀ : CR ⟶ TR)
    (k : U ⟶ F) (gA : F ⟶ TA) (gR : F ⟶ TR)
    (hu : u = i ≫ p ≫ a) (hv : v = c ≫ b)
    (hs : s = vA.hom ≫ vRA.inv) (hn : f ≫ vRA.hom = vR.hom ≫ m)
    (ht : r ≫ i = t) (ha₀ : a ≫ vA.hom = a₀) (hb₀ : b ≫ vR.hom = b₀)
    (ha : (t ≫ p) ≫ a₀ = k ≫ gA) (hb : (r ≫ c) ≫ b₀ = k ≫ gR)
    (hg : gR ≫ m = gA) : u ≫ s = v ≫ f := by
  apply (cancel_epi r).mp
  apply (cancel_mono vRA.hom).mp
  calc
    (r ≫ (u ≫ s)) ≫ vRA.hom = (t ≫ p) ≫ a₀ := by
      simp only [hu, hs, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [ha₀, ← Category.assoc r i, ht]
    _ = k ≫ gA := ha
    _ = (k ≫ gR) ≫ m := by rw [Category.assoc, hg]
    _ = ((r ≫ c) ≫ b₀) ≫ m := congrArg (· ≫ m) hb.symm
    _ = (r ≫ (v ≫ f)) ≫ vRA.hom := by
      simp only [hv, Category.assoc, hn]
      rw [reassoc_of% hb₀]

/-- The ordinary root insertion square follows from the supplied finite normalizations.

Source: latest blueprint, diagonal tower coefficient changes (1), root projections.
(blueprint: lem-diagonal-ordinary-root-route-square).

Proof: forget to abelian sheaves, compose with the inverse-realization underlying
isomorphism and precompose with the invertible bottom IntegralRoots map. The
normalization of s cancels the cyclic inverse-realization factors. Naturality of the
inverse underlying comparison moves the supplied line map outside the realization.
The finite-equivalence triangle identity replaces each root insertion by the original
realized root map. The bottom-to-E transition preserves the root-limit map, so both
LineEndpoint normalizations apply to the same root limit. The resulting maps are the
n-th root projection followed by the two finite-root arrows; coefficient normalization
makes them equal. Cancel the two isomorphisms and use faithful module forgetting. -/
theorem diagonalOrdinaryRootRouteSquare
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA)
    (s : q.quotientRight ≅ q.restriction ⋙ q.cyclicRight)
    (hs : q.RestrictionNormalized s) :
    q.quotientRootInsertion ≫ s.hom.app _ =
      q.cyclicRootInsertion ≫ q.cyclicRight.map q.lineMap := by
  let X := diagonalSurface Y
  let NR := geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
    (cartierResidue_cast l (n + 1)) X
  let NA := geoCartierLine A (l ^ (n + 1)) hA X
  let UR := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})
  let UA := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})
  let vR := UniformizerSquareData.inverseUnderlying q.cyclic.eW NR
  let vA := UniformizerSquareData.inverseUnderlying q.eW NA
  let vRA := UniformizerSquareData.inverseUnderlying q.cyclic.eW (q.restriction.obj NA)
  let r := q.cyclic.integralRoots
  have : IsIso r.hom := diagonalBottomIntegralRoots_isIso l X r
  have hq : q.quotientRootInsertion.hom = integralLineMap l E X ≫
      quotientLineMap l E π n X ≫ (q.eW.rootInsertion _ q.lineW.endpoint.iso).hom := by
    unfold UniformizerSquareData.quotientRootInsertion
    change q.route.first.lineW.semilinear.hom.hom ≫
      (q.route.second.lineW.semilinear.hom.hom ≫ _) = _
    exact congrArg₂ (· ≫ ·) q.route.first.lineW.semilinear.underlying
      (congrArg (· ≫ (q.eW.rootInsertion _ q.lineW.endpoint.iso).hom)
        q.route.second.lineW.semilinear.underlying)
  have hc : q.cyclicRootInsertion.hom = cyclicLineMap l n X ≫
      (q.cyclic.eW.rootInsertion _ q.cyclic.lineEndpoint.iso).hom := by
    unfold UniformizerSquareData.cyclicRootInsertion
    change q.cyclic.line.semilinear.hom.hom ≫ _ = _
    exact congrArg (· ≫ (q.cyclic.eW.rootInsertion _ q.cyclic.lineEndpoint.iso).hom)
      q.cyclic.line.semilinear.underlying
  have hn := inverseUnderlying_naturality q.cyclic.eW q.lineMap
  change (q.cyclicRight.map q.lineMap).hom ≫ vRA.hom = vR.hom ≫ UR.map q.lineMap at hn
  have hsA := hs NA
  change (s.hom.app NA).hom = vA.hom ≫ vRA.inv at hsA
  have ha := q.lineW.endpoint.normalization
  change (q.lineW.integralRoots.hom ≫ quotientLineMap l E π n X) ≫
    q.eW.underlying.inv.app _ ≫ UA.map q.lineW.endpoint.iso.hom = _ at ha
  have hr := q.cyclic.lineEndpoint.normalization
  change (r.hom ≫ cyclicLineMap l n X) ≫ q.cyclic.eW.underlying.inv.app _ ≫
    UR.map q.cyclic.lineEndpoint.iso.hom = _ at hr
  apply Mod.hom_ext
  exact root_square r.hom q.lineW.integralRoots.hom (integralLineMap l E X)
    (quotientLineMap l E π n X) (cyclicLineMap l n X)
    q.quotientRootInsertion.hom q.cyclicRootInsertion.hom
    (q.eW.rootInsertion _ q.lineW.endpoint.iso).hom
    (q.cyclic.eW.rootInsertion _ q.cyclic.lineEndpoint.iso).hom
    vA vR vRA (s.hom.app NA).hom (q.cyclicRight.map q.lineMap).hom (UR.map q.lineMap)
    (q.eW.underlying.inv.app _ ≫ UA.map q.lineW.endpoint.iso.hom)
    (q.cyclic.eW.underlying.inv.app _ ≫ UR.map q.cyclic.lineEndpoint.iso.hom)
    (limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n))
    (q.lineW.finiteRoots.toLine A hA)
    (q.cyclic.finiteRoots.toLine (diagonalResidue.{u} l n) (cartierResidue_cast l (n + 1)))
    hq hc hsA hn (diagonalIntegralRoots_transition l X E r q.lineW.integralRoots)
    (FiniteRealization.rootInsertion_underlying q.eW _ q.lineW.endpoint.iso)
    (FiniteRealization.rootInsertion_underlying q.cyclic.eW _ q.cyclic.lineEndpoint.iso)
    ha hr (finiteRoots_toLine_scalar q.maps q.cyclic.finiteRoots q.lineW.finiteRoots)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
