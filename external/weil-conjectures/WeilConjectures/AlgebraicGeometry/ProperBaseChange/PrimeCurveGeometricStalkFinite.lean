/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricFiberFinite
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
/-!
# Finite geometric stalks for prime coefficients on smooth proper curves

## References

* Stacks Project, Tag 0GKV, case (a), finite-stalk paragraph
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
private theorem constant_curve_cohomology_finite
    {R : Type (u + 1)} [CommRing R] [Finite R]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [Smooth f] [ConnectedSpace X] [IsProper f]
    (ell : ℕ) [Fact ell.Prime] (hp : (ell : R) = 0) (q : ℕ) :
    Finite ((cohomology (ModuleCat.{u + 1} R) X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology _).obj
          (ModuleCat.of R R)))) := by
  let M := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R)
  have hi : (Ideal.span {(ell : R)} : Ideal R) = ⊥ := by rw [hp, Ideal.span_singleton_zero]
  have : Finite (R ⧸ (Ideal.span {(ell : R)} : Ideal R)) := by
    rw [hi]
    exact Finite.of_equiv R (RingEquiv.quotientBot R).toEquiv.symm
  have hfinite := IsCurve.finite_sheafH_constantModSheaf_of_isProper R f ell q
  let b : (R ⧸ (Ideal.span {(ell : R)} : Ideal R)) ≃ₐ[R] R :=
    (Ideal.quotientEquivAlgOfEq R hi).trans (AlgEquiv.quotientBot R R)
  let e : constantModSheaf R X ell ≅ M :=
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).mapIso
      b.toLinearEquiv.toModuleIso
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
  have : Finite ((Sheaf.functorH.{u + 1} X.smallEtaleTopology q).obj
      (U.obj (constantModSheaf R X ell))) := hfinite
  let eH := (Sheaf.functorH.{u + 1} X.smallEtaleTopology q).mapIso (U.mapIso e)
  have : Finite (Sheaf.H (U.obj M) q) :=
    Finite.of_equiv _ eH.addCommGroupIsoToAddEquiv.toEquiv
  have : Finite ((Sheaf.functorH.{u + 1} X.smallEtaleTopology q).obj (U.obj M)) :=
    show Finite (Sheaf.H (U.obj M) q) from inferInstance
  obtain ⟨ec⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso X R q
  obtain ⟨eh⟩ := Scheme.nonempty_sheafH_extDerivedIso X q
  let E := (ec.app M) ≪≫ (eh.app (U.obj M)).symm
  exact Finite.of_equiv _ E.addCommGroupIsoToAddEquiv.toEquiv.symm
/-- The geometric stalks of every nonnegative prime-coefficient higher direct image
are finite, including at points of residue characteristic equal to the prime. -/
theorem prime_constant_stalk_finite
    {C S : Scheme.{u}} (f : C ⟶ S) [Smooth f] [IsProper f]
    [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1)
    (ell : ℕ) [Fact ell.Prime] (q : ℕ)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    Finite (((Scheme.pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj
      (higherDirectImage (ULift.{u + 1} (ZMod ell)) f q
        ((constantSheaf C.smallEtaleTopology _).obj
          (ModuleCat.of (ULift.{u + 1} (ZMod ell)) (ULift.{u + 1} (ZMod ell)))))) := by
  let R := ULift.{u + 1} (ZMod ell)
  let M := (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R)
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : Scheme.IsFiniteSheaf M := by
    constructor
    intro Ξ _ _ t
    let e := (Scheme.pointSmallEtale t).sheafFiberConstantSheafIso (ModuleCat.of R R)
    have : Finite (((Scheme.pointSmallEtale t).sheafFiber
        (A := ModuleCat.{u + 1} R)).obj M) :=
      Finite.of_equiv R e.toLinearEquiv.toEquiv.symm
    exact (ModuleCat.isFinitelyGenerated_iff _).mpr (Module.Finite.of_finite (R := R))
  have : GeometricallyIrreducible f :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected f
  have : SmoothOfRelativeDimension 1 f :=
    smoothOfRelativeDimension_of_fiberToSpecResidueField f 1 fun t ↦ by
      have : Smooth (f.fiberToSpecResidueField t) :=
        inferInstanceAs (Smooth (pullback.snd _ _))
      have : IrreducibleSpace (f.fiber t) := inferInstance
      exact (smoothOfRelativeDimension_iff_topologicalKrullDim_eq
        (f.fiberToSpecResidueField t) 1).mpr (hdim t)
  have : ConnectedSpace (pullback f s : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := pullback.snd f s)
  have : IsCurve (pullback.snd f s) :=
    { krullDim_le_one := le_of_eq
        (topologicalKrullDim_eq_of_smoothOfRelativeDimension (pullback.snd f s) 1) }
  have hfinite := constant_curve_cohomology_finite (R := R)
    (pullback.snd f s) ell (CharP.cast_eq_zero R ell) q
  let e := (cohomology (ModuleCat.{u + 1} R) (pullback f s) q).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} R) (pullback.fst f s)).app
        (ModuleCat.of R R)))
  have : Finite ((cohomology (ModuleCat.{u + 1} R) (pullback f s) q).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} R) (pullback.fst f s)).obj M))) :=
    Finite.of_equiv _ e.toLinearEquiv.toEquiv.symm
  obtain ⟨a, b, hab⟩ := geometricFiber_finite_stalk_formula R f Ω s M q
  exact Finite.of_equiv _ (asIso (a.inv ≫
    (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} R)).map
      (baseChangeHomologyMap R (IsPullback.of_hasPullback f s) q M) ≫
        b.hom)).toLinearEquiv.toEquiv.symm
end AlgebraicGeometry.Etale
