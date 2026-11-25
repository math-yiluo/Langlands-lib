/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift

import WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.Curve.IntegralOpenExtensionComparison
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# DenseOpenFinitenessComparison

Source: Stacks Project, Lemma 0GJA.
(blueprint: lem-pbc-j2-dense-open-finiteness-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem invertibleOrder_of_mono
    {Λ : Type (u + 1)} [CommRing Λ] {X S : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : G ⟶ F) [Mono ι] [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    Scheme.IsTorsionSheafOfInvertibleOrder S G := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  constructor
  intro Ω _ _ s x
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  have : Limits.PreservesFiniteLimits
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)) := inferInstance
  have hi := (ModuleCat.mono_iff_injective ((Scheme.pointSmallEtale s).sheafFiber.map ι)).mp
    inferInstance
  obtain ⟨n, hn, hu, hx⟩ :=
    Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
      (S := S) Ω s (((Scheme.pointSmallEtale s).sheafFiber.map ι).hom x)
  refine ⟨n, hn, hu, hi ?_⟩
  simpa only [map_nsmul, map_zero] using hx

private theorem primary_of_mono
    {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : G ⟶ F) [Mono ι] (p : ℕ) (hF : Scheme.IsPrimaryTorsionSheaf Λ F p) :
    Scheme.IsPrimaryTorsionSheaf Λ G p := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  intro Ω _ _ s x
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  have : Limits.PreservesFiniteLimits
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)) := inferInstance
  have hi := (ModuleCat.mono_iff_injective ((Scheme.pointSmallEtale s).sheafFiber.map ι)).mp
    inferInstance
  obtain ⟨n, hn⟩ := hF Ω s (((Scheme.pointSmallEtale s).sheafFiber.map ι).hom x)
  refine ⟨n, hi ?_⟩
  simpa only [map_nsmul, map_zero] using hn

private theorem isZero_of_primary_invertible
    {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (p : ℕ) (hp : p.Prime) [CharP k p]
    (hF : Scheme.IsPrimaryTorsionSheaf Λ F p)
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F] :
    CategoryTheory.Limits.IsZero F := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  apply (Limits.IsZero.iff_id_eq_zero F).mpr
  apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro s
  have := (Scheme.pointSmallEtale (X.algClosurePoint s)).sheafFiber_additive
    (A := ModuleCat.{u + 1} Λ)
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  ext x
  obtain ⟨m, hm⟩ := hF _ (X.algClosurePoint s) x
  obtain ⟨n, _, hu, hn⟩ :=
    Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
      (S := Spec (.of k)) _ (X.algClosurePoint s) x
  let e := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  have hnk : (n : k) ≠ 0 := by
    have hh : IsUnit (n : k) := by simpa using hu.map e.toMonoidHom
    exact hh.ne_zero
  have hndiv : ¬ p ∣ n := by
    rintro ⟨a, rfl⟩
    apply hnk
    simp [Nat.cast_mul]
  have hc : (p ^ m).Coprime n := (hp.coprime_iff_not_dvd.mpr hndiv).pow_left m
  exact (nsmul_eq_zero_iff_of_coprime hc).mp ⟨hm, hn⟩

/-- Source: Stacks Project, Lemma 0GJA, proof, with Lemma 095L.
(blueprint: lem-pbc-j2-dense-open-finiteness-comparison).

Proof: The reduced closed complement Z is a finite set of k-rational points. In the open-closed
short exact sequence the third term Q = i_* i^* F has zero positive cohomology and finite
H^0, since its stalks are quotients of the finite constructible stalks of F. In degrees
at least two the first and middle terms have isomorphic cohomology. In degrees zero and
one the exact sequence is 0 → H^0(G) → H^0(F) → H^0(Q) → H^1(G) → H^1(F) → 0.
For either proper constructible finiteness or invertible-order constructible finiteness,
this exact sequence transfers finiteness from G to F: subgroups, quotients and extensions
of finite groups are finite. In the reverse direction it transfers finiteness from F
to G by the same argument and the finite H^0(Q). Constructibility of F is the assumption
hP, transported to the module coefficient encoding. For invertible-order finiteness in
the reverse direction, if F is primary and G has invertible order then G is zero by
stalk conservativity; otherwise the assumed torsion alternative gives invertible order
of F. All arguments apply to empty Z and the zero sheaf.
-/
theorem IsCurve.dense_open_finiteness_comparison {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) (hP : (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)))
    (U : P.C.Opens) (hU : Dense (U : Set P.C)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let F' := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
    let G := (sheafCompose P.C.smallEtaleTopology E).obj F'
    (IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) G k →
      IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) F k) ∧
    ((Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
      ∃ p : ℕ, p.Prime ∧ CharP k p ∧
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
      IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) F k →
      IsCurve.FiniteOfInvertibleOrder (ULift.{u + 1} ℤ) G k) ∧
    (IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) P.toSpec G →
      IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) P.toSpec F) ∧
    ((Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
      ∃ p : ℕ, p.Prime ∧ CharP k p ∧
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
      IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) P.toSpec F →
      IsCurve.FiniteOfIsProper (ULift.{u + 1} ℤ) P.toSpec G) := by
  classical
  dsimp only
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
  let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
  let B := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
    ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
  let G := (sheafCompose P.C.smallEtaleTopology E).obj B
  let T := sheafCompose P.C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  have : T.Additive := { map_add := by intros; rfl }
  have : IsCurve P.toSpec := P.isCurve
  have : IsNoetherian P.C := isNoetherian_of_locallyOfFiniteType P.toSpec
  have : TopologicalSpace.NoetherianSpace P.C := inferInstance
  have : TopologicalSpace.NoetherianSpace U :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact U.ι := ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : Scheme.IsConstructibleSheaf F :=
    (Scheme.isConstructibleSheaf_integral_iff P.F 
      ((Scheme.isTorsionAbelianSheaf_characterizations
        P.F).1.mpr P.isTorsion)).mpr hP
  let J := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).obj
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).obj F)
  obtain ⟨e⟩ := Etale.integral_open_extension_comparison P.F U
  have : Scheme.IsConstructibleSheaf J := by
    have : Scheme.IsConstructibleSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).obj F) :=
      Scheme.IsConstructibleSheaf.upperStar _ _
    exact Scheme.IsConstructibleSheaf.openImmersionLowerShriek U.ι U.closedComplement
      (by rw [U.range_closedComplement, Scheme.Opens.range_ι]) _
  have : Scheme.IsConstructibleSheaf G := Scheme.IsConstructibleSheaf.of_iso e.symm
  let ε : J ⟶ F :=
    (Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).counit.app F
  have : Mono ε :=
    (Etale.shortExact_openClosedShortComplex (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      U.ι U.closedComplement F
      (by rw [U.range_closedComplement, Scheme.Opens.range_ι])).mono_f
  let ι : G ⟶ F := e.hom ≫ ε
  have : Mono ι := inferInstance
  have hfinite := IsCurve.dense_open_integral_cohomology_finiteness P hP U hU
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h _ _ q
    have : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) G :=
      invertibleOrder_of_mono ι
    exact hfinite.mpr (fun q ↦ h q) q
  · intro ht h _ _ q
    rcases ht with hi | ⟨p, hp, hc, hprimary⟩
    · have := hi
      exact hfinite.mp (fun q ↦ h q) q
    · have := hc
      have hz := isZero_of_primary_invertible (k := k) G p hp (primary_of_mono ι p hprimary)
      have : Subsingleton (Sheaf.H (T.obj G) q) :=
        Sheaf.subsingleton_H_of_isZero (T.map_isZero hz) q
      infer_instance
  · intro h _ _ q
    exact hfinite.mpr (fun q ↦ h q) q
  · intro _ h _ _ q
    exact hfinite.mp (fun q ↦ h q) q


end AlgebraicGeometry
