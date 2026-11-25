/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity

import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.AlgebraicGeometry.AlgClosedExtensionModuleSections
import WeilConjectures.AlgebraicGeometry.ModuleAcyclicCohomologyComparisonZero
import WeilConjectures.AlgebraicGeometry.KilledSheafModuleLift
import WeilConjectures.AlgebraicGeometry.IsProperOrIsAffine
import WeilConjectures.AlgebraicGeometry.Curve.RootTrivializationBaseChange
import WeilConjectures.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility
import WeilConjectures.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange
import WeilConjectures.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange

/-!
# Canonical pullback in degrees zero and one

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
proof of proposition-cohomology-smooth-affine-curve, proper and affine cases in degrees zero and one
(blueprint: lem-sc-constant-low-degree-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
proof of proposition-cohomology-smooth-affine-curve, proper and affine cases in degrees zero and one
(blueprint: lem-sc-constant-low-degree-base-change).

Proof: baseChange_curve preserves the smooth connected curve hypotheses. Choose a primitive
root in k and transport it to K; exponentiation by it identifies constant coefficients with
roots of unity and commutes with pullback. In degree zero both groups are the roots of unity
in the ground fields, and the primitive-root coordinates identify the map with the identity.
For a proper curve, divisibility of global units and the Kummer sequence identify degree one
with Picard n-torsion. Identify this with Jacobian n-torsion;
genus_jacobian_invariant and the finite-etale n-torsion assertion of thm-av-final make its
pullback bijective. For an affine curve, the Kummer short exact ladder has bijective outer
maps by units_quotient_base_change and the affine Picard-torsion clause of
kummer_base_change_compatibility, so its middle map in degree one is bijective by the short
five lemma. The proper-or-affine dichotomy exhausts all connected smooth curves.
For n = 1 the groups are zero and the same argument applies. -/
theorem IsConnectedCurve.constant_low_degree_baseChange_bijective
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    (n : ℕ) [NeZero n] (hn : (n : k) ≠ 0)
    (r : ∀ q : ℕ, Sheaf.H (C.constantZMod n) q →+
        Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) q)
    (hr : (∀ q : ℕ, r q =
        (Sheaf.H.map (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))).hom) q).comp
          (Etale.cohomologyMap
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (C.constantZMod n) q))) :
    ∀ q : ℕ, q ≤ 1 → Function.Bijective (r q) := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let P := pullback f b
  let π := pullback.fst f b
  let e := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} π).app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))
  have he (q : ℕ) : Function.Bijective (Sheaf.H.map e.hom q) :=
    ConcreteCategory.bijective_of_isIso ((Sheaf.functorH _ q).mapIso e).hom
  have hzero : Function.Bijective (Etale.cohomologyMap π (C.constantZMod n) 0) := by
    have hkill : n • 𝟙 (C.constantZMod n) = 0 := by
      let F := constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}
      have h : n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) = 0 := by
        ext x
        simp [nsmul_eq_mul]
      change n • 𝟙 (F.obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) = 0
      rw [← F.map_id, ← F.map_nsmul, h, F.map_zero]
    obtain ⟨M, ⟨a⟩⟩ := exists_module_sheaf_of_nsmul_id_eq_zero C n (C.constantZMod n) hkill
    have hM := Etale.bijective_cohomologyMap_of_module_acyclic_zero π n
      (Etale.isIso_globalSectionsUpperStarMap_algClosed_extension f n) M
    have ha : Function.Bijective (Sheaf.H.map a.hom 0) :=
      ConcreteCategory.bijective_of_isIso ((Sheaf.functorH _ 0).mapIso a).hom
    have haP : Function.Bijective
        (Sheaf.H.map ((Etale.upperStar AddCommGrpCat.{u + 1} π).map a.hom) 0) :=
      ConcreteCategory.bijective_of_isIso
        ((Sheaf.functorH _ 0).mapIso
          ((Etale.upperStar AddCommGrpCat.{u + 1} π).mapIso a)).hom
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨x', rfl⟩ := ha.2 x
      obtain ⟨y', rfl⟩ := ha.2 y
      apply congrArg (Sheaf.H.map a.hom 0)
      apply hM.1
      apply haP.1
      simpa only [← Etale.cohomologyMap_map] using hxy
    · intro y
      obtain ⟨y', rfl⟩ := haP.2 y
      obtain ⟨x', hx'⟩ := hM.2 y'
      refine ⟨Sheaf.H.map a.hom 0 x', ?_⟩
      rw [Etale.cohomologyMap_map, hx']
  have hone : Function.Bijective (r 1) := by
    have : NeZero (n : k) := ⟨hn⟩
    obtain ⟨_, _, ζ, hζ, hζext⟩ := IsSepClosed.exists_isPrimitiveRoot k n
    have hζK := hζext K (algebraMap k K)
    obtain ⟨_, _, φ, hφ, _⟩ := kummer_base_change_compatibility k K C f P π
      (pullback.snd f b) (IsPullback.of_hasPullback f b) n hn
    have hμ : Function.Bijective ((Sheaf.H.map φ.τ₁ 1).comp
        (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) 1)) := by
      obtain hf | hC := isProper_or_isAffine f
      · let : IsProper f := hf
        exact proper_kummer_degree_one_baseChange_bijective f n hn φ hφ
      · let : IsAffine C := hC
        exact affine_kummer_degree_one_baseChange_bijective f n hn φ hφ
    let a := C.constantZModIsoRootsOfUnitySheaf n f hζ
    let aP := P.constantZModIsoRootsOfUnitySheaf n (pullback.snd f b) hζK
    have ha : Function.Bijective (Sheaf.H.map a.hom 1) :=
      ConcreteCategory.bijective_of_isIso ((Sheaf.functorH _ 1).mapIso a).hom
    have haP : Function.Bijective (Sheaf.H.map aP.hom 1) :=
      ConcreteCategory.bijective_of_isIso ((Sheaf.functorH _ 1).mapIso aP).hom
    have hs := constant_root_trivialization_baseChange f n ζ hζ hζK φ hφ
    have hcomm (x : Sheaf.H (C.constantZMod n) 1) :
        Sheaf.H.map aP.hom 1 (r 1 x) =
          Sheaf.H.map φ.τ₁ 1
            (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) 1 (Sheaf.H.map a.hom 1 x)) := by
      rw [hr 1]
      change Sheaf.H.map aP.hom 1 (Sheaf.H.map e.hom 1
        (Etale.cohomologyMap π (C.constantZMod n) 1 x)) = _
      rw [Etale.cohomologyMap_map]
      calc
        _ = Sheaf.H.map (e.hom ≫ aP.hom) 1
            (Etale.cohomologyMap π (C.constantZMod n) 1 x) :=
          (Sheaf.H.map_comp_apply _ _ _).symm
        _ = Sheaf.H.map ((Etale.upperStar AddCommGrpCat.{u + 1} π).map a.hom ≫ φ.τ₁) 1
            (Etale.cohomologyMap π (C.constantZMod n) 1 x) := by
          exact congrArg (fun m ↦ Sheaf.H.map m 1
            (Etale.cohomologyMap π (C.constantZMod n) 1 x)) hs.symm
        _ = _ := Sheaf.H.map_comp_apply _ _ _
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply ha.1
      apply hμ.1
      change Sheaf.H.map φ.τ₁ 1
        (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) 1 (Sheaf.H.map a.hom 1 x)) =
        Sheaf.H.map φ.τ₁ 1
          (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) 1 (Sheaf.H.map a.hom 1 y))
      rw [← hcomm x, ← hcomm y, hxy]
    · intro y
      obtain ⟨z, hz⟩ := hμ.2 (Sheaf.H.map aP.hom 1 y)
      obtain ⟨x, hx⟩ := ha.2 z
      refine ⟨x, haP.1 ?_⟩
      rw [hcomm, hx]
      exact hz
  intro q hq
  have hq' : q = 0 ∨ q = 1 := by omega
  rcases hq' with rfl | rfl
  · rw [hr 0]
    exact (he 0).comp hzero
  · exact hone

end AlgebraicGeometry
