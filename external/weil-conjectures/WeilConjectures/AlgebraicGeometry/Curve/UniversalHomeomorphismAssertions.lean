/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.CohomologyRestrictionSquareTransport

/-! Transfer of curve assertions across a universal homeomorphism. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
open Etale

/-- Assertions transfer across a surjective closed universal homeomorphism of curves.
Source: Stacks Project, Theorem 59.83.10 (03SC), Proposition 59.45.4 (03SI).
(blueprint: lem-weil-pbc-universal-homeomorphism-assertions)

The proof compares the eight cohomology assertions through the equivalence of etale
sheaf categories induced by a universal homeomorphism. Pullback preserves the
constructibility and torsion conditions, and the comparison maps are compatible
with composition and base change. -/
theorem IsCurve.assertions_of_universalHomeomorphism
    (Λ : Type (u + 1)) [CommRing Λ] {k : Type u} [Field k] [IsAlgClosed k]
    {C D : Scheme.{u}} (f : C ⟶ Spec (.of k)) (i : D ⟶ C)
    [IsCurve f] [IsCurve (i ≫ f)] [IsClosedImmersion i]
    [IsUniversalHomeomorphism i]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : IsCurve.Assertions Λ (i ≫ f)
      ((i)^*[ModuleCat.{u + 1} Λ].obj F)) :
    IsCurve.Assertions Λ f F := by
  let E (X : Scheme.{u}) := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let F₀ := (i)^*[ModuleCat.{u + 1} Λ].obj F
  obtain ⟨α⟩ := pullback_forget_modules_iso Λ i F
  let e (q : ℕ) : Sheaf.H ((E C).obj F) q ≃+ Sheaf.H ((E D).obj F₀) q :=
    (cohomologyEquiv i ((E C).obj F) q).trans
    (((Sheaf.functorH _ q).mapIso α.symm).addCommGroupIsoToAddEquiv)
  have hprimary (p : ℕ) (hF : Scheme.IsPrimaryTorsionSheaf Λ F p) :
      Scheme.IsPrimaryTorsionSheaf Λ F₀ p := by
    intro Ω _ _ s x
    let e := ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) i s).app F).toLinearEquiv
    obtain ⟨n, hn⟩ := hF Ω (s ≫ i) (e x)
    refine ⟨n, e.injective ?_⟩
    simpa only [map_nsmul, map_zero] using hn
  have horder [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F] :
      Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F₀ := by
    constructor
    intro Ω _ _ s x
    let e := ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) i s).app F).toLinearEquiv
    obtain ⟨n, hn, hu, hx⟩ :=
      Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
        (S := Spec (.of k)) Ω (s ≫ i) (e x)
    refine ⟨n, hn, hu, e.injective ?_⟩
    simpa only [map_nsmul, map_zero] using hx
  have htransfer {X' X₀' : Scheme.{u}} (g : X' ⟶ C) (j : X₀' ⟶ X')
      (l : X₀' ⟶ D) [IsUniversalHomeomorphism j] (hh : j ≫ g = l ≫ i) (q : ℕ)
      (hb : Function.Bijective (cohomologyMap l ((E D).obj F₀) q)) :
      Function.Bijective (cohomologyMap g ((E C).obj F) q) := by
    obtain ⟨b₁, b₂, hcomm⟩ := exists_addEquiv_cohomology_restrictionSquare
      Λ g i j l hh F q (cohomologyMap_bijective _ _ _) (cohomologyMap_bijective _ _ _)
    constructor
    · intro x y hxy
      apply b₁.injective
      apply hb.1
      rw [← hcomm x, ← hcomm y, hxy]
    · intro y
      obtain ⟨z, hz⟩ := hb.2 (b₂ y)
      refine ⟨b₁.symm z, b₂.injective ?_⟩
      rw [hcomm, b₁.apply_symm_apply, hz]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have : Subsingleton (Sheaf.H ((E D).obj F₀) q) := H.subsingleton_of_two_lt q hq
    exact (e q).injective.subsingleton
  · intro _ q hq
    have : IsAffine D := isAffine_of_isAffineHom i
    have : Subsingleton (Sheaf.H ((E D).obj F₀) q) :=
      H.subsingleton_of_one_lt_of_isAffine q hq
    exact (e q).injective.subsingleton
  · intro p _ _ hF q hq
    have : Subsingleton (Sheaf.H ((E D).obj F₀) q) :=
      H.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p (hprimary p hF) q hq
    exact (e q).injective.subsingleton
  · intro _ _ q
    have : Scheme.IsConstructibleSheaf F₀ := Scheme.IsConstructibleSheaf.upperStar i F
    have : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F₀ := horder
    have : Finite (Sheaf.H ((E D).obj F₀) q) :=
      H.finite_of_isTorsionSheafOfInvertibleOrder q
    exact Finite.of_injective _ (e q).injective
  · intro _ _ q
    have : IsProper (i ≫ f) := inferInstance
    have : Scheme.IsConstructibleSheaf F₀ := Scheme.IsConstructibleSheaf.upperStar i F
    have : Finite (Sheaf.H ((E D).obj F₀) q) := H.finite_of_isProper q
    exact Finite.of_injective _ (e q).injective
  · intro _ k' _ _ C' ι f' g h q
    have : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F₀ := horder
    let j := pullback.fst g i
    let l := pullback.snd g i
    have hj : IsUniversalHomeomorphism j := inferInstance
    have hs := (IsPullback.of_hasPullback g i).flip.paste_vert h
    exact htransfer g j l pullback.condition q
      (H.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' hs q)
  · intro _ k' _ _ C' ι f' g h q
    have : IsProper (i ≫ f) := inferInstance
    let j := pullback.fst g i
    let l := pullback.snd g i
    have hj : IsUniversalHomeomorphism j := inferInstance
    have hs := (IsPullback.of_hasPullback g i).flip.paste_vert h
    exact htransfer g j l pullback.condition q
      (H.bijective_cohomologyMap_of_isProper k' hs q)
  · intro W a _
    let j := pullback.fst a i
    let l := pullback.snd a i
    have : IsUniversalHomeomorphism j := inferInstance
    have : IsOpenImmersion l := inferInstance
    obtain ⟨b₁, b₂, hcomm⟩ := exists_addEquiv_cohomology_restrictionSquare
      Λ a i j l pullback.condition F 2
      (cohomologyMap_bijective _ _ _) (cohomologyMap_bijective _ _ _)
    intro y
    obtain ⟨z, hz⟩ := H.surjective_cohomologyMap_of_isOpenImmersion l (b₂ y)
    refine ⟨b₁.symm z, b₂.injective ?_⟩
    rw [hcomm, b₁.apply_symm_apply, hz]

end AlgebraicGeometry
