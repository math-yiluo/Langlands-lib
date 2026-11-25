/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforwardModuleAssertions
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

/-! # Finite-open transfer for prime module coefficients

Source: Stacks Project, etale-cohomology.tex, 0A5D and 0GJ1.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

private theorem invertibleOrder_of_iso {Λ : Type (u + 1)} [CommRing Λ]
    {S X : Scheme.{u}} {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (e : F ≅ G) [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    Scheme.IsTorsionSheafOfInvertibleOrder S G where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x := by
    let es := (Scheme.pointSmallEtale s).sheafFiber.mapIso e
    obtain ⟨n, hn, hu, hx⟩ :=
      Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
        (S := S) (F := F) Ω s (es.inv.hom x)
    refine ⟨n, hn, hu, ?_⟩
    have he : es.hom.hom (es.inv.hom x) = x := by
      rw [← ModuleCat.comp_apply, es.inv_hom_id, ModuleCat.id_apply]
    rw [← he, ← map_nsmul, hx, map_zero]

/-- Assertions descend along a split monomorphism when the conditional hypotheses
pass to the larger sheaf. This applies to genuine retracts, without an isomorphism.
Source: Stacks Project, 03SD, first proof paragraph (retract devissage). -/
private theorem assertions_of_retraction {Λ : Type (u + 1)} [CommRing Λ]
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : F ⟶ G) (b : G ⟶ F) (hab : a ≫ b = 𝟙 F)
    (hc : Scheme.IsConstructibleSheaf F → Scheme.IsConstructibleSheaf G)
    (hp : ∀ p, Scheme.IsPrimaryTorsionSheaf Λ F p →
      Scheme.IsPrimaryTorsionSheaf Λ G p)
    (ho : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F →
      Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) G)
    (h : Assertions Λ f G) : Assertions Λ f F := by
  let T := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let a' := T.map a
  let b' := T.map b
  have hab' : a' ≫ b' = 𝟙 (T.obj F) := by
    dsimp [a', b']
    rw [← T.map_comp, hab, T.map_id]
  have hinj (q : ℕ) : Function.Injective (Sheaf.H.map a' q) := by
    apply Function.LeftInverse.injective (g := Sheaf.H.map b' q)
    intro x
    rw [← Sheaf.H.map_comp_apply, hab', Sheaf.H.map_id_apply]
  have hsurj {Y : Scheme.{u}} (g : Y ⟶ X) (q : ℕ)
      (hg : Function.Surjective (Etale.cohomologyMap g (T.obj G) q)) :
      Function.Surjective (Etale.cohomologyMap g (T.obj F) q) := by
    intro y
    obtain ⟨x, hx⟩ := hg (Sheaf.H.map ((Etale.upperStar _ g).map a') q y)
    refine ⟨Sheaf.H.map b' q x, ?_⟩
    rw [Etale.cohomologyMap_map, hx, ← Sheaf.H.map_comp_apply,
      ← CategoryTheory.Functor.map_comp, hab', CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply]
  have hbij {Y : Scheme.{u}} (g : Y ⟶ X) (q : ℕ)
      (hg : Function.Bijective (Etale.cohomologyMap g (T.obj G) q)) :
      Function.Bijective (Etale.cohomologyMap g (T.obj F) q) := by
    refine ⟨?_, hsurj g q hg.2⟩
    intro x y hxy
    apply hinj q
    apply hg.1
    simpa only [Etale.cohomologyMap_map] using
      congrArg (Sheaf.H.map ((Etale.upperStar _ g).map a') q) hxy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have := h.subsingleton_of_two_lt q hq
    exact (hinj q).subsingleton
  · intro _ q hq
    have := h.subsingleton_of_one_lt_of_isAffine q hq
    exact (hinj q).subsingleton
  · intro p _ _ hF q hq
    have := h.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p (hp p hF) q hq
    exact (hinj q).subsingleton
  · intro hF hFo q
    have := hc hF
    have := ho hFo
    have := h.finite_of_isTorsionSheafOfInvertibleOrder q
    exact Finite.of_injective _ (hinj q)
  · intro _ hF q
    have := hc hF
    have := h.finite_of_isProper q
    exact Finite.of_injective _ (hinj q)
  · intro hF k' _ _ X' ι f' ι' hs q
    have := ho hF
    exact hbij ι' q (h.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' hs q)
  · intro _ k' _ _ X' ι f' ι' hs q
    exact hbij ι' q (h.bijective_cohomologyMap_of_isProper k' hs q)
  · intro W g _
    exact hsurj g 2 (h.surjective_cohomologyMap_of_isOpenImmersion g)

/-- Transfer assertions across a finite-open square, allowing a supplied
isomorphism of the sheaf on the upper open. No filtration or constant-case
hypothesis is part of this result.

Source: Stacks Project 0A5D (lemma-finite-pushforward-statements) and
0GJ1 (lemma-compatible-shriek-push-finite).
(blueprint: r1-prime-module-finite-open-assertions-transfer)

Proof: Apply a_! to e and transport the eight assertions to a_! H. Finite
pushforward preserves them: its cohomology comparison is an isomorphism in
all degrees, since finite pushforward has no positive derived functors.
For C2 a finite scheme over an affine is affine; for C5 and C7 a finite
scheme over a proper scheme is proper. The torsion conditions in C3 and C6
pass from p_* a_! H to a_! H by the finite stalk formula, a finite product
of geometric stalks. Constructibility passes in the same direction when
needed for C4 and C5. Finite base change makes the cohomology comparisons
commute with field extension and restriction to opens, giving C6--C8.
All sheaves are r-torsion because the coefficient ring has characteristic r.
Finally the finite-open exchange identifies p_* a_! H with j_! v_* H,
and its naturality transports all eight assertions to the latter sheaf.
This includes zero sheaves and empty opens and does not require surjectivity. -/
theorem prime_module_finite_open_assertions_transfer
    {k : Type u} [Field k] [IsAlgClosed k] {X U V Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] (p : Y ⟶ X) [IsFinite p]
    [IsCurve (p ≫ f)] (j : U ⟶ X) [IsOpenImmersion j]
    (a : V ⟶ Y) [IsOpenImmersion a] (v : V ⟶ U) (sq : IsPullback a v p j)
    (r : ℕ) [Fact r.Prime]
    (F H : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    (e : F ≅ H)
    (hF : Assertions (ULift.{u + 1} (ZMod r)) (p ≫ f)
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) a).obj
        F)) :
    Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj H)) := by
  have transport {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))
      {P Q : Sheaf Z.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))} (i : P ≅ Q)
      (h : Assertions (ULift.{u + 1} (ZMod r)) g P) :
      Assertions (ULift.{u + 1} (ZMod r)) g Q := by
    apply assertions_of_retraction g i.inv i.hom i.inv_hom_id ?_ ?_ ?_ h
    · intro hQ
      let := hQ
      exact Scheme.IsConstructibleSheaf.of_iso i.symm
    · intro t hQ Ω _ _ s x
      let es := (Scheme.pointSmallEtale s).sheafFiber.mapIso i
      obtain ⟨n, hn⟩ := hQ Ω s (es.hom.hom x)
      refine ⟨n, ?_⟩
      apply (ModuleCat.mono_iff_injective es.hom).mp inferInstance
      simpa using hn
    · intro hQ
      let := hQ
      exact invertibleOrder_of_iso i.symm
  let R := ULift.{u + 1} (ZMod r)
  let A := ModuleCat.{u + 1} R
  let K := (Etale.openImmersionLowerShriek A a).obj H
  have hK : Assertions R (p ≫ f) K :=
    transport (p ≫ f) ((Etale.openImmersionLowerShriek A a).mapIso e) hF
  have hprime := Assertions.of_finite_pushforward_module R p f K hK
  have := Etale.isIso_finiteOpenComparison_app A sq H
  exact transport f (asIso ((Etale.finiteOpenComparison A sq).app H)).symm
    hprime

end AlgebraicGeometry.IsCurve
