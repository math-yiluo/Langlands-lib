/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.ModuleValuedInjectiveCohomology
import WeilConjectures.AlgebraicGeometry.InjectiveModuleAbelianAcyclic
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Category.Grp.Zero

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale

private theorem exactForget (X : Scheme.{u}) (r : ℕ) :
    let U := sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})
    PreservesFiniteLimits U ∧ PreservesFiniteColimits U := by
  let A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))
  let B := AddCommGrpCat.{u + 1}
  let F := forget₂ A B
  let U := sheafCompose X.smallEtaleTopology F
  let W := (Functor.whiskeringRight X.Etaleᵒᵖ A B).obj F
  have : PreservesColimitsOfSize.{u + 1, u + 1} F :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1} _
  have : PreservesLimitsOfSize.{u + 1, u + 1} F := inferInstance
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      (U ⋙ sheafToPresheaf X.smallEtaleTopology B) :=
    inferInstanceAs (PreservesLimitsOfSize.{u + 1, u + 1}
      (sheafToPresheaf X.smallEtaleTopology A ⋙ W))
  have hlim := preservesLimits_of_reflects_of_preserves U
    (sheafToPresheaf X.smallEtaleTopology B)
  have : X.smallEtaleTopology.PreservesSheafification F :=
    GrothendieckTopology.instPreservesSheafification X.smallEtaleTopology F
  let e := sheafComposeNatIso X.smallEtaleTopology F
    (sheafificationAdjunction X.smallEtaleTopology A)
    (sheafificationAdjunction X.smallEtaleTopology B)
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (presheafToSheaf X.smallEtaleTopology A ⋙ U) :=
    preservesColimits_of_natIso e
  have hcolim := (Adjunction.preservesColimitsOfSize_iff
    (sheafificationAdjunction X.smallEtaleTopology A) U).mpr inferInstance
  exact ⟨inferInstance, inferInstance⟩

/-- An injective embedding gives a right exact cohomology ladder for dimension shifting.
Source: Stacks Project, Tags 03FD, 095T and 010S.
(blueprint: new-module-acyclic-effacement-ladder)

Proof: Embed M into an injective module-valued sheaf J, using enough injectives
in the Grothendieck abelian category of module-valued sheaves. Let Q be its cokernel
and g : J → Q the quotient. Forgetting coefficients is exact, so 0 → U(M) → U(J)
→ U(Q) → 0 is short exact. Exact abelian inverse image gives the second short exact
sequence. Take the canonical connecting homomorphisms δX and δY in degree q.
The long exact sequences give exactness at H^q(U(Q)) and its pullback.
Module-valued sheaves are equivalent to modules over the constant ring sheaf:
extend the constant scalar action uniquely over sheafification. This equivalence
commutes with underlying abelian sheaves and preserves injectivity. Thus Tag 03FD
makes H^{q+1}(U(J)) zero. The canonical isomorphism i^*U(J) ≅ U(i^*J), obtained
by commuting the coefficient forgetful functor with inverse image, and hacyclic
make the corresponding group on Y zero as well. Exactness then makes both
connecting maps surjective. Naturality of the long exact sequence under exact
inverse image, including the constant-integer-sheaf comparison in cohomologyMap,
gives the commuting boundary square. The case q = 0 uses only vanishing in degree
one, and includes M = 0. None of these steps asserts comparison for M or Q. -/
theorem Etale.exists_module_acyclic_effacement_ladder
    {X Y : Scheme.{u}} (i : Y ⟶ X) (r : ℕ)
    (hacyclic : ∀ (J : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) [Injective J]
        (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
          AddCommGrpCat.{u + 1})).obj
            ((i)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))].obj J)) q))
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) (q : ℕ) :
    let U := sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})
    let V := (i)^*[AddCommGrpCat.{u + 1}]
    ∃ (J Q : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) (g : J ⟶ Q),
    ∃ δX : Sheaf.H (U.obj Q) q →+ Sheaf.H (U.obj M) (q + 1),
    ∃ δY : Sheaf.H (V.obj (U.obj Q)) q →+ Sheaf.H (V.obj (U.obj M)) (q + 1),
      Function.Exact (Sheaf.H.map (U.map g) q) δX ∧
      Function.Exact (Sheaf.H.map (V.map (U.map g)) q) δY ∧
      Function.Surjective δX ∧ Function.Surjective δY ∧
      δY.comp (cohomologyMap i (U.obj Q) q) =
        (cohomologyMap i (U.obj M) (q + 1)).comp δX := by
  classical
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})
  let V := (i)^*[AddCommGrpCat.{u + 1}]
  have hU := exactForget X r
  have : PreservesFiniteLimits U := hU.1
  have : PreservesFiniteColimits U := hU.2
  let S := ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M))
    (cokernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have hUS : (S.map U).ShortExact := hS.map_of_exact U
  obtain ⟨hY, δX, δY, _, _, _, _, hEX, hEY, _, _, hδ⟩ :=
    pullbackCohomology_longExact_ladder i (S.map U) hUS
  obtain ⟨I, hI, -, hcomp⟩ := moduleValued_injective_cohomology_comparison X r S.X₂
  have : Injective I := hI
  have hzero := Scheme.isZero_rightDerived_etale_toSheaf_of_injective X
    (ULift.{u} (ZMod r)) I (Scheme.Etale.mk (𝟙 X)) (q + 1) (Nat.zero_lt_succ q)
  have := AddCommGrpCat.subsingleton_of_isZero hzero
  obtain ⟨eH⟩ := hcomp (q + 1)
  have hJ : Subsingleton (Sheaf.H (U.obj S.X₂) (q + 1)) := eH.injective.subsingleton
  have hJY := hacyclic S.X₂ (q + 1) (Nat.zero_lt_succ q)
  obtain ⟨e⟩ := pullback_forget_modules_iso (ULift.{u + 1} (ZMod r)) i S.X₂
  have hinj : Function.Injective (Sheaf.H.map e.inv (q + 1)) := by
    intro a b hab
    have h := congrArg (Sheaf.H.map e.hom (q + 1)) hab
    simpa only [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply] using h
  have hVJ : Subsingleton (Sheaf.H (V.obj (U.obj S.X₂)) (q + 1)) :=
    hinj.subsingleton
  refine ⟨S.X₂, S.X₃, S.g, δX q, δY q, (hEX q).2.1, (hEY q).2.1, ?_, ?_, ?_⟩
  · intro x
    exact ((hEX q).2.2 x).mp (hJ.elim _ _)
  · intro x
    exact ((hEY q).2.2 x).mp (hVJ.elim _ _)
  · apply AddMonoidHom.ext
    intro x
    exact (hδ q x).symm

end AlgebraicGeometry
