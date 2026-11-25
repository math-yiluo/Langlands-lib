/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenHighCohomology
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness
import WeilConjectures.AlgebraicGeometry.Curve.PrimeAnnihilatedPrimaryCases
import WeilConjectures.AlgebraicGeometry.Curve.PrimeAnnihilatedInvertibleCases

/-! # Primary vanishing and finiteness across a dense open -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- Primary vanishing and the two conditional finiteness assertions transfer across a
 dense-open counit for a constructible sheaf killed by a prime.
Source: Stacks Project, Tag 0GJA, proof, the five-term sequence and remarks (a), (b)
(blueprint: lem-pbc-s2-dense-open-primary-finiteness).

Proof: Put G = j_!j^*F and B = i_*i^*F for the reduced closed complement i:Z -> X.
The geometric stalks of G are those of F on U and zero outside U. Hence G is constructible
and killed by r. Both primary torsion and invertible-order torsion pass from F to G.
The complement is a finite union of k-rational points. Its degree-zero cohomology is a
finite product of stalk modules of F; these are finite because constructibility gives
finite generation and Λ is finite. Its positive-degree cohomology vanishes. The long exact
sequence gives 0 -> H^0(G) -> H^0(F) -> H^0(B) -> H^1(G) -> H^1(F) -> 0 and canonical
bijections H^q(G) -> H^q(F) for q >= 2. Consequently, finiteness of all groups for either
sheaf implies finiteness for the other: in degree zero use the injection and the finite
boundary group; in degree one use the surjection and its kernel, a quotient of that
boundary group; in higher degrees use the bijections. This proves the proper finiteness
assertion. For primary vanishing, fix a prime p equal to the characteristic. If r = p,
both sheaves are p-primary and the higher-degree bijections transfer the vanishings.
If r != p and G is p-primary, every stalk of G is killed by coprime integers, so G is zero
and its cohomology vanishes. In the reverse implication, if F is p-primary the same
coprimality argument makes F zero when r != p. For invertible-order finiteness, if r is
invertible in k, both sheaves have invertible-order torsion and the preceding finite-group
argument applies. If r is not invertible, an invertible-order hypothesis on either sheaf
forces that sheaf to be zero. All assertions are then automatic for that sheaf. These
cases prove the conditional equivalences without claiming the torsion hypotheses are
equivalent. Empty X and the full open U=X are covered by the same zero or identity maps. -/
theorem dense_open_primary_finiteness (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0)
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let G := (U.ι)_!open[ModuleCat.{u + 1} Λ].obj
      ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)
    (VanishingAboveOneOfIsPrimaryTorsionSheaf Λ F k ↔
      VanishingAboveOneOfIsPrimaryTorsionSheaf Λ G k) ∧
    (FiniteOfInvertibleOrder Λ F k ↔ FiniteOfInvertibleOrder Λ G k) ∧
    (FiniteOfIsProper Λ f F ↔ FiniteOfIsProper Λ f G) := by
  classical
  let G := (U.ι)_!open[ModuleCat.{u + 1} Λ].obj
    ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)
  let A := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : A.Additive := { map_add := by intros; rfl }
  let ε : A.obj G ⟶ A.obj F := A.map
    ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).counit.app F)
  have hG : r • 𝟙 G = 0 := by
    have h := congrArg
      (((U.ι)^*[ModuleCat.{u + 1} Λ] ⋙ (U.ι)_!open[ModuleCat.{u + 1} Λ]).map) hF
    simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero,
      Functor.comp_obj] using h
  have : Scheme.IsConstructibleSheaf G := by
    have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
    have : TopologicalSpace.NoetherianSpace X := inferInstance
    have : TopologicalSpace.NoetherianSpace U :=
      U.ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact U.ι := ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    have : Scheme.IsConstructibleSheaf (((U.ι)^*[ModuleCat.{u + 1} Λ]).obj F) :=
      Scheme.IsConstructibleSheaf.upperStar _ _
    exact Scheme.IsConstructibleSheaf.openImmersionLowerShriek U.ι U.closedComplement
      (by rw [U.range_closedComplement, Scheme.Opens.range_ι]) _
  have hzero (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (hM : Limits.IsZero M) (q : ℕ) : Subsingleton (Sheaf.H (A.obj M) q) :=
    Sheaf.subsingleton_H_of_isZero (A.map_isZero hM) q
  have hprimaryF := Scheme.prime_annihilated_primary_cases Λ r F hF
  have hprimaryG := Scheme.prime_annihilated_primary_cases Λ r G hG
  have hinvertibleF := Scheme.prime_annihilated_invertible_cases Λ (k := k) r F hF
  have hinvertibleG := Scheme.prime_annihilated_invertible_cases Λ (k := k) r G hG
  have hfinite := dense_open_cohomology_finiteness Λ f F U hU
  have hhigh (q : ℕ) (hq : 1 < q) : Function.Bijective (Sheaf.H.map ε q) :=
    (dense_open_high_cohomology Λ f F U hU).1 q hq
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h p _ _ hp q hq
      by_cases hrp : r = p
      · subst p
        exact (Equiv.ofBijective _ (hhigh q hq)).subsingleton_congr.mpr
          (h r hprimaryF.1 q hq)
      · exact hzero G (hprimaryG.2 p hrp hp) q
    · intro h p _ _ hp q hq
      by_cases hrp : r = p
      · subst p
        exact (Equiv.ofBijective _ (hhigh q hq)).subsingleton_congr.mp
          (h r hprimaryG.1 q hq)
      · exact hzero F (hprimaryF.2 p hrp hp) q
  · by_cases hr : IsUnit (r : Γ(Spec (.of k), ⊤))
    · have := hinvertibleF.1 hr
      have := hinvertibleG.1 hr
      exact ⟨fun h _ _ ↦ hfinite.mp (fun q ↦ h q),
        fun h _ _ ↦ hfinite.mpr (fun q ↦ h q)⟩
    · constructor
      · intro _ _ hGinv q
        have := hzero G (hinvertibleG.2 hr hGinv) q
        infer_instance
      · intro _ _ hFinv q
        have := hzero F (hinvertibleF.2 hr hFinv) q
        infer_instance
  · exact ⟨fun h _ _ ↦ hfinite.mp (fun q ↦ h q),
      fun h _ _ ↦ hfinite.mpr (fun q ↦ h q)⟩

end AlgebraicGeometry.IsCurve
