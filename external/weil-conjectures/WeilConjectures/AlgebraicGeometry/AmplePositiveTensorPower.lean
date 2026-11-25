/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import all WeilConjectures.AlgebraicGeometry.AmpleIso
import all WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators

/-! # Positive tensor powers preserve absolute ampleness

Source: Stacks Project, Properties Definition 01PS and Lemma 01PT;
Varieties Lemma 09NX, powering the component bundles.
(blueprint: lem-sc-ample-positive-tensor-power).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

private theorem nonvanishing_of_frame {X : Scheme.{u}} (M : X.Modules)
    (s : Γ(M, ⊤)) {V : X.Opens} {e : Γ(M, V)} (he : IsFreeGenerator e)
    (a : Γ(X, V)) (ha : M.presheaf.map (homOfLE le_top).op s = a • e)
    (x : X) (hx : x ∈ V) :
    x ∈ nonvanishingLocus M s ↔ IsUnit (X.presheaf.germ V x hx a) := by
  let g := TopCat.Presheaf.germ M.val.presheaf V x hx e
  have hg := bijective_smul_germ M he x hx
  have hspan : Submodule.span (X.presheaf.stalk x) ({g} : Set _) = ⊤ := by
    apply eq_top_iff.mpr
    intro z _
    obtain ⟨b, hb⟩ := hg.2 z
    exact Submodule.mem_span_singleton.mpr ⟨b, hb⟩
  have hsg : TopCat.Presheaf.germ M.val.presheaf ⊤ x trivial s =
      X.presheaf.germ V x hx a • g := by
    rw [← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE le_top) x hx s]
    change TopCat.Presheaf.germ M.val.presheaf V x hx
      (M.presheaf.map (homOfLE le_top).op s) = _
    rw [ha, PresheafOfModules.germ_smul]
    rfl
  have hmem : TopCat.Presheaf.germ M.val.presheaf ⊤ x trivial s ∈
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) • (⊤ : Submodule (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x)) ↔
      X.presheaf.germ V x hx a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [hsg, ← hspan, Submodule.mem_smul_span_singleton]
    constructor
    · rintro ⟨b, hb, heq⟩
      exact hg.1 heq ▸ hb
    · intro hb
      exact ⟨_, hb, rfl⟩
  change ¬ _ ↔ _
  rw [hmem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

/-- A positive tensor power of an ample invertible module is ample.

Source: Stacks Project, Properties Definition 01PS and Lemma 01PT;
Varieties Lemma 09NX, first two paragraphs.
(blueprint: lem-sc-ample-positive-tensor-power).

Proof: keep compactness from ampleness of M. At any point choose a positive exponent n,
a section s of M^n, and its affine nonvanishing open U containing the point. The kth
power of s is a global section of (M^n)^k. Transport it through the tensor-power
isomorphisms (M^n)^k ≅ M^(n*k) ≅ M^(k*n) ≅ (M^k)^n. In a local frame of M the
coefficient of the new section is the kth power of that of s. Since k is positive,
that coefficient is a unit in each local ring exactly when the original coefficient
is a unit. Consequently the nonvanishing locus stays U, and n, U and the transported
section witness ampleness of M^k at the chosen point. On the empty scheme the
pointwise condition is vacuous. Positivity is necessary: M^0 is the structure module,
which need not be ample on a nonaffine scheme.
-/
theorem isAmple_positive_tensorPow {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible]
    (hM : IsAmple X M) (k : ℕ) (hk : 0 < k) : IsAmple X (M.tensorPow k)  := by
  refine ⟨hM.1, fun x ↦ ?_⟩
  obtain ⟨n, hn, s, U, hx, hU, hs⟩ := hM.2 x
  let f : 𝟙_ X.Modules ⟶ M.tensorPow n := homOfGlobalSection _ s
  let e : (M.tensorPow n).tensorPow k ≅ (M.tensorPow k).tensorPow n :=
    (M.tensorPowMulIso n k).symm ≪≫
      eqToIso (congrArg M.tensorPow (Nat.mul_comm n k)) ≪≫ M.tensorPowMulIso k n
  let t := tensorPowSectionOne f k ⊤
  refine ⟨n, hn, e.hom.app ⊤ t, U, hx, hU, ?_⟩
  have hloc : nonvanishingLocus ((M.tensorPow n).tensorPow k) t =
      nonvanishingLocus (M.tensorPow n) s := by
    ext y
    have := IsInvertible.sheafOfModules_isInvertible (M.tensorPow n)
    obtain ⟨V, hyV, _, v, hv⟩ :=
      exists_isFreeGenerator (M.tensorPow n) (x := y) (W := ⊤) trivial
    let a := hv.coeff ((M.tensorPow n).presheaf.map (homOfLE le_top).op s)
    have ha : (M.tensorPow n).presheaf.map (homOfLE le_top).op s = a • v :=
      (hv.coeff_smul _).symm
    have hf : f.app V.1 (unitSectionsEquiv V.1 1) = a • v := by
      exact (homOfGlobalSection_app_one _ s V.1).trans ha
    obtain ⟨E, hE, hEt⟩ := exists_tensorPowSectionOne_eq_pow_smul f hv hf k
    have ht : ((M.tensorPow n).tensorPow k).presheaf.map (homOfLE le_top).op t =
        a ^ k • E := by
      rw [presheaf_map_tensorPowSectionOne]
      exact hEt
    rw [nonvanishing_of_frame _ t hE (a ^ k) ht y hyV,
      nonvanishing_of_frame _ s hv a ha y hyV, map_pow, isUnit_pow_iff hk.ne']
  intro y
  exact (hs y).trans ((Set.ext_iff.mp hloc y).symm.trans
    (Set.ext_iff.mp (nonvanishingLocus_iso e t) y).symm)

end AlgebraicGeometry.Scheme.Modules
