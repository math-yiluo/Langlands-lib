/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenClosedTerm
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Ring.BooleanRing
import Std.Tactic.BVDecide.Normalize.Prop

/-! # Dense-open field-extension comparison ingredients -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- Simultaneous degree-zero and degree-one comparison bijections transfer across
extension by zero from a dense open, for one algebraically closed field extension.
Source: Stacks Project, Tag 0GJA, proof (five-term exact sequence and remark (c)).
(blueprint: lem-pbc-x2-dense-open-low-base-change)

Proof: The reduced closed complement is a finite union of spectra of k, since density
excludes the generic points of the Noetherian curve. Its base change is the corresponding
union of spectra of k'. Closed direct image is exact and its cohomology is that of the
complement. The degree-zero comparison is the product of the canonical stalk comparisons,
which are bijections; positive cohomology vanishes over both fields. The open-closed
short exact sequence and its inverse image therefore give the commuting five-term ladder
0 -> H⁰(G) -> H⁰(F) -> H⁰(B) -> H¹(G) -> H¹(F) -> 0, with the canonical cohomologyMap
as vertical maps. If the two G maps are bijections, the five lemma gives both F maps.
Conversely the first four-term diagram gives injectivity and surjectivity at H⁰(G),
and the last five-term diagram gives the bijection at H¹(G), using both F bijections
and the B bijection. Empty complements and empty schemes give the same exact diagram. -/
theorem dense_open_low_base_change (Λ : Type (u + 1)) [CommRing Λ]
    {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of k')}
    {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let G := (U.ι)_!open[ModuleCat.{u + 1} Λ].obj
      ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)
    (∀ q : ℕ, q ≤ 1 → Function.Bijective (cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)) ↔
    (∀ q : ℕ, q ≤ 1 → Function.Bijective (cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) q)) := by
  dsimp
  obtain ⟨B, b, w, hS, hB, hBX, hBY⟩ := dense_open_closed_term Λ f h F U hU
  let S := ShortComplex.mk _ b w
  obtain ⟨hY, δX, δY, _, _, hiX, hiY, exX, exY, c₁, c₂, c₃⟩ :=
    pullbackCohomology_longExact_ladder ι' S hS
  let := hBX
  let := hBY
  have surX : Function.Surjective (Sheaf.H.map S.f 1) := by
    intro x
    exact (exX 1).1 x |>.mp (Subsingleton.elim _ _)
  have surY : Function.Surjective (Sheaf.H.map (((ι')^*[AddCommGrpCat.{u + 1}]).map S.f) 1) := by
    intro x
    exact (exY 1).1 x |>.mp (Subsingleton.elim _ _)
  have hc₁ (q : ℕ) :
      (Sheaf.H.map (((ι')^*[AddCommGrpCat.{u + 1}]).map S.f) q).comp
        (cohomologyMap ι' S.X₁ q) =
      (cohomologyMap ι' S.X₂ q).comp (Sheaf.H.map S.f q) := AddMonoidHom.ext (fun x ↦ (c₁ q x).symm)
  have hc₂ (q : ℕ) :
      (Sheaf.H.map (((ι')^*[AddCommGrpCat.{u + 1}]).map S.g) q).comp
        (cohomologyMap ι' S.X₂ q) =
      (cohomologyMap ι' S.X₃ q).comp (Sheaf.H.map S.g q) := AddMonoidHom.ext (fun x ↦ (c₂ q x).symm)
  have hc₃ (q : ℕ) :
      (δY q).comp (cohomologyMap ι' S.X₃ q) =
      (cohomologyMap ι' S.X₁ (q + 1)).comp (δX q) := AddMonoidHom.ext (fun x ↦ (c₃ q x).symm)
  constructor
  · intro hF
    have hG₀ := AddMonoidHom.bijective_of_bijective_of_injective_of_left_exact
      _ _ _ _ _ _ _ (hc₁ 0) (hc₂ 0) (exX 0).1 (exY 0).1
      (hF 0 (by omega)) hB.1 hiX hiY
    have hG₁i := AddMonoidHom.injective_of_surjective_of_injective_of_injective
      _ _ _ _ _ _ _ _ _ _ (hc₂ 0) (hc₃ 0) (hc₁ 1)
      (exX 0).2.1 (exX 0).2.2 (exY 0).2.1
      (hF 0 (by omega)).2 hB.1 (hF 1 (by omega)).1
    have hG₁s := AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
      (δX 0) (Sheaf.H.map S.f 1) (0 : Sheaf.H S.X₂ 1 →+ Unit)
      (δY 0) (Sheaf.H.map (((ι')^*[AddCommGrpCat.{u + 1}]).map S.f) 1)
      (0 : Sheaf.H (((ι')^*[AddCommGrpCat.{u + 1}]).obj S.X₂) 1 →+ Unit)
      _ _ _ (0 : Unit →+ Unit) (hc₃ 0) (hc₁ 1) (by ext)
      (fun x ↦ by simpa using surX x) (exY 0).2.2
      (fun x ↦ by simpa using surY x) hB.2 (hF 1 (by omega)).2
      (fun _ _ _ ↦ Subsingleton.elim _ _)
    intro q hq
    interval_cases q
    · exact hG₀
    · exact ⟨hG₁i, hG₁s⟩
  · intro hG
    have hF₀i := AddMonoidHom.injective_of_surjective_of_injective_of_injective
      (0 : Unit →+ Sheaf.H S.X₁ 0) (Sheaf.H.map S.f 0) (Sheaf.H.map S.g 0)
      (0 : Unit →+ Sheaf.H (((ι')^*[AddCommGrpCat.{u + 1}]).obj S.X₁) 0)
      (Sheaf.H.map (((ι')^*[AddCommGrpCat.{u + 1}]).map S.f) 0)
      (Sheaf.H.map (((ι')^*[AddCommGrpCat.{u + 1}]).map S.g) 0)
      (0 : Unit →+ Unit) _ _ _ (by ext; simp) (hc₁ 0) (hc₂ 0)
      (fun x ↦ by
        constructor
        · intro hx
          have hz := hiX (hx.trans (map_zero _).symm)
          exact ⟨0, hz.symm⟩
        · rintro ⟨y, rfl⟩
          exact map_zero _)
      (exX 0).1
      (fun x ↦ by
        constructor
        · intro hx
          have hz := hiY (hx.trans (map_zero _).symm)
          exact ⟨0, hz.symm⟩
        · rintro ⟨y, rfl⟩
          exact map_zero _)
      (fun _ ↦ ⟨0, rfl⟩) (hG 0 (by omega)).1 hB.1
    have hF₀s := AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
      _ _ _ _ _ _ _ _ _ _ (hc₁ 0) (hc₂ 0) (hc₃ 0)
      (exX 0).2.1 (exY 0).1 (exY 0).2.1
      (hG 0 (by omega)).2 hB.2 (hG 1 (by omega)).1
    have hF₁ := AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      _ _ _ _ _ _ _ (hc₃ 0) (hc₁ 1) (exX 0).2.2 (exY 0).2.2
      hB.2 (hG 1 (by omega)) surX surY
    intro q hq
    interval_cases q
    · exact ⟨hF₀i, hF₀s⟩
    · exact hF₁

end AlgebraicGeometry.IsCurve
