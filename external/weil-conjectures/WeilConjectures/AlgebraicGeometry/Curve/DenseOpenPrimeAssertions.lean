/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenHighCohomology
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenBaseChange

/-! # Dense-open comparison for prime-torsion module sheaves -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

private theorem surjective_iff_of_bijective_square
    {A B C D : Type*} (i : A → B) (j : C → D) (a : A → C) (b : B → D)
    (hi : Function.Bijective i) (hj : Function.Bijective j)
    (hcomm : ∀ x, j (a x) = b (i x)) :
    Function.Surjective a ↔ Function.Surjective b := by
  constructor
  · intro ha y
    obtain ⟨z, rfl⟩ := hj.2 y
    obtain ⟨x, rfl⟩ := ha z
    exact ⟨i x, (hcomm x).symm⟩
  · intro hb z
    obtain ⟨y, hy⟩ := hb (j z)
    obtain ⟨x, rfl⟩ := hi.2 y
    exact ⟨x, hj.1 ((hcomm x).trans hy)⟩

/-- The eight assertions are unchanged by extending the restriction from a dense open by zero.
Source: Stacks Project, Lemma 0GJA and its proof, specialized to prime-torsion coefficients
(blueprint: lemma-removing-finitely-many-points--1).

Proof: Give the closed complement Z its reduced scheme structure. It is a finite union of
k-rational points, since X has dimension at most one and U contains all generic points.
The open-closed sequence is 0 → j_! j^* F → F → i_* i^* F → 0. Finite direct image is exact,
so H^q(X,i_* i^* F) equals H^q(Z,i^* F): zero for q > 0, and in degree zero the finite
product of the geometric stalks at Z. Those stalks are finite: constructibility gives
finitely generated modules and the coefficient ring is finite. This product is unchanged
by extension of algebraically closed fields. The long exact sequence therefore gives
isomorphisms H^q(X,j_! j^* F) → H^q(X,F) for q ≥ 2 and the exact five-term sequence in
degrees zero and one. The same statements hold on every open W of X, with dense open W ∩ U,
and after every algebraically closed field extension, compatibly with all maps and boundaries.
Assertions C1-C3 use the isomorphisms in degree at least two. C4-C5 use these isomorphisms
and the finite boundary product in the five-term sequence. For C6-C7, use the commuting
five-term ladders in degrees zero and one and the higher-degree isomorphisms. C8 follows
from the commuting restriction square in degree two. Both sheaves are constructible and
killed by r. If r differs from the characteristic, both have invertible torsion; if r equals
it, both are primary. Any exceptional invertible or different-primary condition forces
the corresponding prime-torsion sheaf to be zero and is automatic. Thus these arguments
apply to the conditional forms of all eight assertions, in both directions. The empty
scheme and U = X give respectively zero groups and the identity comparison. -/
theorem assertions_iff_dense_open_prime (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0)
    (U : X.Opens) (hU : Dense (U : Set X)) :
    IsCurve.Assertions Λ f F ↔ IsCurve.Assertions Λ f
      ((U.ι)_!open[ModuleCat.{u + 1} Λ].obj ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)) := by
  let G := (U.ι)_!open[ModuleCat.{u + 1} Λ].obj
    ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)
  let A := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
  let B := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G
  let ε : B ⟶ A := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).counit.app F)
  obtain ⟨hhigh, hopen⟩ := dense_open_high_cohomology Λ f F U hU
  have hhigh' (q : ℕ) (hq : 1 < q) : Function.Bijective (Sheaf.H.map ε q) :=
    hhigh q hq
  have h₁ : VanishingAboveTwo Λ F ↔ VanishingAboveTwo Λ G := by
    constructor
    · intro h q hq
      exact (Equiv.ofBijective _ (hhigh' q (by omega))).subsingleton_congr.mpr (h q hq)
    · intro h q hq
      exact (Equiv.ofBijective _ (hhigh' q (by omega))).subsingleton_congr.mp (h q hq)
  have h₂ : VanishingAboveOneOfIsAffine Λ F ↔ VanishingAboveOneOfIsAffine Λ G := by
    constructor
    · intro h _ q hq
      exact (Equiv.ofBijective _ (hhigh' q hq)).subsingleton_congr.mpr (h q hq)
    · intro h _ q hq
      exact (Equiv.ofBijective _ (hhigh' q hq)).subsingleton_congr.mp (h q hq)
  obtain ⟨h₃, h₄, h₅⟩ := dense_open_primary_finiteness Λ f r F hF U hU
  obtain ⟨h₆, h₇⟩ := dense_open_base_change Λ f r F hF U hU
  have h₈ : SurjectiveRestrictionTwo Λ F ↔ SurjectiveRestrictionTwo Λ G := by
    constructor
    · intro h W a _
      exact (surjective_iff_of_bijective_square (Sheaf.H.map ε 2)
        (Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map ε) 2)
        (cohomologyMap a B 2) (cohomologyMap a A 2)
        (hhigh' 2 (by omega)) (hopen a)
        (fun x ↦ (cohomologyMap_map a 2 ε x).symm)).mpr (h a)
    · intro h W a _
      exact (surjective_iff_of_bijective_square (Sheaf.H.map ε 2)
        (Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map ε) 2)
        (cohomologyMap a B 2) (cohomologyMap a A 2)
        (hhigh' 2 (by omega)) (hopen a)
        (fun x ↦ (cohomologyMap_map a 2 ε x).symm)).mp (h a)
  rw [assertions_iff, assertions_iff]
  exact h₁.and (h₂.and (h₃.and (h₄.and (h₅.and (h₆.and (h₇.and h₈))))))

end AlgebraicGeometry.IsCurve
