/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.AlgebraicGeometry.Curve.PrimeAnnihilatedPrimaryCases

/-! # Componentwise curve assertions for finite biproducts

Source: Stacks Project, Theorem 03SC, proof; Lemma 0A5C
(blueprint: lem-pbc-f1-prime-biproduct-primary). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.IsCurve

-- The base morphism is unused, but belongs to the existing public signature.
set_option linter.unusedVariables false in
/-- Componentwise equivalence for the primary assertions of a prime-killed finite sum.
Source: Stacks Project, Theorem 03SC, proof, fourth paragraph; Lemma 0A5C.
(blueprint: lem-pbc-f1-prime-biproduct-primary).

Proof: At any geometric stalk, all components and H are killed by r. For a prime p
which is the characteristic of k, if p = r every component and H is p-primary.
The C3 conditions then say vanishing of the same cohomology degrees, which is
componentwise by additivity. If p differs from r, any p-primary r-killed stalk
is zero: for each element, Bezout for the coprime integers r and p^n expresses
1 as an integer combination of its two annihilators. Conservativity of geometric
stalks makes any sheaf satisfying this exceptional hypothesis zero. Hence the C3
conclusion is automatic, both when that hypothesis holds for a component and
when it holds for H. Transport cohomology and stalks along e. The empty sum is
zero, and its C3 assertion and the empty universal quantifier are both true.
The cohomology here is Mathlib's Ext-based `Sheaf.H`: its coefficient functor is
additive, and `Abelian.Ext.addEquivBiproduct` identifies it with the finite product
of component groups. No derived-global-sections bridge is needed. The product
identification sends a class to its images under the projections, with inverse
the sum of its images under the injections. Thus vanishing is tested coordinatewise. -/
theorem prime_biproduct_primary_iff (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (r : ℕ) [Fact r.Prime] {ι : Type} [Finite ι]
    (G : ι → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hGr : ∀ a, r • 𝟙 (G a) = 0)
    {H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : H ≅ ⨁ G)
    (hHr : r • 𝟙 H = 0) :
    VanishingAboveOneOfIsPrimaryTorsionSheaf Λ H k ↔
      ∀ a, VanishingAboveOneOfIsPrimaryTorsionSheaf Λ (G a) k := by
  classical
  have := Fintype.ofFinite ι
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : U.Additive := { map_add := by intros; rfl }
  have hvan (q : ℕ) : Subsingleton (Sheaf.H (U.obj H) q) ↔
      ∀ a, Subsingleton (Sheaf.H (U.obj (G a)) q) := by
    let T := U ⋙ Sheaf.functorH X.smallEtaleTopology q
    change Subsingleton (T.obj H) ↔ ∀ a, Subsingleton (T.obj (G a))
    constructor
    · intro h a
      have hz : IsZero (T.obj H) := AddCommGrpCat.isZero_iff_subsingleton.mpr h
      apply AddCommGrpCat.subsingleton_of_isZero
      apply (IsZero.iff_id_eq_zero _).mpr
      calc
        𝟙 (T.obj (G a)) =
            T.map (biproduct.ι G a ≫ e.inv) ≫
              T.map (e.hom ≫ biproduct.π G a) := by
          rw [← T.map_comp]
          simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_self, T.map_id]
        _ = 0 := by rw [hz.eq_zero_of_src (T.map (e.hom ≫ biproduct.π G a)), comp_zero]
    · intro h
      have hz (a : ι) : IsZero (T.obj (G a)) :=
        AddCommGrpCat.isZero_iff_subsingleton.mpr (h a)
      apply AddCommGrpCat.subsingleton_of_isZero
      apply (IsZero.iff_id_eq_zero _).mpr
      have hb : 𝟙 (T.obj (⨁ G)) = 0 := by
        rw [← T.map_id, ← IsBilimit.total (biproduct.isBilimit G), T.map_sum]
        apply Finset.sum_eq_zero
        intro a _
        rw [T.map_comp, (hz a).eq_zero_of_src (T.map (biproduct.ι G a)), comp_zero]
      calc
        𝟙 (T.obj H) = T.map e.hom ≫ 𝟙 (T.obj (⨁ G)) ≫ T.map e.inv := by
          simp only [Category.id_comp, ← T.map_comp, Iso.hom_inv_id, T.map_id]
        _ = 0 := by rw [hb, zero_comp, comp_zero]
  have hH := Scheme.prime_annihilated_primary_cases Λ r H hHr
  have hG (a : ι) := Scheme.prime_annihilated_primary_cases Λ r (G a) (hGr a)
  constructor
  · intro h a p _ _ hp q hq
    by_cases hrp : r = p
    · subst p
      exact (hvan q).mp (h r hH.1 q hq) a
    · exact Sheaf.subsingleton_H_of_isZero (U.map_isZero ((hG a).2 p hrp hp)) q
  · intro h p _ _ hp q hq
    by_cases hrp : r = p
    · subst p
      exact (hvan q).mpr (fun a ↦ h a r (hG a).1 q hq)
    · exact Sheaf.subsingleton_H_of_isZero (U.map_isZero (hH.2 p hrp hp)) q

end AlgebraicGeometry.IsCurve
