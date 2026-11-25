/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import Mathlib.Algebra.Category.Grp.Biproducts
import WeilConjectures.AlgebraicGeometry.Curve.PrimeAnnihilatedInvertibleCases

/-! # Componentwise curve assertions for finite biproducts

Source: Stacks Project, Theorem 03SC, proof; Lemma 0A5C
(blueprint: lem-pbc-f1-prime-biproduct-invertible). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.IsCurve

private noncomputable def sumEquiv
    {C : Type*} [Category C] [Preadditive C]
    (T : C ⥤ AddCommGrpCat.{u + 1}) [T.Additive]
    {ι : Type} [Finite ι] (G : ι → C) [HasBiproduct G]
    {H : C} (e : H ≅ ⨁ G) : T.obj H ≃ (∀ a, T.obj (G a)) :=
  (T.mapIso e ≪≫ T.mapBiproduct G ≪≫
    AddCommGrpCat.biproductIsoPi _).addCommGroupIsoToAddEquiv.toEquiv

private theorem sumEquiv_apply
    {C : Type*} [Category C] [Preadditive C]
    (T : C ⥤ AddCommGrpCat.{u + 1}) [T.Additive]
    {ι : Type} [Finite ι] (G : ι → C) [HasBiproduct G]
    {H : C} (e : H ≅ ⨁ G) (x : T.obj H) (a : ι) :
    sumEquiv T G e x a = T.map (e.hom ≫ biproduct.π G a) x := by
  have hp : (AddCommGrpCat.biproductIsoPi (fun a ↦ T.obj (G a))).hom ≫
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun a ↦ T.obj (G a)) a) =
      biproduct.π _ a := by
    rw [← AddCommGrpCat.biproductIsoPi_inv_comp_π]
    simp only [Iso.hom_inv_id_assoc]
  change ((T.mapIso e ≪≫ T.mapBiproduct G ≪≫
    AddCommGrpCat.biproductIsoPi _).hom ≫ AddCommGrpCat.ofHom
      (Pi.evalAddMonoidHom (fun a ↦ T.obj (G a)) a)) x = _
  rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc]
  simp only [Function.comp_def]
  rw [hp,
    Functor.mapBiproduct_hom]
  simp only [biproduct.lift_π, ← T.map_comp, Functor.mapIso_hom]

private theorem finite_sum_iff
    {C : Type*} [Category C] [Preadditive C]
    (T : C ⥤ AddCommGrpCat.{u + 1}) [T.Additive]
    {ι : Type} [Finite ι] (G : ι → C) [HasBiproduct G]
    {H : C} (e : H ≅ ⨁ G) : Finite (T.obj H) ↔ ∀ a, Finite (T.obj (G a)) := by
  constructor
  · intro h a
    let := h
    apply Finite.of_injective (T.map (biproduct.ι G a ≫ e.inv))
    apply Function.LeftInverse.injective
      (g := T.map (e.hom ≫ biproduct.π G a))
    intro x
    rw [← ConcreteCategory.comp_apply, ← T.map_comp]
    simp
  · intro h
    let := h
    exact Finite.of_equiv _ (sumEquiv T G e).symm

private theorem bijective_pi_iff {ι : Type} {A B : ι → Type*}
    [∀ a, AddCommGroup (A a)] [∀ a, AddCommGroup (B a)]
    (c : ∀ a, A a →+ B a) :
    Function.Bijective (fun (x : ∀ a, A a) a ↦ c a (x a)) ↔ ∀ a, Function.Bijective (c a) := by
  classical
  constructor
  · intro h a
    constructor
    · intro x y hxy
      have he : (fun b ↦ c b (Function.update (0 : ∀ a, A a) a x b)) =
          (fun b ↦ c b (Function.update (0 : ∀ a, A a) a y b)) := by
        funext b
        by_cases hb : b = a
        · subst b
          simpa using hxy
        · simp [hb]
      have := congrFun (h.1 he) a
      simpa using this
    · intro y
      obtain ⟨x, hx⟩ := h.2 (Function.update (0 : ∀ a, B a) a y)
      exact ⟨x a, by simpa using congrFun hx a⟩
  · intro h
    constructor
    · intro x y hxy
      funext a
      exact (h a).1 (congrFun hxy a)
    · intro y
      choose x hx using fun a ↦ (h a).2 (y a)
      exact ⟨x, funext hx⟩

private theorem bijective_sum_iff
    {C : Type*} [Category C] [Preadditive C]
    (T S : C ⥤ AddCommGrpCat.{u + 1}) [T.Additive] [S.Additive]
    (η : T ⟶ S) {ι : Type} [Finite ι] (G : ι → C) [HasBiproduct G]
    {H : C} (e : H ≅ ⨁ G) :
    Function.Bijective (η.app H) ↔ ∀ a, Function.Bijective (η.app (G a)) := by
  have hc (x : T.obj H) : sumEquiv S G e (η.app H x) =
      fun a ↦ η.app (G a) (sumEquiv T G e x a) := by
    funext a
    rw [sumEquiv_apply, sumEquiv_apply]
    exact (ConcreteCategory.congr_hom (η.naturality (e.hom ≫ biproduct.π G a)) x).symm
  have he : (fun (x : ∀ a, T.obj (G a)) a ↦ η.app (G a) (x a)) =
      sumEquiv S G e ∘ η.app H ∘ (sumEquiv T G e).symm := by
    funext x
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      (hc ((sumEquiv T G e).symm x)).symm
  rw [← bijective_pi_iff (fun a ↦ (η.app (G a)).hom), he]
  constructor
  · intro h
    exact (sumEquiv S G e).bijective.comp (h.comp (sumEquiv T G e).symm.bijective)
  · intro h
    have hi : Function.Injective (η.app H) := by
      intro x y hxy
      apply (sumEquiv T G e).injective
      apply h.1
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
        congrArg (sumEquiv S G e) hxy
    refine ⟨hi, ?_⟩
    intro y
    obtain ⟨x, hx⟩ := h.2 (sumEquiv S G e y)
    exact ⟨(sumEquiv T G e).symm x, (sumEquiv S G e).injective hx⟩

private theorem cohomology_bijective_sum_iff (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (a : Y ⟶ X) {ι : Type} [Finite ι]
    (G : ι → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : H ≅ ⨁ G) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap a
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj H) q) ↔
    ∀ i, Function.Bijective (Etale.cohomologyMap a
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj (G i)) q) := by
  let A := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : A.Additive := { map_add := by intros; rfl }
  let T := A ⋙ Sheaf.functorH X.smallEtaleTopology q
  let S := A ⋙ Etale.upperStar AddCommGrpCat.{u + 1} a ⋙ Sheaf.functorH Y.smallEtaleTopology q
  let η : T ⟶ S :=
    { app := fun F ↦ AddCommGrpCat.ofHom (Etale.cohomologyMap a (A.obj F) q)
      naturality := by
        intro F F' φ
        ext x
        exact Etale.cohomologyMap_map a q (A.map φ) x }
  exact bijective_sum_iff T S η G e

/-- Componentwise equivalence for the invertible assertions of a prime-killed finite sum.
Source: Stacks Project, Theorem 03SC, proof, fourth paragraph; Lemma 0A5C.
(blueprint: lem-pbc-f1-prime-biproduct-invertible).

Proof: If r is invertible in k, every stalk of each G a and H has invertible-order
torsion, since r kills it. The given constructibility hypotheses
supply the C4 hypotheses for H and every component. Cohomology and inverse image
are additive and comparison maps natural, so finiteness and bijectivity are equivalent to the same
properties for all components. This proves both C4 and C6 in this case. If r is
not invertible in the field k, the characteristic is r. Any r-killed sheaf with
invertible-order torsion has zero stalks: each stalk element is killed by r and
by an integer invertible in k, hence coprime to r; Bezout then kills it by 1.
Stalk conservativity makes it the zero sheaf. Its cohomology is zero, finite,
and all comparison maps bijective. This proves all exceptional conditional
assertions for H and for any individual component. Empty sums are zero.
The cohomology here is Mathlib's Ext-based `Sheaf.H`: its coefficient functor is
additive, so `Functor.mapBiproduct` followed by `AddCommGrpCat.biproductIsoPi`
identifies its value with the finite product of component groups. No derived-global-sections
bridge is needed. The product identification sends a class to its images under
the projections, with inverse the sum of its images under the injections. Thus vanishing
is tested coordinatewise.
For a scheme map a, naturality `Etale.cohomologyMap_map` with each injection and
projection identifies the comparison with the product of component comparisons.
Injectivity is tested on one coordinate at a time. Surjectivity follows by choosing
preimages for each coordinate and summing the injections; conversely a preimage of
a vector supported in one coordinate gives a preimage in that component. A finite
product is finite iff each factor is finite (each factor is a retract, and all
cohomology groups contain zero). This also proves the asserted finiteness tests. -/
theorem prime_biproduct_invertible_iff (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (r : ℕ) [Fact r.Prime] {ι : Type} [Finite ι]
    (G : ι → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hGc : ∀ a, Scheme.IsConstructibleSheaf (G a)) (hGr : ∀ a, r • 𝟙 (G a) = 0)
    {H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : H ≅ ⨁ G)
    (hHr : r • 𝟙 H = 0)
    (hHc : Scheme.IsConstructibleSheaf H) :
    (FiniteOfInvertibleOrder Λ H k ∧ BaseChangeOfInvertibleOrder Λ f H) ↔
      ∀ a, FiniteOfInvertibleOrder Λ (G a) k ∧
        BaseChangeOfInvertibleOrder Λ f (G a) := by
  classical
  let A := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : A.Additive := { map_add := by intros; rfl }
  have hfinite (q : ℕ) : Finite (Sheaf.H (A.obj H) q) ↔
      ∀ a, Finite (Sheaf.H (A.obj (G a)) q) :=
    finite_sum_iff (A ⋙ Sheaf.functorH X.smallEtaleTopology q) G e
  have hInvH := Scheme.prime_annihilated_invertible_cases Λ (k := k) r H hHr
  have hInvG (a : ι) :=
    Scheme.prime_annihilated_invertible_cases Λ (k := k) r (G a) (hGr a)
  by_cases hr : IsUnit (r : Γ(Spec (.of k), ⊤))
  · have := hInvH.1 hr
    have (a : ι) := (hInvG a).1 hr
    have := hHc
    have (a : ι) := hGc a
    constructor
    · intro h a
      constructor
      · intro _ _ q
        exact (hfinite q).mp (h.1 q) a
      · intro _ k' _ _ X' ι' f' a' hp q
        exact (cohomology_bijective_sum_iff Λ a' G e q).mp (h.2 k' hp q) a
    · intro h
      constructor
      · intro _ _ q
        exact (hfinite q).mpr (fun a ↦ (h a).1 q)
      · intro _ k' _ _ X' ι' f' a' hp q
        exact (cohomology_bijective_sum_iff Λ a' G e q).mpr
          (fun a ↦ (h a).2 k' hp q)
  · have hz (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (hF : r • 𝟙 F = 0) :
        FiniteOfInvertibleOrder Λ F k ∧ BaseChangeOfInvertibleOrder Λ f F := by
      constructor
      · intro _ _ q
        have hzero := (Scheme.prime_annihilated_invertible_cases Λ (k := k) r F hF).2
          hr inferInstance
        have hh := Sheaf.subsingleton_H_of_isZero (A.map_isZero hzero) q
        let := hh
        infer_instance
      · intro _ k' _ _ X' ι' f' a' hp q
        have hzero := (Scheme.prime_annihilated_invertible_cases Λ (k := k) r F hF).2
          hr inferInstance
        have hA := A.map_isZero hzero
        have hB := (Etale.upperStar AddCommGrpCat.{u + 1} a').map_isZero hA
        have := Sheaf.subsingleton_H_of_isZero hA q
        have := Sheaf.subsingleton_H_of_isZero hB q
        exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    exact ⟨fun _ a ↦ hz (G a) (hGr a), fun _ ↦ hz H hHr⟩

end AlgebraicGeometry.IsCurve
