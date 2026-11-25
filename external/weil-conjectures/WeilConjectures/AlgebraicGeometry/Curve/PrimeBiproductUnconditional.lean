/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions

import Mathlib.Algebra.Category.Grp.Biproducts

/-! # Componentwise curve assertions for finite biproducts

Source: Stacks Project, Theorem 03SC, proof; Lemma 0A5C
(blueprint: theorem-cohomology-curves). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts

private theorem biproduct_coordinates {C : Type*} [Category C] [Preadditive C]
    {ι : Type} [Finite ι] (G : ι → C) [HasBiproduct G] {H : C} (e : H ≅ ⨁ G)
    (F : C ⥤ AddCommGrpCat.{u + 1}) [F.Additive] :
    ∃ E : F.obj H ≃+ (∀ i, F.obj (G i)),
      ∀ x i, E x i = F.map (e.hom ≫ biproduct.π G i) x := by
  let d := AddCommGrpCat.biproductIsoPi (F.obj ∘ G)
  let c := F.mapBiproduct G
  let E := ((F.mapIso e) ≪≫ c ≪≫ d).addCommGroupIsoToAddEquiv
  refine ⟨E, ?_⟩
  intro x i
  have hd : d.hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun i ↦ F.obj (G i)) i) =
      biproduct.π (F.obj ∘ G) i := by
    rw [← AddCommGrpCat.biproductIsoPi_inv_comp_π]
    exact d.hom_inv_id_assoc _
  have hc : c.hom ≫ biproduct.π (F.obj ∘ G) i = F.map (biproduct.π G i) := by
    simp [c]
  change (F.map e.hom ≫ c.hom ≫ d.hom) x i = _
  change ((F.map e.hom ≫ c.hom ≫ d.hom) ≫
    AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun i ↦ F.obj (G i)) i)) x = _
  rw [Category.assoc, Category.assoc, hd, hc, ← F.map_comp]

private theorem biproduct_subsingleton_iff {C : Type*} [Category C] [Preadditive C]
    {ι : Type} [Finite ι] (G : ι → C) [HasBiproduct G] {H : C} (e : H ≅ ⨁ G)
    (F : C ⥤ AddCommGrpCat.{u + 1}) [F.Additive] :
    Subsingleton (F.obj H) ↔ ∀ i, Subsingleton (F.obj (G i)) := by
  classical
  obtain ⟨E, _⟩ := biproduct_coordinates G e F
  constructor
  · intro h i
    have : Subsingleton (∀ i, F.obj (G i)) := E.toEquiv.symm.subsingleton
    exact Function.Surjective.subsingleton
      (Function.surjective_eval (β := fun j ↦ ↥(F.obj (G j))) i)
  · intro h
    have : ∀ i, Subsingleton (F.obj (G i)) := h
    exact E.toEquiv.subsingleton

private theorem biproduct_finite_iff {C : Type*} [Category C] [Preadditive C]
    {ι : Type} [Finite ι] (G : ι → C) [HasBiproduct G] {H : C} (e : H ≅ ⨁ G)
    (F : C ⥤ AddCommGrpCat.{u + 1}) [F.Additive] :
    Finite (F.obj H) ↔ ∀ i, Finite (F.obj (G i)) := by
  classical
  obtain ⟨E, _⟩ := biproduct_coordinates G e F
  constructor
  · intro h i
    have : Finite (∀ i, F.obj (G i)) := Finite.of_equiv _ E.toEquiv
    exact Finite.of_surjective _ (Function.surjective_eval (β := fun j ↦ ↥(F.obj (G j))) i)
  · intro h
    have : ∀ i, Finite (F.obj (G i)) := h
    exact Finite.of_equiv _ E.toEquiv.symm

private theorem biproduct_surjective_iff {C : Type*} [Category C] [Preadditive C]
    {ι : Type} [Finite ι] (G : ι → C) [HasBiproduct G] {H : C} (e : H ≅ ⨁ G)
    {F Q : C ⥤ AddCommGrpCat.{u + 1}} [F.Additive] [Q.Additive] (τ : F ⟶ Q) :
    Function.Surjective (τ.app H) ↔ ∀ i, Function.Surjective (τ.app (G i)) := by
  classical
  obtain ⟨E, hE⟩ := biproduct_coordinates G e F
  obtain ⟨D, hD⟩ := biproduct_coordinates G e Q
  have hτ (x : F.obj H) (i : ι) : D (τ.app H x) i = τ.app (G i) (E x i) := by
    rw [hD, hE]
    exact (ConcreteCategory.congr_hom (τ.naturality (e.hom ≫ biproduct.π G i)) x).symm
  constructor
  · intro h i y
    obtain ⟨z, hz⟩ := D.surjective (Pi.single i y)
    obtain ⟨x, hx⟩ := h z
    refine ⟨E x i, ?_⟩
    rw [← hτ, hx, hz, Pi.single_eq_same]
  · intro h y
    obtain ⟨z, hz⟩ := Function.Surjective.piMap h (D y)
    obtain ⟨x, hx⟩ := E.surjective z
    refine ⟨x, D.injective ?_⟩
    funext i
    rw [hτ, hx]
    exact congrFun hz i

private theorem biproduct_injective_iff {C : Type*} [Category C] [Preadditive C]
    {ι : Type} [Finite ι] (G : ι → C) [HasBiproduct G] {H : C} (e : H ≅ ⨁ G)
    {F Q : C ⥤ AddCommGrpCat.{u + 1}} [F.Additive] [Q.Additive] (τ : F ⟶ Q) :
    Function.Injective (τ.app H) ↔ ∀ i, Function.Injective (τ.app (G i)) := by
  obtain ⟨E, hE⟩ := biproduct_coordinates G e F
  obtain ⟨D, hD⟩ := biproduct_coordinates G e Q
  have hτ (x : F.obj H) (i : ι) : D (τ.app H x) i = τ.app (G i) (E x i) := by
    rw [hD, hE]
    exact (ConcreteCategory.congr_hom (τ.naturality (e.hom ≫ biproduct.π G i)) x).symm
  constructor
  · intro h i x y hxy
    let j := biproduct.ι G i ≫ e.inv
    let p := e.hom ≫ biproduct.π G i
    have hjp : j ≫ p = 𝟙 (G i) := by simp [j, p]
    have h' : F.map j x = F.map j y := h (by
      have hn := ConcreteCategory.congr_hom (τ.naturality j)
      exact (hn x).trans ((congrArg (fun z ↦ Q.map j z) hxy).trans (hn y).symm))
    have h'' := congrArg (fun z ↦ F.map p z) h'
    simpa only [← AddCommGrpCat.comp_apply, ← F.map_comp, hjp, F.map_id,
      AddCommGrpCat.id_apply] using h''
  · intro h x y hxy
    apply E.injective
    funext i
    apply h i
    rw [← hτ, ← hτ, hxy]

private theorem biproduct_bijective_iff {C : Type*} [Category C] [Preadditive C]
    {ι : Type} [Finite ι] (G : ι → C) [HasBiproduct G] {H : C} (e : H ≅ ⨁ G)
    {F Q : C ⥤ AddCommGrpCat.{u + 1}} [F.Additive] [Q.Additive] (τ : F ⟶ Q) :
    Function.Bijective (τ.app H) ↔ ∀ i, Function.Bijective (τ.app (G i)) := by
  rw [Function.Bijective, biproduct_injective_iff G e τ,
    biproduct_surjective_iff G e τ]
  exact ⟨fun h i ↦ ⟨h.1 i, h.2 i⟩, fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩⟩

namespace AlgebraicGeometry.IsCurve

/-- Componentwise equivalence for the unconditional assertions of a finite sum.
Source: Stacks Project, Theorem 03SC, proof, fourth paragraph; Lemma 0A5C.
(blueprint: theorem-cohomology-curves).

Proof: The underlying abelian-sheaf functor is additive by definition, as are
`Sheaf.functorH` and inverse image. Apply `Functor.mapBiproduct` followed by
`AddCommGrpCat.biproductIsoPi` to identify the cohomology of H with the finite
product of the cohomology of G i. Its coordinates are the maps induced by
`e.hom ≫ biproduct.π G i`. A product is subsingleton iff every factor is, and
finite iff every factor is: evaluation is surjective since the factors contain
zero, and a finite product of finite types is finite.

Naturality `Etale.cohomologyMap_map` makes pullback a natural transformation
between the additive cohomology functors. Surjectivity is tested in product
coordinates, using vectors supported in one coordinate for the forward direction
and choosing coordinate preimages for the converse. For injectivity, each summand
is a retract via `biproduct.ι G i ≫ e.inv` and `e.hom ≫ biproduct.π G i`;
naturality gives the forward implication, and joint injectivity of coordinates
gives the converse. Bijectivity combines these two tests. Apply the tests degree
by degree to C1, C2, C5, C7 and C8. Properness and affineness are common hypotheses;
the supplied constructibility proofs discharge C5 in the respective directions.
Empty products are singletons, so the argument includes the empty index type.
No derived-global-sections comparison or constructibility closure theorem is used. -/
theorem prime_biproduct_unconditional_iff (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {ι : Type} [Finite ι]
    (G : ι → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hGc : ∀ a, Scheme.IsConstructibleSheaf (G a))
    {H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : H ≅ ⨁ G)
    (hHc : Scheme.IsConstructibleSheaf H) :
    (VanishingAboveTwo Λ H ∧ VanishingAboveOneOfIsAffine Λ H ∧
      FiniteOfIsProper Λ f H ∧ BaseChangeOfIsProper Λ f H ∧
      SurjectiveRestrictionTwo Λ H) ↔
      ∀ a, VanishingAboveTwo Λ (G a) ∧ VanishingAboveOneOfIsAffine Λ (G a) ∧
        FiniteOfIsProper Λ f (G a) ∧ BaseChangeOfIsProper Λ f (G a) ∧
        SurjectiveRestrictionTwo Λ (G a) := by
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : U.Additive := ⟨by intros; rfl⟩
  have hV (q : ℕ) : Subsingleton (Sheaf.H (U.obj H) q) ↔
      ∀ i, Subsingleton (Sheaf.H (U.obj (G i)) q) :=
    biproduct_subsingleton_iff G e (U ⋙ Sheaf.functorH _ q)
  have hF (q : ℕ) : Finite (Sheaf.H (U.obj H) q) ↔
      ∀ i, Finite (Sheaf.H (U.obj (G i)) q) :=
    biproduct_finite_iff G e (U ⋙ Sheaf.functorH _ q)
  have hM {Y : Scheme.{u}} (a : Y ⟶ X) (q : ℕ) :
      (Function.Bijective (Etale.cohomologyMap a (U.obj H) q) ↔
        ∀ i, Function.Bijective (Etale.cohomologyMap a (U.obj (G i)) q)) ∧
      (Function.Surjective (Etale.cohomologyMap a (U.obj H) q) ↔
        ∀ i, Function.Surjective (Etale.cohomologyMap a (U.obj (G i)) q)) := by
    let L := U ⋙ Sheaf.functorH X.smallEtaleTopology q
    let R := U ⋙ Etale.upperStar AddCommGrpCat.{u + 1} a ⋙ Sheaf.functorH Y.smallEtaleTopology q
    let τ : L ⟶ R :=
      { app := fun K ↦ AddCommGrpCat.ofHom (Etale.cohomologyMap a (U.obj K) q)
        naturality := by
          intro K K' φ
          ext x
          exact Etale.cohomologyMap_map a q (U.map φ) x }
    exact ⟨biproduct_bijective_iff G e τ, biproduct_surjective_iff G e τ⟩
  constructor
  · rintro ⟨h₁, h₂, h₅, h₇, h₈⟩ i
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      exact (hV q).mp (h₁ q hq) i
    · intro _ q hq
      exact (hV q).mp (h₂ q hq) i
    · intro _ _ q
      have : Scheme.IsConstructibleSheaf H := hHc
      exact (hF q).mp (h₅ q) i
    · intro _ k' _ _ X' b f' a hp q
      exact (hM a q).1.mp (h₇ k' hp q) i
    · intro W a _
      exact (hM a 2).2.mp (h₈ a) i
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      exact (hV q).mpr (fun i ↦ (h i).1 q hq)
    · intro _ q hq
      exact (hV q).mpr (fun i ↦ (h i).2.1 q hq)
    · intro _ _ q
      apply (hF q).mpr
      intro i
      have : Scheme.IsConstructibleSheaf (G i) := hGc i
      exact (h i).2.2.1 q
    · intro _ k' _ _ X' b f' a hp q
      exact (hM a q).1.mpr (fun i ↦ (h i).2.2.2.1 k' hp q)
    · intro W a _
      exact (hM a 2).2.mpr (fun i ↦ (h i).2.2.2.2 a)

end AlgebraicGeometry.IsCurve
