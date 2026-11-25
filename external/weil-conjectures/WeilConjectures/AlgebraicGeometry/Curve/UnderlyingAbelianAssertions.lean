/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import Mathlib.CategoryTheory.Sites.Point.Basic

/-! # Changing scalars in the curve assertions

Source: Stacks Project, Theorem 03SC, second proof paragraph. Cohomology is taken
on the underlying abelian sheaf, so only the stalkwise torsion hypotheses need comparison.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.IsCurve

private noncomputable def cohomologyEquiv {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ) :
    Sheaf.H F q ≃ Sheaf.H G q where
  toFun := Sheaf.H.map e.hom q
  invFun := Sheaf.H.map e.inv q
  left_inv x := by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id]; simp
  right_inv x := by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id]; simp

private noncomputable def stalkAddEquiv
    {Λ R : Type (u + 1)} [CommRing Λ] [CommRing R] {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (e : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj G ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    ↥(((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)).obj G) ≃+
      ↥(((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := Scheme.pointSmallEtale s
  let eR := (Φ.sheafFiberCompIso
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).app G
  let eΛ := (Φ.sheafFiberCompIso
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app F
  exact (eR.symm ≪≫ Φ.sheafFiber.mapIso e ≪≫ eΛ).addCommGroupIsoToAddEquiv

private theorem invertibleOrder_of_underlying_iso
    {Λ R : Type (u + 1)} [CommRing Λ] [CommRing R] {X B : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (e : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj G ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)
    [Scheme.IsTorsionSheafOfInvertibleOrder B F] :
    Scheme.IsTorsionSheafOfInvertibleOrder B G := by
  constructor
  intro Ω _ _ s x
  let es := stalkAddEquiv e Ω s
  obtain ⟨n, hn, hu, hx⟩ :=
    Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
      (S := B) Ω s (es x)
  refine ⟨n, hn, hu, es.injective ?_⟩
  simpa only [map_nsmul, map_zero] using hx

/-- The conditional curve assertions depend only on the underlying abelian sheaf
when both coefficient sheaves are constructible.
Source: Stacks Project, Theorem 03SC, second proof paragraph; Lemma 0A5C.
(blueprint: theorem-cohomology-curves)

Proof: An isomorphism of underlying abelian sheaves induces isomorphisms on every
cohomology group and on every geometric stalk. Forgetting module scalars commutes
with stalks because it preserves filtered colimits. Thus primary torsion and
invertible-order torsion pass along the stalk isomorphisms. For C1--C3 transfer
subsingleton cohomology along the induced equivalence; for C4--C5 transfer finiteness,
using the assumed constructibility on each side. For C6--C8 naturality identifies
the comparison map with the original comparison conjugated by the cohomology
isomorphisms on source and pullback. Bijectivity and surjectivity survive conjugation.
No curve, reducedness, finiteness of the rings, or characteristic assumption is needed. -/
theorem assertions_of_underlying_abelian_iso
    {Λ R : Type (u + 1)} [CommRing Λ] [CommRing R] {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    [Scheme.IsConstructibleSheaf F] [Scheme.IsConstructibleSheaf G]
    (e : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj G ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)
    (h : Assertions R f G) : Assertions Λ f F := by
  have comparison_surjective_of_iso {X Y : Scheme.{u}} (a : Y ⟶ X)
      {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ)
      (h : Function.Surjective (Etale.cohomologyMap a F q)) :
      Function.Surjective (Etale.cohomologyMap a G q) := by
    let eX := cohomologyEquiv e q
    let eY := cohomologyEquiv ((Etale.upperStar _ a).mapIso e) q
    have eq : Etale.cohomologyMap a G q =
        eY ∘ Etale.cohomologyMap a F q ∘ eX.symm := by
      funext x
      change Etale.cohomologyMap a G q x =
        Sheaf.H.map ((Etale.upperStar _ a).map e.hom) q
          (Etale.cohomologyMap a F q (Sheaf.H.map e.inv q x))
      rw [← Etale.cohomologyMap_map, ← Sheaf.H.map_comp_apply, e.inv_hom_id]
      simp
    rw [eq]
    exact eY.surjective.comp (h.comp eX.symm.surjective)
  have comparison_bijective_of_iso {X Y : Scheme.{u}} (a : Y ⟶ X)
      {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ)
      (h : Function.Bijective (Etale.cohomologyMap a F q)) :
      Function.Bijective (Etale.cohomologyMap a G q) := by
    refine ⟨?_, comparison_surjective_of_iso a e q h.2⟩
    intro x y hxy
    apply (cohomologyEquiv e.symm q).injective
    apply h.1
    change Etale.cohomologyMap a F q (Sheaf.H.map e.inv q x) =
      Etale.cohomologyMap a F q (Sheaf.H.map e.inv q y)
    simpa only [Etale.cohomologyMap_map] using
      congrArg (Sheaf.H.map ((Etale.upperStar _ a).map e.inv) q) hxy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have := h.subsingleton_of_two_lt q hq
    exact (cohomologyEquiv e q).symm.injective.subsingleton
  · intro _ q hq
    have := h.subsingleton_of_one_lt_of_isAffine q hq
    exact (cohomologyEquiv e q).symm.injective.subsingleton
  · intro p _ _ hF q hq
    have hG : Scheme.IsPrimaryTorsionSheaf R G p := by
      intro Ω _ _ s x
      let es := stalkAddEquiv e Ω s
      obtain ⟨n, hn⟩ := hF Ω s (es x)
      refine ⟨n, es.injective ?_⟩
      simpa only [map_nsmul, map_zero] using hn
    have := h.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p hG q hq
    exact (cohomologyEquiv e q).symm.injective.subsingleton
  · intro _ _ q
    have := invertibleOrder_of_underlying_iso (B := Spec (.of k)) e
    have := h.finite_of_isTorsionSheafOfInvertibleOrder q
    exact Finite.of_injective _ (cohomologyEquiv e q).symm.injective
  · intro _ _ q
    have := h.finite_of_isProper q
    exact Finite.of_injective _ (cohomologyEquiv e q).symm.injective
  · intro _ k' _ _ X' ι f' ι' hp q
    have := invertibleOrder_of_underlying_iso (B := Spec (.of k)) e
    exact comparison_bijective_of_iso ι' e q
      (h.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' hp q)
  · intro _ k' _ _ X' ι f' ι' hp q
    exact comparison_bijective_of_iso ι' e q
      (h.bijective_cohomologyMap_of_isProper k' hp q)
  · intro W a _
    exact comparison_surjective_of_iso a e 2
      (h.surjective_cohomologyMap_of_isOpenImmersion a)

end AlgebraicGeometry.IsCurve
