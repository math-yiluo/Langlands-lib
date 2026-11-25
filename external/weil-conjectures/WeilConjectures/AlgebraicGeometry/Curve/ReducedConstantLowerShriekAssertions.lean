/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
import WeilConjectures.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction

/-! # Constant prime coefficients extended by zero on reduced curves

Source: Stacks Project, Lemmas 03SG (lemma-even-easier) and 0A3Q
(lemma-somewhat-easier).
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

private theorem comparison_surjective_of_iso {X Y : Scheme.{u}} (a : Y ⟶ X)
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

private theorem comparison_bijective_of_iso {X Y : Scheme.{u}} (a : Y ⟶ X)
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

private theorem assertions_of_iso {Λ : Type (u + 1)} [CommRing Λ]
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : F ≅ G)
    (h : Assertions Λ f F) : Assertions Λ f G := by
  let eA := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
    AddCommGrpCat.{u + 1})).mapIso e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    let := h.subsingleton_of_two_lt q hq
    exact (cohomologyEquiv eA q).symm.injective.subsingleton
  · intro _ q hq
    let := h.subsingleton_of_one_lt_of_isAffine q hq
    exact (cohomologyEquiv eA q).symm.injective.subsingleton
  · intro p _ _ hG q hq
    have hF : Scheme.IsPrimaryTorsionSheaf Λ F p := by
      intro Ω _ _ s x
      let es := (Scheme.pointSmallEtale s).sheafFiber.mapIso e
      obtain ⟨n, hn⟩ := hG Ω s (es.hom.hom x)
      refine ⟨n, ?_⟩
      apply (ModuleCat.mono_iff_injective es.hom).mp inferInstance
      simpa using hn
    let := h.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p hF q hq
    exact (cohomologyEquiv eA q).symm.injective.subsingleton
  · intro _ _ q
    let : Scheme.IsConstructibleSheaf F := Scheme.IsConstructibleSheaf.of_iso e.symm
    let : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F :=
      Scheme.IsTorsionSheafOfInvertibleOrder.of_iso Λ e.symm
    let := h.finite_of_isTorsionSheafOfInvertibleOrder q
    exact Finite.of_injective _ (cohomologyEquiv eA q).symm.injective
  · intro _ _ q
    let : Scheme.IsConstructibleSheaf F := Scheme.IsConstructibleSheaf.of_iso e.symm
    let := h.finite_of_isProper q
    exact Finite.of_injective _ (cohomologyEquiv eA q).symm.injective
  · intro _ k' _ _ X' ι f' ι' hp q
    let : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F :=
      Scheme.IsTorsionSheafOfInvertibleOrder.of_iso Λ e.symm
    exact comparison_bijective_of_iso ι' eA q
      (h.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' hp q)
  · intro _ k' _ _ X' ι f' ι' hp q
    exact comparison_bijective_of_iso ι' eA q
      (h.bijective_cohomologyMap_of_isProper k' hp q)
  · intro W a _
    exact comparison_surjective_of_iso a eA 2
      (h.surjective_cohomologyMap_of_isOpenImmersion a)

/-- Constant prime coefficients extended by zero on a reduced curve.

Source: Stacks Project, 03SG (lemma-even-easier), 0A3Q (lemma-somewhat-easier),
0A5B (lemma-constant-smooth-statements), 0GJA (lemma-restrict-to-open).
(blueprint: k1-reduced-constant-lower-shriek-assertions)

Proof:
1. On a smooth curve, split into its finitely many disjoint irreducible components.
Smooth local rings are domains, so distinct components cannot intersect; Noetherianity
makes the components open as well as closed. On each component an open is either empty
or dense. The empty case has zero extension by zero. In the dense case apply the
Kummer calculations if r is invertible in k and the Artin--Schreier calculations
otherwise (0A5B), followed by dense-open localization (0GJA). Finite pushforward from
components and short-exact devissage reassemble their finite direct sum (03SG).
Points are included: their positive cohomology vanishes and degree zero is the stalk.
2. For a reduced curve choose the finite smooth modification nu : Xn -> X,
isomorphic over a dense open D, supplied by reduced-curve normalization. Pull j back
to jn on Xn. Step 1 gives the assertions for jn_! R; finite pushforward (0A5D,
lemma-finite-pushforward) gives them for nu_* jn_! R.
3. Both nu_* jn_! R and j_! R are constructible: the latter is constant on U and
zero on its complement, and finite pushforward preserves constructibility. Over D
they agree, because nu is an isomorphism there and the stalk description of extension
by zero commutes with restriction to opens. Apply 0GJA twice to transfer the assertions
between these two sheaves (0A3Q).
4. All sheaves have their canonical R = ULift(ZMod r) module structure. The constant
sheaf R is the constant prime-field sheaf used in the cited calculations, since r = 0
in R. Forgetting modules preserves the stalk formulas and the cohomology comparison
maps, so this proves the stated module-valued assertion package. -/
theorem reducedConstantLowerShriekAssertions {k : Type u} [Field k] [IsAlgClosed k]
    {X U : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (r : ℕ) [Fact r.Prime] :
    IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj
        ((constantSheaf U.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod r))))) := by
  obtain ⟨e⟩ := constantModSheaf_iso_constantSheaf (U := U) r
  apply assertions_of_iso f ((Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).mapIso e)
  exact reducedConstantLowerShriekAssertions_of_reduction_data f j r
    (exists_reducedConstantLowerShriekReductionData f j r)

end AlgebraicGeometry.IsCurve
