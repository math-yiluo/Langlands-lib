/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.Curve.Reductions
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
import WeilConjectures.SixFunctors.Etale.Gabber

/-! # Constant-quotient filtration induction steps

Source: Stacks Project, etale-cohomology.tex, 03SD and 0A5C.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

/-- The zero case and successor step for extension by zero of a constant-quotient
filtration. This states only local induction steps, not the terminal assertion.

Source: Stacks Project 03SD (lemma-vanishing-easier), final paragraph;
0A5C (lemma-ses-statements).
(blueprint: r1-open-lower-shriek-constant-filtration-steps)

Proof: Extension by zero is exact and additive, so it sends the zero first term
to a zero sheaf. All its cohomology groups vanish. Its pullbacks are also zero,
so both field-extension maps are bijective and the degree-two restriction map
is surjective. Thus the eight assertions hold at zero. For each monomorphism
W_i -> W_(i+1), the cokernel sequence is short exact in the abelian sheaf
category. Exact extension by zero preserves it. The specified cokernel
isomorphism identifies its third term with a_! R. Transport the constant-case
assertions along that isomorphism and apply short-exact assertion devissage
(Assertions.of_shortExact). The prime coefficient ring is Noetherian, as
required there. The case n=0 has no successor condition. -/
theorem open_lowerShriek_constant_filtration_steps
    {k : Type u} [Field k] [IsAlgClosed k] {Y V : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsCurve g] (a : V ⟶ Y) [IsOpenImmersion a]
    (r : ℕ) [Fact r.Prime] (n : ℕ)
    (W : ℕ → Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    (ι : ∀ i, W i ⟶ W (i + 1)) (hzero : IsZero (W 0))
    (hquot : ∀ i < n, Mono (ι i) ∧ Nonempty (cokernel (ι i) ≅
      (constantSheaf V.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod r)))))
    (hconstant : Assertions (ULift.{u + 1} (ZMod r)) g
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) a).obj
        ((constantSheaf V.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod r)))))) :
    Assertions (ULift.{u + 1} (ZMod r)) g
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) a).obj
        (W 0)) ∧
    ∀ i < n,
      Assertions (ULift.{u + 1} (ZMod r)) g
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) a).obj
          (W i)) →
      Assertions (ULift.{u + 1} (ZMod r)) g
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) a).obj
          (W (i + 1))) := by
  let cohomologyEquiv : ∀ {X : Scheme.{u}}
      {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}},
      (F ≅ G) → (q : ℕ) → Sheaf.H F q ≃ Sheaf.H G q :=
    fun {X} {F G} e q =>
      { toFun := Sheaf.H.map e.hom q
        invFun := Sheaf.H.map e.inv q
        left_inv := fun x => by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id]; simp
        right_inv := fun x => by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id]; simp }
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
  
  have assertions_of_iso {Λ : Type (u + 1)} [CommRing Λ]
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
  
  let L := Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) a
  constructor
  · have hz := Functor.map_isZero L hzero
    let B := (sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})).obj
      (L.obj (W 0))
    have hB : IsZero B := Functor.map_isZero
      (sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})) hz
    have hsub (q : ℕ) : Subsingleton (Sheaf.H B q) :=
      Sheaf.subsingleton_H_of_isZero hB q
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q _; exact hsub q
    · intro _ q _; exact hsub q
    · intro p _ _ _ q _; exact hsub q
    · intro _ _ q; have := hsub q; infer_instance
    · intro _ _ q; have := hsub q; infer_instance
    · intro _ k' _ _ X' b g' b' _ q
      have := hsub q
      have : Subsingleton (Sheaf.H ((Etale.upperStar _ b').obj B) q) :=
        Sheaf.subsingleton_H_of_isZero
          (Functor.map_isZero (Etale.upperStar AddCommGrpCat.{u + 1} b') hB) q
      exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    · intro _ k' _ _ X' b g' b' _ q
      have := hsub q
      have : Subsingleton (Sheaf.H ((Etale.upperStar _ b').obj B) q) :=
        Sheaf.subsingleton_H_of_isZero
          (Functor.map_isZero (Etale.upperStar AddCommGrpCat.{u + 1} b') hB) q
      exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    · intro T b _
      have : Subsingleton (Sheaf.H ((Etale.upperStar _ b).obj B) 2) :=
        Sheaf.subsingleton_H_of_isZero
          (Functor.map_isZero (Etale.upperStar AddCommGrpCat.{u + 1} b) hB) 2
      exact fun y ↦ ⟨0, Subsingleton.elim _ _⟩
  · intro i hi hWi
    obtain ⟨hmono, ⟨e⟩⟩ := hquot i hi
    have : Mono (ι i) := hmono
    let S := ShortComplex.mk (ι i) (cokernel.π (ι i)) (cokernel.condition (ι i))
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (ι i) }
    have hSL : (S.map L).ShortExact := hS.map L
    apply Assertions.of_shortExact (ULift.{u + 1} (ZMod r)) g hSL hWi
    exact assertions_of_iso g (L.mapIso e).symm hconstant
  
end AlgebraicGeometry.IsCurve
