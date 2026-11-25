/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SectionFractionPresentation

/-! # Restriction and division of section fractions

Source: Stacks Project, Properties, Lemma 01PW (lemma-invert-s-sections), canonical map.
(blueprint: lem-sc-p1-section-fraction-restriction-map)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite DirectSum

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction followed by division by a free generator descends to the fraction quotient.
Source: Stacks Project, Properties, Lemma 01PW (lemma-invert-s-sections), the canonical
map in part (2). (blueprint: lem-sc-p1-section-fraction-restriction-map)

Proof: On `U`, each tensor power of `s` is a free generator. Tensoring with it is a
bijection on sections for every module `F`. Its inverse is additive and linear over
`Γ(U, O_X)`, since tensoring is linear. Compose that inverse with restriction in each
numerator degree. The resulting maps are additive and linear along scalar restriction.
The tensor-power addition isomorphism shows that division of `t` by `s^n` agrees with
division of `t ⊗ s^b` by `s^(n+b)`. Thus the direct-sum map kills every generator of
`sectionFractionRelations`, hence its span, and descends to the quotient. On the
quotient generators it satisfies the displayed tensor formula; scalar compatibility
follows from linearity along restriction. No compactness or quasi-coherence is used.
-/
theorem exists_sectionFraction_restriction_map {X : Scheme.{u}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens)
    (hs : IsFreeGenerator ((homOfGlobalSection L s).app U (unitSectionsEquiv U 1))) :
    ∃ f : SectionFractionPresentation L F s →+ Γ(F, U),
      (∀ (r : Γ(X, ⊤)) (z : SectionFractionPresentation L F s),
        f (r • z) = (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) • f z) ∧
      (∀ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, ⊤)),
        tmulSection (f (sectionFraction L F s n t))
            (tensorPowSectionOne (homOfGlobalSection L s) n U) =
          (F ⊗ L.tensorPow n).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op t) := by
  classical
  let e (n : ℕ) : Γ(F, U) →ₗ[Γ(X, U)] Γ(F ⊗ L.tensorPow n, U) :=
    { toFun := fun x ↦ tmulSection x (tensorPowSectionOne (homOfGlobalSection L s) n U)
      map_add' := fun x y ↦ add_tmulSection x y _
      map_smul' := fun r x ↦ smul_tmulSection r x _ }
  have he (n : ℕ) : Function.Bijective (e n) := by
    simpa only [e, LinearMap.coe_mk, AddHom.coe_mk, homOfLE_leOfHom,
      presheaf_map_id_apply] using
      IsFreeGenerator.bijective_tmulSection_right (M := F)
        (isFreeGenerator_tensorPowSectionOne (homOfGlobalSection L s) hs n) le_rfl
  let d (n : ℕ) := (LinearEquiv.ofBijective (e n) (he n)).symm
  have hd (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)) :
      tmulSection (d n t) (tensorPowSectionOne (homOfGlobalSection L s) n U) = t :=
    (LinearEquiv.ofBijective (e n) (he n)).apply_symm_apply t
  let res := (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
  let φ (n : ℕ) : Γ(F ⊗ L.tensorPow n, ⊤) →ₛₗ[res] Γ(F, U) :=
    { toFun := fun t ↦ d n ((F ⊗ L.tensorPow n).presheaf.map (homOfLE le_top).op t)
      map_add' := by intros; simp
      map_smul' := by intros; simp [res, map_smul] }
  let g₀ := DirectSum.toAddMonoid (fun n ↦ (φ n).toAddMonoidHom)
  let g : (⨁ n : ℕ, Γ(F ⊗ L.tensorPow n, ⊤)) →ₛₗ[res] Γ(F, U) :=
    { toFun := g₀
      map_add' := g₀.map_add
      map_smul' := by
        intro r z
        induction z using DirectSum.induction_on with
        | zero => simp
        | of n t =>
          simp only [← DirectSum.of_smul, g₀, DirectSum.toAddMonoid_of]
          exact (φ n).map_smulₛₗ r t
        | add x y hx hy => simp [smul_add, hx, hy] }
  have hg (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, ⊤)) :
      g (DirectSum.of (fun i : ℕ ↦ Γ(F ⊗ L.tensorPow i, ⊤)) n t) = φ n t :=
    DirectSum.toAddMonoid_of (fun n ↦ (φ n).toAddMonoidHom) n t
  have hrel : sectionFractionRelations L F s ≤ LinearMap.ker g := by
    apply Submodule.span_le.mpr
    rintro z ⟨n, b, t, rfl⟩
    change g (DirectSum.of _ n t - DirectSum.of _ (n + b)
      ((mulTensorPowSection (homOfGlobalSection L s) F n b).app ⊤ t)) = 0
    rw [map_sub, hg, hg, sub_eq_zero]
    apply (he (n + b)).1
    change tmulSection (φ n t) (tensorPowSectionOne (homOfGlobalSection L s) (n + b) U) =
      tmulSection (φ (n + b) ((mulTensorPowSection (homOfGlobalSection L s) F n b).app ⊤ t))
        (tensorPowSectionOne (homOfGlobalSection L s) (n + b) U)
    dsimp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← mulTensorPowSection_app_tmulSection, hd, ← Hom.app_presheaf_map, hd]
  let f := (sectionFractionRelations L F s).liftQ g hrel
  refine ⟨f.toAddMonoidHom, ?_, ?_⟩
  · intro r z
    exact f.map_smulₛₗ r z
  · intro n t
    change tmulSection (f (Submodule.Quotient.mk (DirectSum.of _ n t)))
      (tensorPowSectionOne (homOfGlobalSection L s) n U) = _
    rw [Submodule.liftQ_apply, hg]
    exact hd n _

end AlgebraicGeometry.Scheme.Modules
