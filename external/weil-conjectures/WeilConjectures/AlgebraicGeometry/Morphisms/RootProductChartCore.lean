/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.Morphisms.RootFactorStalkLocalization

/-! Local algebra presentation at a point of a root product chart.

## References

* Stacks Project, Tags 0EYH and 0EYI, affine root charts and pointed neighborhoods
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem stalkMap_comp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) : ((f ≫ g).stalkMap x).hom =
      (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom := by
  exact congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f g x)

-- Dependent stalk types across the chart isomorphism require extra elaboration steps.
set_option backward.isDefEq.respectTransparency false in
/-- A root product chart, localized at a specified point, is the localization of one
root factor over the base stalk, compatibly with the structural ring map. -/
theorem rootProductChart_stalk_localization_core {Z : Scheme.{u}}
    (R : CommRingCat.{u}) (q : Z ⟶ Spec R) (z : Z)
    (f : R) (hf : f ∈ (q z).asIdeal)
    (m : ℕ) (e : Fin m → ℕ) (he : ∀ k, 0 < e k)
    (α : Z ≅ Spec (CommRingCat.of (∀ k : Fin m,
      AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))))
    (hα : α.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (∀ k : Fin m,
        AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)))) = q) :
    let R₀ := (Spec R).presheaf.stalk (q z)
    ∃ (k : Fin m) (f₀ : R₀), f₀ ∈ IsLocalRing.maximalIdeal R₀ ∧
      let p := (Polynomial.X : Polynomial R₀) ^ e k - Polynomial.C f₀
      let D := AdjoinRoot p
      ∃ (P : Ideal D) (hP : P.IsMaximal),
        letI : P.IsPrime := hP.isPrime
        let E := Localization.AtPrime P
        ∃ θ : Z.presheaf.stalk z ≃+* E,
          θ.toRingHom.comp (q.stalkMap z).hom =
            (algebraMap D E).comp (AdjoinRoot.of p)  := by
  classical
  let A (k : Fin m) := AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)
  obtain ⟨⟨k, w⟩, hw⟩ := (PrimeSpectrum.sigmaToPi_bijective A).surjective (α.hom z)
  let g : Spec (CommRingCat.of (A k)) ⟶ Spec (CommRingCat.of (∀ k, A k)) :=
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom A k))
  have hgw : g w = α.hom z := hw
  let t : Spec (CommRingCat.of (A k)) ⟶ Z := g ≫ α.inv
  have htz : t w = z := by
    dsimp only [t]
    rw [Scheme.Hom.comp_apply, hgw]
    change (α.hom ≫ α.inv) z = z
    simp
  have htq : t ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R (A k))) := by
    dsimp only [t]
    rw [Category.assoc, ← hα, α.inv_hom_id_assoc]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom A k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (∀ k, A k))) = _
    rw [← Spec.map_comp]
    rfl
  have : IsOpenImmersion t := by dsimp only [t, g]; infer_instance
  subst z
  have hf' : f ∈ ((t ≫ q) w).asIdeal := hf
  obtain ⟨f₀, hf₀, P, hP, θ, hθ⟩ :=
    rootFactor_stalk_localization R f (e k) (he k) (t ≫ q) htq w hf'
  let s : Z.presheaf.stalk (t w) ≃+*
      (Spec (CommRingCat.of (A k))).presheaf.stalk w :=
    RingEquiv.ofBijective (t.stalkMap w).hom (ConcreteCategory.bijective_of_isIso _)
  refine ⟨k, f₀, hf₀, P, hP, s.trans θ, ?_⟩
  change θ.toRingHom.comp ((t.stalkMap w).hom.comp (q.stalkMap (t w)).hom) = _
  exact (congrArg (fun h ↦ θ.toRingHom.comp h) (stalkMap_comp_hom t q w).symm).trans hθ

end AlgebraicGeometry.Scheme
