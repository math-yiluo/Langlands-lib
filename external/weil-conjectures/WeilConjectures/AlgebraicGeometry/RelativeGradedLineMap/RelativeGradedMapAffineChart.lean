/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeGradedLineMap.RelativeGradedLineMap
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample

/-! # Affine restriction of a relative graded canonical map

## References

* Stacks Project, Constructions, Tag 01O9, part (3)
* Stacks Project, Constructions, Tag 01O9, characterization (3), and Tag 01NK
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine base chart, a normalized graded section map whose positive-degree
images generate has the basic-open and fraction formulas of its canonical relative map.
No immersion or quasi-compactness assumption is required.
-/
theorem RelativeGradedLineMap.affine_chart_formulas
    {Z S : Scheme.{u}} {h : Z ⟶ S} {L : Z.Modules} [L.IsInvertible]
    {A : S.GradedAlgebraData} (ψ : RelativeGradedLineMap h A L)
    (r : Z ⟶ A.relProj) (hr : ψ.IsCanonicalMap r)
    (V : S.affineOpens)
    (hM : ((tensorPullback (h ⁻¹ᵁ V.1).ι).obj L).IsInvertible) :
    let T := (h ⁻¹ᵁ V.1).toScheme
    let M := (tensorPullback (h ⁻¹ᵁ V.1).ι).obj L
    let 𝒜 : ℕ → AddSubgroup (A.obj V) := fun n ↦ (A.grading V n).toAddSubgroup
    letI : GradedRing 𝒜 := { (inferInstance : GradedRing (A.grading V)) with }
    let γ : A.grading V →+*ᵍ 𝒜 :=
      { toRingHom := RingHom.id _
        map_mem := fun ha ↦ ha }
    ∀ (ρ : T ⟶ Proj 𝒜),
      ρ ≫ Proj.map γ (by
        intro a ha
        exact Ideal.mem_map_of_mem γ.toRingHom ha) ≫ A.relProjι V = (h ⁻¹ᵁ V.1).ι ≫ r →
      ∀ (φ : 𝒜 →+*ᵍ sectionRingGrade M),
        (∀ (n : ℕ) (a : A.grading V n),
          φ.toRingHom a = (DirectSum.of (SectionRingComponent M) n)
            (ψ.evaluate (h ⁻¹ᵁ V.1).ι V (by simp) n a)) →
        (∀ z : T, ∃ (n : ℕ) (a : A.obj V) (ha : a ∈ 𝒜 n),
          0 < n ∧ z ∈ nonvanishingLocus (M.tensorPow n) ((φ.toRingHom a) n)) →
        (∀ (d : ℕ) (_hd : 0 < d) (a : A.obj V) (_ha : a ∈ 𝒜 d),
          (ρ ⁻¹ᵁ Proj.basicOpen 𝒜 a : Set T) =
            nonvanishingLocus (M.tensorPow d) ((φ.toRingHom a) d)) ∧
        (∀ (d : ℕ) (_hd : 0 < d) (a : A.obj V) (ha : a ∈ 𝒜 d),
          ∀ (n : ℕ) (b : A.obj V) (_hb : b ∈ 𝒜 (n • d)),
            (ρ.app (Proj.basicOpen 𝒜 a)
              (Proj.awayToSection 𝒜 a (HomogeneousLocalization.Away.mk 𝒜 ha n b _hb))) •
              (M.tensorPow (n • d)).presheaf.map
                (homOfLE (le_top : ρ ⁻¹ᵁ Proj.basicOpen 𝒜 a ≤ ⊤)).op
                (((φ.toRingHom a) ^ n) (n • d)) =
              (M.tensorPow (n • d)).presheaf.map
                (homOfLE (le_top : ρ ⁻¹ᵁ Proj.basicOpen 𝒜 a ≤ ⊤)).op
                ((φ.toRingHom b) (n • d))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
