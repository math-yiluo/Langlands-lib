/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverStageDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.PointedSectionStageDescent

/-!
# Descent of a pointed finite torsor along affine inverse limits

## References

* Stacks Project, Tag 0EZJ, last paragraph of the limit reduction
* Stacks Project, Tags 0BTV and 01ZM
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Descend a finite torsor and a point above a compatible section. The two inverse
systems need only be qcqs with affine transitions, and need not be Noetherian or normal. -/
theorem GaloisCover.exists_pointed_stage_of_affine_limits
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D K : I ⥤ Scheme.{u})
    (hDqc : ∀ i, CompactSpace (D.obj i)) (hDqs : ∀ i, QuasiSeparatedSpace (D.obj i))
    (hKqc : ∀ i, CompactSpace (K.obj i)) (hKqs : ∀ i, QuasiSeparatedSpace (K.obj i))
    (hDa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f))
    (hKa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (K.map f))
    {X T : Scheme.{u}} (κ : (Functor.const I).obj X ⟶ D)
    (b : (Functor.const I).obj T ⟶ K)
    (hκ : IsLimit (Cone.mk X κ)) (hb : IsLimit (Cone.mk T b))
    (s : K ⟶ D) (sη : T ⟶ X) (hs : ∀ i, sη ≫ κ.app i = b.app i ≫ s.app i)
    (G : Type (u + 1)) [Group G] [Finite G] (Z : GaloisCover G X)
    (hZ : ∃ z : T ⟶ Z.P, z ≫ Z.π = sη) :
    ∃ (i : I) (Z₀ : GaloisCover G (D.obj i)) (χ : Z.P ⟶ Z₀.P),
      IsPullback χ Z.π Z₀.π (κ.app i) ∧
      ∃ z₀ : K.obj i ⟶ Z₀.P, z₀ ≫ Z₀.π = s.app i := by
  obtain ⟨i, Z₀, χ, hχ⟩ :=
    GaloisCover.exists_stage_of_affine_limits D hDqc hDqs hDa κ hκ G Z
  obtain ⟨z, hz⟩ := hZ
  let P := pullback Z₀.π (s.app i)
  let p : P ⟶ K.obj i := pullback.snd _ _
  have : Etale Z₀.π := Z₀.etale
  have : LocallyOfFinitePresentation p := by
    dsimp [p, P]
    infer_instance
  let a : T ⟶ P := pullback.lift (z ≫ χ) (b.app i) (by
    rw [Category.assoc, hχ.w, ← Category.assoc, hz, hs])
  have ha : a ≫ p = b.app i := by simp [a, p]
  obtain ⟨j, f, a₀, _, ha₀⟩ := exists_map_at_refinement_of_affine_limit
    K hKqc hKqs hKa b hb i p a ha
  obtain ⟨Z₁, ρ, hρ⟩ := GaloisCover.exists_baseChange G Z₀ (D.map f)
  have hz₀ : (a₀ ≫ pullback.fst Z₀.π (s.app i)) ≫ Z₀.π = s.app j ≫ D.map f := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha₀]
    exact s.naturality f
  let z₁ : K.obj j ⟶ Z₁.P := hρ.lift
    (a₀ ≫ pullback.fst Z₀.π (s.app i)) (s.app j) hz₀
  have hκf : κ.app j ≫ D.map f = κ.app i := by
    simpa using (κ.naturality f).symm
  have hχf : χ ≫ Z₀.π = Z.π ≫ (κ.app j ≫ D.map f) := by
    rw [hκf]
    exact hχ.w
  let ψ : Z.P ⟶ Z₁.P := hρ.lift χ (Z.π ≫ κ.app j) (by
    simpa only [Category.assoc] using hχf)
  refine ⟨j, Z₁, ψ, ?_, z₁, ?_⟩
  · have houter : IsPullback χ Z.π Z₀.π (κ.app j ≫ D.map f) := by
      rw [hκf]
      exact hχ
    exact houter.of_right' hρ
  · exact hρ.lift_snd _ _ _

end AlgebraicGeometry.Scheme
