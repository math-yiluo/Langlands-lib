/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.DisjointCover
public import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.AlgebraicGeometry.IntegralPointedEtaleFiniteModel

/-!
# Pointed clopen refinements for integral morphisms

Source: the conservativity argument in the proof of blueprint
`lemma-integral-changes-source-base--2`. (blueprint: lem-sbc-integral-pointed-clopen-refinement)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom.Nbhd

set_option backward.isDefEq.respectTransparency.types false in
/-- An étale neighbourhood of a point over an integral morphism is refined by a clopen
piece of a base-changed neighbourhood of its image.

Source: blueprint `lemma-integral-changes-source-base--2`, proof, the integral algebra over the
strict henselisation and its finite subalgebras.
(blueprint: lem-sbc-integral-pointed-clopen-refinement)

Proof: Shrink the base to an affine neighbourhood. Over its strict henselisation, write the
integral algebra as the filtered union of its finite subalgebras. Shrink the given étale
neighbourhood at the marked point to a standard étale affine. Its finitely many presentation
coefficients descend to one finite subalgebra. A finite algebra over a strictly henselian
local ring is a product of strictly henselian local rings. In the factor selected by the
marked geometric point the descended étale neighbourhood has a section through that point.
Pull back that factor and its complementary factors to the integral algebra. The factor
is clopen and its section gives a map to the original neighbourhood preserving the marked
point. The idempotent defining the factor, its complement, the étale section, and their
finitely many equations descend to a pointed étale neighbourhood of the base geometric
point. This gives P, Q, p and a with the two displayed equalities. No surjectivity of f is
used. If the source is empty there is no geometric point t, so this case is vacuous. -/
theorem exists_pointed_clopen_refinement
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (t : Scheme.Hom.GeometricFiber f y) (V : X.Etale)
    (v : (Scheme.pointSmallEtale t.1).fiber.obj V) :
    ∃ (c : Scheme.Hom.Nbhd y) (P Q : (pullback c.1.hom f).Opens),
      Disjoint P Q ∧ P ⊔ Q = ⊤ ∧
      ∃ (p : (Scheme.pointSmallEtale t.1).fiber.obj (openObj f c P))
        (a : openObj f c P ⟶ V),
        (Scheme.pointSmallEtale t.1).fiber.map a p = v ∧
        (Scheme.pointSmallEtale t.1).fiber.map (openIncl f c P) p =
          ((AlgebraicGeometry.Etale.baseChangeNbhd f y t).obj c).2 := by
  classical
  obtain ⟨c, Z, g, hg, ρ, hρ, W, r, a₀, ha₀, hra₀, hrs⟩ :=
    exists_pointed_etale_finite_model f y t V v
  have := hg
  let t₀ : Scheme.Hom.GeometricFiber g c.2.left :=
    ⟨basePt f c t ≫ ρ, by rw [Category.assoc, hρ, basePt_fst]⟩
  let w : (Scheme.pointSmallEtale t₀.1).fiber.obj W :=
    CategoryTheory.Over.homMk (r ≫ pullback.fst W.hom ρ) (by
      change (r ≫ pullback.fst W.hom ρ) ≫ W.hom = basePt f c t ≫ ρ
      rw [Category.assoc, pullback.condition, ← Category.assoc, hrs])
  obtain ⟨s, ⟨b⟩⟩ :=
    Scheme.Hom.SplitNbhd.exists_pieceFunctor_obj_hom g t₀ (Functor.elementsMk _ W w)
  let c' := c.comp s.obj
  let gm := c.compHom s.obj
  let θ : pullback c'.1.hom f ⟶ pullback s.obj.1.hom g :=
    pullback.lift (pullback.fst _ f) ((f.Etale.map gm.val).left ≫ ρ) (by
      rw [Category.assoc, hρ, Scheme.Hom.etale_map_left_comp_fst]
      rfl)
  have hθpt : basePt f c' t ≫ θ = basePt g s.obj t₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, basePt_fst, basePt_fst]
      rfl
    · simp [θ, gm, t₀]
  let P := θ ⁻¹ᵁ s.piece t₀
  have hPc : IsClopen (P : Set (pullback c'.1.hom f : Scheme.{u})) :=
    (s.isClopen t₀).preimage θ.continuous
  let Q : (pullback c'.1.hom f).Opens := ⟨(P : Set _)ᶜ, hPc.isClosed.isOpen_compl⟩
  have hpRange : Set.range (basePt f c' t).base ⊆ Set.range P.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim (α := Spec (.of Ω)) x default]
    change θ (basePt f c' t default) ∈ s.piece t₀
    rw [← Scheme.Hom.comp_apply, hθpt]
    exact s.mem t₀
  let pt : Spec (.of Ω) ⟶ P := IsOpenImmersion.lift P.ι (basePt f c' t) hpRange
  have hpt : pt ≫ P.ι = basePt f c' t := IsOpenImmersion.lift_fac _ _ _
  let p : (Scheme.pointSmallEtale t.1).fiber.obj (openObj f c' P) :=
    CategoryTheory.Over.homMk pt (by
      change pt ≫ P.ι ≫ pullback.snd c'.1.hom f = t.1
      rw [← Category.assoc, hpt, basePt_snd])
  let μ₁ : P.toScheme ⟶ pullback c.1.hom f := P.ι ≫ (f.Etale.map gm.val).left
  let μ₂ : P.toScheme ⟶ W.left := θ.resLE (s.piece t₀) P le_rfl ≫ b.val.left
  have hμ : μ₂ ≫ W.hom = μ₁ ≫ ρ := by
    have hb : b.val.left ≫ W.hom =
        (s.piece t₀).ι ≫ pullback.snd s.obj.1.hom g := MorphismProperty.Over.w b.val
    simp only [μ₁, μ₂, Category.assoc, hb]
    rw [Scheme.Hom.resLE_comp_ι_assoc]
    simp [θ]
  let μ : P.toScheme ⟶ pullback W.hom ρ := pullback.lift μ₂ μ₁ hμ
  let a : openObj f c' P ⟶ V := MorphismProperty.Over.homMk (μ ≫ a₀) (by
    change (μ ≫ a₀) ≫ V.hom = P.ι ≫ pullback.snd c'.1.hom f
    rw [Category.assoc, ha₀, ← Category.assoc, pullback.lift_snd]
    simpa only [μ₁, Category.assoc] using
      congrArg (fun h ↦ P.ι ≫ h) (Scheme.Hom.etale_map_left_comp_snd f gm.val))
  have hptθ : pt ≫ θ.resLE (s.piece t₀) P le_rfl = (s.piecePt t₀).left := by
    apply (cancel_mono (s.piece t₀).ι).mp
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hpt, hθpt,
      Scheme.Hom.SplitNbhd.piecePt_left_ι]
  have hptμ : pt ≫ μ = r := by
    apply pullback.hom_ext
    · change pt ≫ μ ≫ pullback.fst W.hom ρ = r ≫ pullback.fst W.hom ρ
      rw [pullback.lift_fst, ← Category.assoc, hptθ]
      exact congrArg CategoryTheory.Over.Hom.left b.map_val
    · change pt ≫ μ ≫ pullback.snd W.hom ρ = r ≫ pullback.snd W.hom ρ
      rw [pullback.lift_snd, hrs]
      change pt ≫ (P.ι ≫ (f.Etale.map gm.val).left) = basePt f c t
      rw [← Category.assoc, hpt]
      exact basePt_comp_etale_map_left f gm t
  refine ⟨c', P, Q, ?_, ?_, p, a, ?_, ?_⟩
  · rw [disjoint_iff]
    ext x
    simp [Q]
  · ext x
    simp [Q]
  · apply CategoryTheory.Over.OverMorphism.ext
    change pt ≫ μ ≫ a₀ = v.left
    rw [← Category.assoc, hptμ, hra₀]
  · apply CategoryTheory.Over.OverMorphism.ext
    exact hpt

end AlgebraicGeometry.Scheme.Hom.Nbhd
