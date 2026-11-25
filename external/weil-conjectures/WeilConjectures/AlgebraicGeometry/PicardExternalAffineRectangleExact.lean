/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardScalarAffineSectionsExact
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.AlgebraicGeometry.PicardExternalAffineRectangleComparison
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Exactness on affine rectangles of the external coefficient

Source: Stacks Project, Tag 0BED, the short exact coefficient diagram.
(blueprint: lem-sc-picard-external-affine-rectangle-exact).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The external coefficient, as a functor in the left module.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-affine-rectangle-exact). -/
def picardExternalCoefficientFunctor
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (G : Y.Modules) : X.Modules ⥤ (Limits.pullback f g).Modules :=
  tensorPullback (pullback.fst f g) ⋙
    tensorRight ((tensorPullback (pullback.snd f g)).obj G)

set_option backward.isDefEq.respectTransparency.types true in
/-- The coefficient functor preserves zero maps.
Source: additive adjunctions (blueprint: lem-sc-picard-external-affine-rectangle-exact). -/
instance picardExternalCoefficientFunctor_zero
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (G : Y.Modules) : (picardExternalCoefficientFunctor f g G).PreservesZeroMorphisms := by
  have : (tensorPullback (pullback.fst f g)).Additive :=
    (Classical.choose (exists_tensorPullbackAdjunction (pullback.fst f g))).left_adjoint_additive
  unfold picardExternalCoefficientFunctor
  infer_instance

/-- External-coefficient sections on one affine rectangle are short exact in the left
quasi-coherent coefficient. No flatness over the structure sheaf of Y is required.
Source: Stacks, Tag 0BED, equation-kunneth-on-cech and its coefficient diagram
(blueprint: lem-sc-picard-external-affine-rectangle-exact).

Proof: For affine opens U and V, their inverse-image intersection in the fibre product
is the affine scheme Spec (Gamma(U) tensor_k Gamma(V)). Affine pullback sections and
tensor sections identify the external module there with Gamma(F,U) tensor_k Gamma(G,V).
The comparisons are natural in F: the induced map of external sections is the tensor
of the section map of F with the identity on Gamma(G,V). The affine section sequence
of S is short exact, and tensoring over the field k preserves exactness, injectivity
and surjectivity. Transport this sequence through the natural comparisons, then
restrict scalars along the product structure map. Empty U or V and zero G give zero
modules, so the same statement holds in these cases. -/
theorem picardExternal_affine_rectangle_exact
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) (V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (G : Y.Modules) [G.IsQuasicoherent] :
    (S.map (picardExternalCoefficientFunctor f g G ⋙
      picardScalarSectionsFunctor (pullback.fst f g ≫ f)
        (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V))).ShortExact := by
  have hs := picardScalar_affine_sections_exact f U hU S hS
  have ht := hs.map_of_exact (tensorRight ((picardScalarSectionsFunctor g V).obj G))
  obtain ⟨e⟩ := picardExternal_affine_rectangle_comparison f g U V hU hV S G
  exact ShortComplex.shortExact_of_iso e ht

end
end AlgebraicGeometry.Scheme.Modules
