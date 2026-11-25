/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardScalarAffineSectionsExact
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.PicardExternalRectangleSections

/-! # Affine rectangle comparison for external coefficients

Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-affine-rectangle-comparison).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

set_option backward.isDefEq.respectTransparency.types true in
/-- External pullback and tensoring preserve zero maps.
Source: additive adjunctions
(blueprint: lem-sc-picard-external-affine-rectangle-comparison). -/
instance picardExternalRectangleComparison_zero
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (G : Y.Modules) :
    (tensorPullback (pullback.fst f g) ⋙
      tensorRight ((tensorPullback (pullback.snd f g)).obj G)).PreservesZeroMorphisms := by
  have : (tensorPullback (pullback.fst f g)).Additive :=
    (Classical.choose (exists_tensorPullbackAdjunction (pullback.fst f g))).left_adjoint_additive
  infer_instance

/-- The affine external-section comparison respects both arrows of a short complex.
This statement does not assume exactness of the complex.
Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech; Schemes, Tags 01I4,
01JQ, 01IA, and Modules, Tag 01BG.
(blueprint: lem-sc-picard-external-affine-rectangle-comparison).

Proof: For each quasi-coherent term of S, the explicitly constructed map
picardExternalRectangleSectionsMap is bijective by the affine rectangle section
computation. ConcreteCategory.isIso_iff_bijective therefore makes each map an
isomorphism. Use asIso on the three term maps and assemble them with
ShortComplex.isoMk. The two arrow equations are precisely the coefficient
naturality theorem for S.f and S.g, taken in the reverse direction. That naturality
is proved from the pullback-unit naturality and tensor-section formulas and holds
without an exactness hypothesis. No data is defined by choosing an unproved
existence witness: the term maps are explicit and their inverses are determined
by bijectivity. Empty opens and zero coefficients are included in the bijectivity
statement and require no separate assumptions. -/
theorem picardExternal_affine_rectangle_comparison
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) (V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (S : ShortComplex X.Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (G : Y.Modules) [G.IsQuasicoherent] :
    Nonempty
      (((S.map (picardScalarSectionsFunctor f U)).map
        (tensorRight ((picardScalarSectionsFunctor g V).obj G))) ≅
        (S.map ((tensorPullback (pullback.fst f g) ⋙
          tensorRight ((tensorPullback (pullback.snd f g)).obj G)) ⋙
          picardScalarSectionsFunctor (pullback.fst f g ≫ f)
            (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)))) := by
  have hi (F : X.Modules) [F.IsQuasicoherent] :
      IsIso (picardExternalRectangleSectionsMap f g U V F G) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (picardExternalRectangleSectionsMap_bijective f g U V hU hV F G)
  have := hi S.X₁
  have := hi S.X₂
  have := hi S.X₃
  refine ⟨ShortComplex.isoMk
    (asIso (picardExternalRectangleSectionsMap f g U V S.X₁ G))
    (asIso (picardExternalRectangleSectionsMap f g U V S.X₂ G))
    (asIso (picardExternalRectangleSectionsMap f g U V S.X₃ G)) ?_ ?_⟩
  · exact (picardExternalRectangleSectionsMap_naturality f g U V S.f G).symm
  · exact (picardExternalRectangleSectionsMap_naturality f g U V S.g G).symm

end
end AlgebraicGeometry.Scheme.Modules
