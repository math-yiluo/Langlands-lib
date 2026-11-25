/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleMaps
import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleIdentityLaw
import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleCompositionLaw

/-! # Explicit maps for restricted degree-zero complexes

Source: Stacks Project, Tags 09Z1 and 0EZM.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The explicit restricted transitions satisfy the unit and composition laws.
Source: Stacks Project, Tag 09Z1 proof (restriction to an affine etale object),
and the inverse-image composition comparisons of Tag 03CB.
(blueprint: lem-sbc-restricted-affine-single-transition-laws).

Proof: The pullback projection identity identifies the composite of the restricted
map with the stage second projection with the limit second projection followed by
the original map. Expand rawAffineRestrictedCoefficient. For the identity, substitute
D.map_id and the given coefficient identity law; the two unit laws of upperStarComp
cancel the composition comparisons. For two arrows, substitute D.map_comp and the
coefficient composition law. Apply upperStarComp_assoc to each of the two triangles
of second projections, and naturality to move the coefficient maps through the
comparisons. Cancel adjacent inverse comparisons. Apply the degree-zero single
functor. Its inverse-image comparison is natural, and is compatible with identity
and composition termwise: in degree zero it is the identity comparison, and in all
other degrees both complexes are zero. This gives exactly the displayed laws. -/
theorem restrictedAffineSingleTransition_laws {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (U : S.Etale) :
    let D' := restrictedAffineDiagram D U
    let K := restrictedAffineK D F U
    let ψ := fun {i j : Iᵒᵖ} (f : j ⟶ i) ↦ restrictedAffineSingleTransition D F φ U f
    ( ∀ i : Iᵒᵖ, ψ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) (D'.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} (D'.obj i))
        (ComplexShape.up ℤ)).hom.app (K i))
    ∧ ( ∀ (i j k : Iᵒᵖ) (f : j ⟶ i) (g : k ⟶ j),
      ψ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (D'.map g) (D'.map f)
            (D'.map (g ≫ f)) (D'.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (D'.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ ψ g) := by
  exact ⟨restrictedAffineSingleTransition_identity_law D F φ hφid U,
    restrictedAffineSingleTransition_composition_law D F φ hφcomp U⟩

end AlgebraicGeometry.Etale
