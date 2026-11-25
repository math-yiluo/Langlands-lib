/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedAffineCoefficientConstruction
import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleTransitionLaws
import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleConeNaturality
import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleConeLeg
import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Concrete restricted affine coefficient constructions

Source: Stacks Project, Tags 09Z1 and 0EZM.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

-- Preserve the existing names of the existential proof witnesses in the statement.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- Coherent transitions and cone comparisons for the concrete restricted single complexes.
Source: Stacks Project, Tag 09Z1 proof (restriction to an affine etale object), and
Tag 0EZM (canonical coefficient maps).
(blueprint: lem-sbc-restricted-affine-single-coherence).

Proof: First substitute hD' and the four heterogeneous data equalities to reduce to
the concrete diagram, cone, K, G and L. Restrict each transition by
rawAffineRestrictedCoefficient and compose its image
under the degree-zero single functor with mapCochainComplexSingleFunctor. The pullback
projection triangles and upperStarComp identify successive restrictions. The unit and
associativity coherence of upperStarComp, and the identity and composition laws for phi,
give the two transition laws. At each cone leg use the composition comparisons for the
triangle between the two second projections and the cone leg, followed by the restriction
of eH, to identify G with the pulled-back K. Naturality of these comparisons and the
transition equation hH give the diagram equation hG. Inverting this comparison and
composing with the restricted colimit injection cancels the eH comparison. The remaining
two composition comparisons are precisely rawAffineRestrictedCoefficient for that leg.
Naturality of mapCochainComplexSingleFunctor gives the asserted complex-level equality.
The data equalities only allow local names for these fixed constructions; they introduce
no mathematical hypothesis beyond identifying the constructions. This theorem constructs
neither a limit of schemes nor a cohomology comparison. -/
theorem exists_restricted_affine_single_coherence {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H]
    (U : S.Etale)
    (D' : Iᵒᵖ ⥤ Scheme.{v}) (c' : Cone D')
    (K : ∀ i : Iᵒᵖ, CochainComplex
      (Sheaf (D'.obj i).smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (G : (Iᵒᵖ)ᵒᵖ ⥤ CochainComplex
      (Sheaf c'.pt.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (L : Cocone G)
    (hD' : D' = restrictedAffineDiagram D U)
    (hc' : HEq c' (restrictedAffineCone D c U))
    (hK : HEq K (restrictedAffineK D F U))
    (hG' : HEq G (restrictedAffineG D c H U))
    (hL' : HEq L (restrictedAffineL D c H U)) :
    ∃
    (ψ : ∀ {i j : Iᵒᵖ} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{v + 1} (D'.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i) ⟶ K j)
    (hidentity : ∀ i : Iᵒᵖ, ψ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) (D'.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} (D'.obj i))
        (ComplexShape.up ℤ)).hom.app (K i))
    (hcomposition : ∀ (i j k : Iᵒᵖ) (f : j ⟶ i) (g : k ⟶ j),
      ψ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (D'.map g) (D'.map f)
            (D'.map (g ≫ f)) (D'.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (D'.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ ψ g)
    (eG : ∀ i : Iᵒᵖ, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{v + 1} (c'.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i))
    (hG : ∀ (i j : Iᵒᵖ) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (c'.π.app j) (D'.map f)
            (c'.π.app i) (c'.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (c'.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ (eG j).inv),
    ∀ i : Iᵒᵖ,
      HEq ((eG i).inv ≫ L.ι.app (op i))
        (((upperStar AddCommGrpCat.{v + 1}
          ((restrictedAffineCone D c U).π.app i)).mapCochainComplexSingleFunctor 0).hom.app
            ((upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom (D.obj i).hom)).obj
              (F i.unop)) ≫
        (CochainComplex.singleFunctor _ 0).map
          (rawAffineRestrictedCoefficient (c.π.app i).left (D.obj i).hom c.pt.hom
            (Over.w (c.π.app i)) (F i.unop) (colimit H)
            ((eH i.unop).inv ≫ colimit.ι H i.unop) U)) := by
  subst D'
  cases eq_of_heq hc'
  cases eq_of_heq hK
  cases eq_of_heq hG'
  cases eq_of_heq hL'
  obtain ⟨hid, hcomp⟩ := restrictedAffineSingleTransition_laws D F φ hφid hφcomp U
  refine ⟨restrictedAffineSingleTransition D F φ U, hid, hcomp,
    restrictedAffineSingleConeIso D c F H eH U,
    restrictedAffineSingleConeIso_naturality D c F φ H eH hH U, ?_⟩
  intro i
  exact heq_of_eq (restrictedAffineSingleConeIso_inv_leg D c F H eH U i)

end AlgebraicGeometry.Etale
