import Langlands.GroupScheme.Rational.NumberFieldTypeE6CubicSplitIsotropy
import Langlands.GroupScheme.Rational.NumberFieldTypeE6InnerQuadraticVanishing

/-! # Prime covers of quasi-split inner E6 over totally complex number fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

/-- Vanishing on covers of degree two or three for quasi-split simply
connected inner E6 over totally complex number fields. -/
def NumberFieldTotallyComplexQuasiSplitInnerTypeE6PrimeCoverStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
      IsSimplyConnected G → IsQuasiSplit G →
      (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
      (∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex), d.star σ a = a) →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
        Module.finrank F L ∈ ({2, 3} : Set ℕ) →
        ∀ ξ : Cocycle G (GaloisCocycle.cover F L), ξ.IsTrivial

/-- Cubic splitting isotropy supplies vanishing for the prime covers of
degrees two and three in the inner quasi-split case. -/
def NumberFieldTotallyComplexInnerTypeE6PrimeCoverReductionStatement : Prop :=
  NumberFieldTotallyComplexTypeE6CubicSplitIsotropyStatement.{u} →
    NumberFieldTotallyComplexQuasiSplitInnerTypeE6PrimeCoverStatement.{u}

theorem numberFieldTotallyComplexInnerTypeE6PrimeCoverVanishing_of_cubicSplitIsotropy :
    NumberFieldTotallyComplexInnerTypeE6PrimeCoverReductionStatement.{u} := by
  intro hIso F _ _ hF G _ _ d e hsc hqs hE hinner L _ _ _ _ hL ξ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL
  rcases hL with hL | hL
  · exact numberFieldTotallyComplexInnerTypeE6QuadraticVanishing F hF G d e hsc hqs hE hinner L hL ξ
  let : Smooth G.X.hom := hsc.isSemisimple.isConnectedReductive.smooth
  have hstar (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) : d.pinning.starAction σ = 1 := by
    apply Subtype.ext
    apply StarActionIndependence.equiv_ext_of_weightMap
    exact d.pinning.starAction_weight_of_inner hsc (fun τ a => congrArg Subtype.val (hinner τ a)) σ
  have hsplit := (quasiSplitStarCriterion F G hqs d.pinning).mpr hstar
  let a := AutomorphicAction.conjugation (𝟙 G)
  obtain ⟨H, t, hHa, ht⟩ := finiteGaloisTwistExistence F L G G inferInstance a ξ
  let : IsAffineHom H.X.hom := hHa
  let b := algebraBaseMap F L
  let j : (GroupScheme.baseChange b).obj G ≅ (GroupScheme.baseChange b).obj H := t.toBaseChangeIso
  have hscH : IsSimplyConnected H := (isSimplyConnected_fieldExtension_iff (K := L) H).mp
    (IsSimplyConnected.of_iso j.symm (isSimplyConnectedFieldExtension F L G hsc))
  let : Smooth H.X.hom := hscH.isSemisimple.isConnectedReductive.smooth
  obtain ⟨dH⟩ := titsIndexExistence F H hscH.isSemisimple
  obtain ⟨eH, hEH, _⟩ := t.exists_inner_numbering_of_conjugation d dH e
    (CartanMatrix.E 6) hE hinner ξ ht
  have hsplitH : HasSplitMaximalTorus ((GroupScheme.baseChange b).obj H) := by
    obtain ⟨S, s, hS, hs⟩ := hsplit
    let SL := (CommGroupScheme.baseChange b).obj S
    let sL : SL.toGrp ⟶ (GroupScheme.baseChange b).obj G := (GroupScheme.baseChange b).map s
    have hmax : IsMaximalTorus sL := (maximalTorusBaseChange F L G S s hs.1 hs.2.1).mp hs
    exact ⟨SL, sL ≫ j.hom, hS.baseChange b, hmax.comp_iso j⟩
  exact ξ.isTrivial_of_splitE6_isotropicTwist hF d e hE hsc hsplit t ht hscH dH
    (hIso F L hF hL H dH eH hscH hEH hsplitH)

end Langlands.GroupScheme
