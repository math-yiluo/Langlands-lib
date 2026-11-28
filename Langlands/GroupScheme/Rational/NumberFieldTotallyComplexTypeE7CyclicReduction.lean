import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexTypeE7Inputs
import Langlands.GroupScheme.Rational.NumberFieldTypeE7HasseInputs
import Langlands.GroupScheme.Rational.NumberFieldTypeE6LeviReduction
import Langlands.GroupScheme.Rational.FiniteGaloisTwistExistence
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormBaseChange
import Langlands.GroupScheme.Rational.IsotropicTwistSplitLineReduction
import Langlands.GroupScheme.Torus.CentralizerSmooth

/-! # Reduction of quadratic and cubic vanishing for totally complex type `E_7`

This module states two propositions about a quasi-split simply connected absolutely
almost-simple group `G` of type `E_7` over a totally complex number field: every twist of `G`
by a cocycle on a Galois cover of degree `3` contains a closed copy of `𝔾_m`, and the
centralizer in `G` of a closed copy of `𝔾_m` has trivial cocycles on every finite Galois
field cover. It proves that these two propositions, the quadratic Hasse principle for type
`E_7` and the reduction of an isotropic inner twist to the centralizer of a split line imply
`NumberFieldTotallyComplexTypeE7CyclicStatement`. The two new propositions are not proved
here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `K` be a totally complex number field and `G` a quasi-split simply connected
absolutely almost-simple group of type `E_7` over `K`. Let `ξ` be a cocycle of `G` on a
Galois field cover `Spec L → Spec K` of degree `3`, and `H` a twist of `G` by `ξ` acting by
conjugation, given by a family of identifications `φ` of `G` and `H` over the cover whose
discrepancy is `ξ`. Then `H` contains a closed copy of `𝔾_m`, that is, `H` is isotropic over
`K`. -/
def NumberFieldTotallyComplexTypeE7CubicTwistIsotropyStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
    IsQuasiSplit G →
    ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
      Module.finrank K L = 3 →
      ∀ (ξ : Cocycle G (GaloisCocycle.cover K L))
        (H : GroupScheme (Spec (CommRingCat.of K)))
        (φ : LocalGroupIso G H (GaloisCocycle.cover K L)),
        IsAffineHom H.X.hom → φ.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ →
        ∃ μ : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ H, IsClosedSubgroup μ

/-- Let `K` be a totally complex number field and `G` a quasi-split simply connected
absolutely almost-simple group of type `E_7` over `K`. Let `ν` be a closed copy of `𝔾_m` in
`G` and `j : C ⟶ G` a closed subgroup, smooth over `K`, representing the centralizer of `ν`.
Then every cocycle of `C` on a finite Galois field cover `Spec M → Spec K` is trivial. -/
def NumberFieldTotallyComplexTypeE7SplitLineCentralizerVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
    IsQuasiSplit G →
    ∀ (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ G), IsClosedSubgroup ν →
    ∀ (C : GroupScheme (Spec (CommRingCat.of K))) (j : C ⟶ G),
      IsClosedSubgroup j → Smooth C.X.hom → (torusCentralizer ν).IsRepresentedBy j →
      ∀ (M : Type u) [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
        (τ : Cocycle C (GaloisCocycle.cover K M)), τ.IsTrivial

set_option backward.isDefEq.respectTransparency false in
/-- The quadratic Hasse principle for type `E_7`, the reduction of isotropic inner twists to
centralizers of split lines, the isotropy of cubic twists and the vanishing on centralizers
of split lines imply vanishing on Galois covers of degree `2` and `3`. -/
theorem numberFieldTotallyComplexTypeE7Cyclic_of_inputs
    (hquad : NumberFieldTypeE7QuadraticHasseStatement.{u})
    (hline : IsotropicTwistSplitLineReductionStatement.{u})
    (hiso : NumberFieldTotallyComplexTypeE7CubicTwistIsotropyStatement.{u})
    (hcent : NumberFieldTotallyComplexTypeE7SplitLineCentralizerVanishingStatement.{u}) :
    NumberFieldTotallyComplexTypeE7CyclicStatement.{u} := by
  intro K _ _ hK G _ _ d e hsc habs hCartan hqs L _ _ _ _ hdeg ξ
  rcases hdeg with h2 | h3
  · exact hquad K G d e hsc habs hCartan L h2 hqs.baseChange_of_algebraicExtension ξ
      (ξ.locallyTrivial_of_totallyComplex hK hsc)
  · obtain ⟨H, φ, hH, hφ⟩ := finiteGaloisTwistExistence K L G G inferInstance
      (AutomorphicAction.conjugation (𝟙 G)) ξ
    obtain ⟨μ, hμ⟩ := hiso K G d e hsc habs hCartan hqs L h3 ξ H φ hH hφ
    obtain ⟨M, _, _, _, _, _, _, g, ν, hν, hmem⟩ := hline K G hqs L ξ H φ hH hφ μ hμ
    let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    obtain ⟨C, j, hj, hCsm, hrep⟩ := torusCentralizer_hasSmoothClosedRepresentative ν
      ⟨isSplitTorus_gm, hν⟩ hqs.isConnectedReductive.smooth
    let : Mono j.hom.hom := hrep.1
    have hfac : ∀ {Z : Over (Spec (CommRingCat.of K))} (a b : Z ⟶ GaloisCocycle.cover K M),
        ∃ k : Z ⟶ C.X, k ≫ j.hom.hom =
          ((ξ.refine (GaloisCocycle.coverMap K L M)).twist g).toFun a b := by
      intro Z a b
      have h := hmem a b
      rw [← hrep.2] at h
      exact SubgroupFunctor.mem_range.1 h
    have hlift := hcent K G d e hsc habs hCartan hqs ν hν C j hj hCsm hrep M
      (((ξ.refine (GaloisCocycle.coverMap K L M)).twist g).lift j hfac)
    let : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
    let : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
    exact GaloisCocycle.isTrivial_of_refine K L M ξ hlift.of_lift.of_twist

end Langlands.GroupScheme
