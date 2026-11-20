import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOpenCellHeight
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.ParabolicContainsMinimalProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof

/-! # Dynamic parabolic products at the literal Levi compact -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

set_option maxHeartbeats 600000 in
/-- An Iwasawa product for the standard minimal parabolic gives the product
for every dynamic parabolic at the same compact subgroup. -/
theorem isIwasawaPair_dynamicParabolic_of_minimal
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {K : Subgroup (rationalPoints G)}
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    IsIwasawaPair (Dynamic.parabolic χ).rationalPoints K := by
  have hB : standardParabolic i ν ∅ = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) :=
    standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν
  obtain ⟨P₀, j₀, hj₀, heq₀⟩ := isMinimalParabolicFunctor_iff_exists.mp
    (genericMinimalParabolic F G hG S i hi ν hν)
  have hpoints₀ : (rationalPoints.map j₀).range = standardParabolicPoints i ν ∅ := by
    change (SubgroupFunctor.range j₀).rationalPoints = _
    rw [heq₀, ← hB]
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let j := Dynamic.Affine.parabolicHom χ
  have hj : IsParabolicSubgroup j :=
    Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic parabolicDynamic hG χ
  obtain ⟨Q, j', hj', hle⟩ := parabolicContainsMinimalStatement F G hG _ j hj
  obtain ⟨g, e, hcomp⟩ := minimalParabolicConjugacy F G hG P₀ Q j₀ j' hj₀ hj'
  have hrange : ((rationalPoints.map j₀).range.map (MulAut.conj g).toMonoidHom) ≤
      (rationalPoints.map j).range := by
    rw [← rationalPoints_range_comp_innerIso, hcomp]
    change (SubgroupFunctor.range (e.hom ≫ j')).rationalPoints ≤ _
    rw [SubgroupFunctor.range_iso_comp]
    exact hle _
  rw [SubgroupFunctor.rationalPoints_eq_range (Dynamic.Affine.isRepresentedBy_parabolicHom χ)]
  exact ((hpoints₀ ▸ hPK : IsIwasawaPair (rationalPoints.map j₀).range K).map_conj g).mono hrange

variable [TopologicalSpace F]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology

variable (i ν) (K : Subgroup (rationalPoints G))

/-- Every dynamic parabolic of each actual standard Levi has Iwasawa
factorization with the same preimage of the ambient subgroup. -/
def StandardLeviDynamicIwasawaAt : Prop :=
  ∀ J ⊆ simpleRelativeRoots i ν,
    haveI := leviScheme_isAffineHom i ν J
    ∀ χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ Standard.leviScheme i ν J,
      IsIwasawaPair (Dynamic.parabolic χ).rationalPoints (leviSchemeCompact K i ν J)

set_option maxHeartbeats 900000 in
/-- Transport the literal minimal Levi product to the Levi scheme and apply
the dynamic parabolic product there, with the same compact preimage. -/
theorem standardLeviDynamicIwasawaAt_of_minimal
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (hK : ∀ J ⊆ simpleRelativeRoots i ν,
      IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
        (K.subgroupOf (standardLeviPoints i ν J))) :
    StandardLeviDynamicIwasawaAt i ν K := by
  intro J hJ χ
  have : IsAffineHom (Standard.leviScheme i ν J).X.hom := leviScheme_isAffineHom i ν J
  exact isIwasawaPair_dynamicParabolic_of_minimal
    (standardLevi_isConnectedReductive hG i hi ν hν J hJ)
    (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi)
    (isGenericCocharacter_leviTorusHom hν)
    (isIwasawaPair_leviSchemeCompact hG hi hν hJ (hK J hJ)) χ

end Langlands.HarishChandraSchwartz
