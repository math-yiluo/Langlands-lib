import Langlands.GroupScheme.RelativeLevi.DynamicStatement
import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Rational.AffineWeilParabolicRadicalTransportProof

/-! # Dynamic parabolics, unipotent radicals and Levi subgroups over any base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Dynamic subgroups of a reductive group scheme are respectively a relative
parabolic, its relative unipotent radical, and a relative Levi subgroup. -/
theorem dynamicRelativeLevi : DynamicRelativeLeviStatement.{u} := by
  intro S G P U Z χ iP iU iZ hG hP hU hZ
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨⟨P₀, p₀, hp₀, _, hP₀⟩, ⟨U₀, u₀, hu₀, _, hU₀⟩,
    ⟨Z₀, z₀, hz₀, _, hZ₀⟩⟩ := dynamicBaseRepresentability S G χ
  have hPc : IsClosedSubgroup iP := hP.isClosedSubgroup hP₀ hp₀
  have hUc : IsClosedSubgroup iU := hU.isClosedSubgroup hU₀ hu₀
  have hZc : IsClosedSubgroup iZ := hZ.isClosedSubgroup hZ₀ hz₀
  have hPs : Smooth P.X.hom :=
    ((dynamicBaseSmoothConnected S G χ P iP).2.1 hP).1
  have hUs : Smooth U.X.hom :=
    ((dynamicBaseSmoothConnected S G χ U iU).1 hU).1
  have hZs : Smooth Z.X.hom :=
    ((dynamicBaseSmoothConnected S G χ Z iZ).2.2 hZ).1
  have hrad (r : U ⟶ P) (hr : r ≫ iP = iU) :
      IsRelativeUnipotentRadical r := by
    have hUr : (Dynamic.unipotent χ).IsRepresentedBy (r ≫ iP) := by
      rw [hr]
      exact hU
    refine ⟨IsClosedSubgroup.of_comp hPc (by rw [hr]; exact hUc), hUs,
      Dynamic.range_unipotentRepresentative_isNormal χ iP r hP hUr, ?_⟩
    intro s
    let b := geometricPoint S s
    have hPb := hP.baseChange b
    rw [← Dynamic.parabolic_baseChange] at hPb
    have hUb := hUr.baseChange b
    rw [← Dynamic.unipotent_baseChange, Functor.map_comp] at hUb
    exact (AffineWeilParabolicRadicalTransport.isGeometricUnipotentRadical_of_isRepresentedBy
      (hG.isConnectedReductive_baseChange b) (Dynamic.baseChangeCocharacter b χ) hPb hUb).1
  refine ⟨⟨hPs, hPc.isAffineHom, hP.1, ?_⟩, hrad, ?_⟩
  · intro s
    have hPs := hP.baseChange (S.fromSpecResidueField s)
    rw [← Dynamic.parabolic_baseChange] at hPs
    exact AffineWeilParabolicRadicalTransport.isParabolicSubgroup_of_isRepresentedBy
      (hG.isConnectedReductive_residueFiber s) _ hPs
  · intro l hl
    let r : U ⟶ P := hP.factorHom iU (by
      rw [hU.2]
      exact Dynamic.unipotent_le_parabolic χ)
    have hr : r ≫ iP = iU := hP.factorHom_comp iU _
    exact ⟨IsClosedSubgroup.of_comp hPc (by rw [hl]; exact hZc), hZs,
      U, r, hrad r hr, Dynamic.isIso_subgroupMultiplication hP hZ hU l r hl hr⟩

end Langlands.GroupScheme
