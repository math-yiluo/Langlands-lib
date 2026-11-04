import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesStatement
import Langlands.GroupScheme.Rational.StandardLeviLieWeights
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Rational.PositiveRootInduction

/-! # Proof of the standard-family comparison inside an actual Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Centralizer

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom L.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType L.X.hom]
  (hDynamic : DynamicLieStatement.{u})
  (i : T.toGrp ⟶ G) (iL : T.toGrp ⟶ L) (j : L ⟶ G)
  (hcomp : iL ≫ j = i) (ζ : cocharacterLattice T)
  (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)

include hDynamic hj hcomp

/-- The actual roots of a represented cocharacter centralizer are exactly the
ambient roots with zero pairing, for the same acting torus. -/
theorem relativeRoots_centralizer_factor :
    relativeRoots iL = {α | α ∈ relativeRoots i ∧ latticePairing T α ζ = 0} := by
  have : Mono j.hom.hom := hj.1
  ext α
  constructor
  · intro hα
    exact ⟨relativeRoots_subset_of_factor hj iL hcomp hα,
      relativeRoot_pairing_eq_zero_of_le_dynamicCentralizer hj iL hcomp ζ le_rfl hα⟩
  · rintro ⟨hα, hzero⟩
    refine ⟨hα.1, ?_⟩
    intro hbot
    have hmap : (weightSpace iL α).map (Lie.targetMapLinear j _) = weightSpace i α := by
      apply le_antisymm
      · rintro X ⟨Y, hY, rfl⟩
        have h := lieKernelHomLinear_mem_weightSpace j iL α hY
        rwa [hcomp] at h
      · intro X hX
        have hmem : X.toMul.val ∈
            (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier _ := by
          apply (hDynamic k G _ X.toMul).1.mpr
          have heq : ζ ≫ α = Gm.powerHom _ 0 := by
            apply (gmEndEquiv k).injective
            simpa only [latticePairing_apply, Gm.powerHom, zero_smul, map_zero] using hzero
          have h := weightSpace_le_comp ζ i α hX
          rwa [heq] at h
        obtain ⟨Y, hY⟩ := (hj.mem_range_lieKernelHomLinear X).mpr hmem
        refine ⟨Y, ?_, hY⟩
        apply (lieKernelHomLinear_mem_weightSpace_iff j iL α Y).mp
        rw [hcomp, hY]
        exact hX
    rw [hbot, Submodule.map_bot] at hmap
    exact hα.2 hmap.symm

end Centralizer

/-- The exact simple-root and all-test standard-family comparison. -/
theorem standardLeviStandardFamilies : StandardLeviStandardFamiliesStatement.{u} := by
  intro hDynamic hStandard k _ G hG T i hi ν hν J hJ L hL j hj hjc
  have := hG.isAffineHom
  have := hL.isAffineHom
  have := hG.smooth
  have := hL.smooth
  have := hi.isSplitSubtorus.mono
  let iL := standardLeviTorusFactor i ν J hj
  have hcomp : iL ≫ j = i := standardLeviTorusFactor_comp i ν J hj
  have hiL : IsMaximalSplitTorus iL :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν J hj hjc
  obtain ⟨⟨ζ, hζ⟩, hcomparison⟩ := hStandard k G hG T i hi ν hν J hJ
  have hrep : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j := by
    rw [← (hcomparison ζ hζ).2.1]
    exact hj
  have hroots := relativeRoots_centralizer_factor hDynamic i iL j hcomp ζ hrep
  have hrootssub : relativeRoots iL ⊆ relativeRoots i :=
    relativeRoots_subset_of_factor hj iL hcomp
  have hνL : IsGenericCocharacter iL ν := fun α hα => hν α (hrootssub hα)
  have hsimple : simpleRelativeRoots iL ν = J := by
    apply Set.Subset.antisymm
    · intro α hα
      have hαambient : α ∈ positiveRelativeRoots i ν := ⟨hrootssub hα.1.1, hα.1.2⟩
      have hαzero : latticePairing T α ζ = 0 := (hroots ▸ hα.1.1).2
      have hαsimple : α ∈ simpleRelativeRoots i ν := by
        refine ⟨hαambient, ?_⟩
        rintro ⟨β, hβ, γ, hγ, heq⟩
        have hbnonneg := hζ.pairing_nonneg_of_positive i ν hβ
        have hgnonneg := hζ.pairing_nonneg_of_positive i ν hγ
        have hsum : latticePairing T β ζ + latticePairing T γ ζ = 0 := by
          simpa only [heq, map_add, LinearMap.add_apply] using hαzero
        have hbzero : latticePairing T β ζ = 0 := by omega
        have hgzero : latticePairing T γ ζ = 0 := by omega
        exact hα.2 ⟨β, ⟨hroots.symm ▸ ⟨hβ.1, hbzero⟩, hβ.2⟩,
          γ, ⟨hroots.symm ▸ ⟨hγ.1, hgzero⟩, hγ.2⟩, heq⟩
      by_contra hαJ
      have := hζ.2.2 α hαsimple hαJ
      omega
    · intro α hα
      have hαsimple := hJ hα
      have hαL : α ∈ relativeRoots iL := hroots.symm ▸ ⟨hαsimple.1.1, hζ.2.1 α hα⟩
      refine ⟨⟨hαL, hαsimple.1.2⟩, ?_⟩
      rintro ⟨β, hβ, γ, hγ, heq⟩
      exact hαsimple.2 ⟨β, ⟨hrootssub hβ.1, hβ.2⟩,
        γ, ⟨hrootssub hγ.1, hγ.2⟩, heq⟩
  refine ⟨hsimple, hνL, ?_⟩
  intro K hK
  obtain ⟨⟨eta, heta⟩, hKcomparison⟩ := hStandard k G hG T i hi ν hν K (hK.trans hJ)
  have hetaL : IsStandardCocharacter iL ν K eta := by
    refine ⟨?_, heta.2.1, ?_⟩
    · rwa [hsimple]
    · intro α hα hαK
      exact heta.2.2 α (hJ (hsimple ▸ hα)) hαK
  have hLcomparison := (hStandard k L hL T iL hiL ν hνL K hetaL.1).2 eta hetaL
  rcases hKcomparison eta heta with ⟨hP, hM, hU⟩
  rcases hLcomparison with ⟨hPL, hML, hUL⟩
  rw [hPL, hML, hUL, hP, hM, hU]
  have hχ : (CommGroupScheme.groupHom eta ≫ iL) ≫ j =
      CommGroupScheme.groupHom eta ≫ i := by rw [Category.assoc, hcomp]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hχ] using
      Dynamic.parabolic_eq_comap_of_isClosedSubgroup (CommGroupScheme.groupHom eta ≫ iL) j hjc
  · simpa only [hχ] using
      Dynamic.centralizer_eq_comap_of_isClosedSubgroup (CommGroupScheme.groupHom eta ≫ iL) j hjc
  · simpa only [hχ] using
      Dynamic.unipotent_eq_comap_of_isClosedSubgroup (CommGroupScheme.groupHom eta ≫ iL) j hjc

end Langlands.GroupScheme
