import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityStatement
import Langlands.Representation.Aubert.General.RationalLeviNormTopology
import Langlands.Representation.Aubert.General.RationalParabolicModulusReduction
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement

/-! # Transport of general reductive unimodularity to literal standard Levis -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General

open MeasureTheory.Measure

section Transport

variable {H : Type u} {K : Type v} [Group H] [Group K]
  [TopologicalSpace H] [TopologicalSpace K]
  [IsTopologicalGroup H] [IsTopologicalGroup K]
  [LocallyCompactSpace H] [LocallyCompactSpace K]

/-- The modular character is preserved by a continuous group isomorphism. -/
theorem modularCharacter_continuousMulEquiv (e : H ≃ₜ* K) (g : H) :
    modularCharacter (e g) = modularCharacter g := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let sourceHaar : Measure H := haar
  let targetHaar : Measure K := sourceHaar.map e
  have : IsHaarMeasure targetHaar := e.isHaarMeasure_map sourceHaar
  have : (sourceHaar.map (fun x => x * g)).Regular :=
    Regular.map (Homeomorph.mulRight g)
  have hright : sourceHaar.map (fun x => x * g) = modularCharacterFun g • sourceHaar := by
    rw [modularCharacterFun_eq_haarScalarFactor sourceHaar g]
    exact isMulLeftInvariant_eq_smul_of_regular _ _
  have hmap : targetHaar.map (fun x => x * e g) = modularCharacterFun g • targetHaar := by
    calc
      targetHaar.map (fun x => x * e g) = sourceHaar.map (fun x => e (x * g)) := by
        rw [map_map (by fun_prop) (by fun_prop)]
        congr 1
        funext x
        exact (map_mul e x g).symm
      _ = (sourceHaar.map (fun x => x * g)).map e := by
        rw [map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = modularCharacterFun g • targetHaar := by
        rw [hright, Measure.map_smul _ (by fun_prop)]
  change modularCharacterFun (e g) = modularCharacterFun g
  rw [modularCharacterFun_eq_haarScalarFactor targetHaar (e g)]
  rw! [hmap]
  simp

end Transport

namespace RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The existing closed representative of a standard Levi is connected
reductive, conditional on the unrestricted dynamic-centralizer theorem. -/
theorem standardLeviScheme_isConnectedReductive
    (hStandard : StandardCocharacterStatement.{u})
    (hCentralizer : DynamicCentralizerReductiveStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν)) :
    IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)) := by
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  have hj := Standard.isRepresentedBy_leviHom i ν (rootSet i ν I)
  rw [(hcompare ζ hζ).2.1] at hj
  exact hCentralizer k G hG (CommGroupScheme.groupHom ζ ≫ i)
    (Standard.leviScheme i ν (rootSet i ν I))
    (Standard.leviHom i ν (rootSet i ν I))
    (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)) hj

section LocalField

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

local instance leviUnimodularityPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]

/-- General reductive unimodularity transfers to the literal standard Levi.
The two unproved structural inputs are explicit. -/
theorem standardLevi_modularCharacter_eq_one
    (hUnimod : RationalReductiveUnimodularityStatement.{u})
    (hCentralizer : DynamicCentralizerReductiveStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
    [LocallyCompactSpace (levi i ν I)] :
    ∀ m : levi i ν I, modularCharacter m = 1 := by
  let M := Standard.leviScheme i ν (rootSet i ν I)
  have hM : IsConnectedReductive M :=
    standardLeviScheme_isConnectedReductive i ν hStandard hCentralizer hG hi hν I
  have := hM.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : TopologicalSpace (RationalPoint k M.X) := pointTopology
  let e : RationalPoint k M.X ≃ₜ* levi i ν I := leviRationalPointHomeomorph i ν I
  have : LocallyCompactSpace (RationalPoint k M.X) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : IsTopologicalGroup (RationalPoint k M.X) :=
    e.toHomeomorph.isInducing.isTopologicalGroup e.toMonoidHom
  have : NonarchimedeanGroup (RationalPoint k M.X) :=
    NonarchimedeanGroup.nonarchimedean_of_emb
      e.symm.toMonoidHom e.symm.toHomeomorph.isOpenEmbedding
  have : T2Space (RationalPoint k M.X) := e.toHomeomorph.isEmbedding.t2Space
  intro m
  have hm := hUnimod k M hM hStandard (e.symm m)
  simpa only [e.apply_symm_apply] using
    (modularCharacter_continuousMulEquiv e (e.symm m)).trans hm

end LocalField

/-- The two remaining general structural inputs imply the exact published
rational-parabolic modulus target, with all its original premises. -/
theorem rationalParabolicModulus_of_reductiveUnimodularity
    (hUnimod : RationalReductiveUnimodularityStatement.{u})
    (hCentralizer : DynamicCentralizerReductiveStatement.{u}) :
    RationalParabolicModulusStatement.{u} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard I hU hP hπ
  have : LocallyCompactSpace (levi i ν I) :=
    ((isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I).isClosed_levi_of_continuous_projection
        hP hπ).locallyCompactSpace
  exact ⟨hUnimod k G hG hStandard,
    standardParabolic_modularCharacter_of_levi i ν hStandard hG hi hν I hU hP hπ
      (standardLevi_modularCharacter_eq_one i ν hUnimod hCentralizer hStandard
        hG hi hν I)⟩

end RationalPointFamily
end Langlands.Aubert.General
