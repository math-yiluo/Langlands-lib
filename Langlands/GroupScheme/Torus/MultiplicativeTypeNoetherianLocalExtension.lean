import Langlands.GroupScheme.Torus.MultiplicativeTypeCompleteLocalExtension
import Langlands.GroupScheme.Torus.MultiplicativeTypeFpqcReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypeLocalDetection
import Langlands.GroupScheme.Torus.MultiplicativeTypeEtaleSpecialSplitting
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # reduction from a split special fibre to a noetherian local base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.ExtensionReduction

/-- A split special fibre in an exact split-endpoint extension over a
noetherian local ring gives relative multiplicative type, conditional on
fibral descent, complete-local deformation and local character classification. -/
theorem noetherianLocal_of_splitSpecialFiber
    (hcrit : MultiplicativeTypeFibralCriterionStatement.{u})
    (hdef : MultiplicativeTypeCompleteLocalDeformationStatement.{u})
    (hchar : ∀ (A : Type u) [CommRing A] [IsLocalRing A],
      CompleteLocalExtension.LocalCharacterSurjectivity A)
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (N G Q : GroupScheme (Spec (CommRingCat.of A)))
    [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] [IsAffineHom G.X.hom]
    (i : N ⟶ G) (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hN : RelativeMultiplicativeType.IsDiagonalizable N)
    (hQ : RelativeMultiplicativeType.IsDiagonalizable Q)
    (hs : RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G)) :
    RelativeMultiplicativeType.IsMultiplicativeType G := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have : IsNoetherianRing C := AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  let bc := Spec.algebraMap A C
  let spA := Spec.algebraMap A (IsLocalRing.ResidueField A)
  let spC := Spec.algebraMap C (IsLocalRing.ResidueField C)
  let rκ := IsLocalRing.ResidueField.map (algebraMap A C)
  let bκ := Spec.map (CommRingCat.ofHom rκ)
  have hbκ : bκ ≫ spA = spC ≫ bc := by
    dsimp [bκ, spA, spC, bc, Spec.algebraMap]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 1
  obtain ⟨M, hM, hfg, ⟨e⟩⟩ := hs
  let := hM
  let := hfg
  let eA : (Diagonalizable.groupScheme (CommRingCat.of (IsLocalRing.ResidueField A)) M).toGrp ≅
      (baseChange spA).obj G :=
    (e ≪≫ (Diagonalizable.relativeModelIso (CommRingCat.of (IsLocalRing.ResidueField A)) M).symm).symm
  let eC : (baseChange spC).obj (Diagonalizable.groupScheme (CommRingCat.of C) M).toGrp ≅
      (baseChange spC).obj ((baseChange bc).obj G) :=
    Diagonalizable.baseChangeIso spC M ≪≫ (Diagonalizable.baseChangeIso bκ M).symm ≪≫
      (baseChange bκ).mapIso eA ≪≫
        Descent.pullbackComparison spA bκ (spC ≫ bc) hbκ G ≪≫
          baseChangeCompIso bc spC G
  let F := baseChange bc
  have : Flat (F.obj G).X.hom := by
    change Flat (pullback.snd G.X.hom bc)
    infer_instance
  have : LocallyOfFinitePresentation (F.obj G).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd G.X.hom bc)
    infer_instance
  have : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom bc)
    infer_instance
  have hqC : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (F.map i)) (F.map q) := by
    change RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ((baseChange bc).map i))
      ((baseChange bc).map q)
    simpa only [SubgroupFunctor.range_baseChangeHom] using hq.baseChange bc
  let d := CompleteLocalExtension.diagonalizingIso hdef (hchar C) (F.map i) (F.map q)
    hqC (hN.baseChange bc) (hQ.baseChange bc) M eC
  have hGC : RelativeMultiplicativeType.IsMultiplicativeType (F.obj G) :=
    RelativeMultiplicativeType.IsMultiplicativeType.of_isDiagonalizable
      (RelativeMultiplicativeType.IsDiagonalizable.of_iso d.symm
        (Diagonalizable.isDiagonalizable_groupScheme (CommRingCat.of C) M))
  have : Module.FaithfullyFlat A C := .of_flat_of_isLocalHom
  have hff := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap A C))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : Flat bc := hff.1
  have : Surjective bc := hff.2
  have : QuasiCompact bc := inferInstance
  exact FpqcMultiplicativeType.of_fpqcBaseChange_of_fibralCriterion hcrit G bc hGC

/-- A multiplicative-type residue fibre of a split-endpoint extension over
a noetherian ring has an actual affine fppf diagonalizing neighbourhood. -/
theorem noetherian_exists_diagonalizing_neighbourhood
    (hcrit : MultiplicativeTypeFibralCriterionStatement.{u})
    (hdef : MultiplicativeTypeCompleteLocalDeformationStatement.{u})
    (hchar : ∀ (A : Type u) [CommRing A] [IsLocalRing A],
      CompleteLocalExtension.LocalCharacterSurjectivity A)
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (N G Q : GroupScheme (Spec (CommRingCat.of R)))
    [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] [IsAffineHom G.X.hom]
    (i : N ⟶ G) (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hN : RelativeMultiplicativeType.IsDiagonalizable N)
    (hQ : RelativeMultiplicativeType.IsDiagonalizable Q)
    (p : PrimeSpectrum R)
    (hs : IsMultiplicativeType ((baseChange (Spec.algebraMap R p.asIdeal.ResidueField)).obj G)) :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (b : U ⟶ Spec (CommRingCat.of R)),
      Flat b ∧ LocallyOfFinitePresentation b ∧ p ∈ Set.range b ∧
        RelativeMultiplicativeType.IsDiagonalizable ((baseChange b).obj G) := by
  let E := etaleSpecialSplitting R G p hs
  have : IsNoetherianRing E.ring := E.noetherian
  let A := E.ring
  let B := Localization.AtPrime E.point.asIdeal
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing E.point.asIdeal.primeCompl B inferInstance
  let b := Spec.algebraMap R A
  let ell := Spec.algebraMap A B
  let F := baseChange b
  let K := baseChange ell
  have : Flat (K.obj (F.obj G)).X.hom := by
    change Flat (pullback.snd (pullback.snd G.X.hom b) ell)
    infer_instance
  have : LocallyOfFinitePresentation (K.obj (F.obj G)).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd (pullback.snd G.X.hom b) ell)
    infer_instance
  have : IsAffineHom (K.obj (F.obj G)).X.hom := by
    change IsAffineHom (pullback.snd (pullback.snd G.X.hom b) ell)
    infer_instance
  have hqA : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (F.map i)) (F.map q) := by
    change RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ((baseChange b).map i))
      ((baseChange b).map q)
    simpa only [SubgroupFunctor.range_baseChangeHom] using hq.baseChange b
  have hqB : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (K.map (F.map i))) (K.map (F.map q)) := by
    change RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange ell).map (F.map i))) ((baseChange ell).map (F.map q))
    simpa only [SubgroupFunctor.range_baseChangeHom] using hqA.baseChange ell
  let spB := Spec.algebraMap B (IsLocalRing.ResidueField B)
  let spA := Spec.algebraMap A E.point.asIdeal.ResidueField
  have hsp : spB ≫ ell = spA := by
    dsimp [spB, ell, spA, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hsplit : RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange spB).obj (K.obj (F.obj G))) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (Descent.pullbackComparison ell spB spA hsp (F.obj G) ≪≫ E.iso)
      (Diagonalizable.isDiagonalizable_groupScheme
        (CommRingCat.of E.point.asIdeal.ResidueField) E.characters)
  have hGB := noetherianLocal_of_splitSpecialFiber hcrit hdef hchar B
    (K.obj (F.obj N)) (K.obj (F.obj G)) (K.obj (F.obj Q))
    (K.map (F.map i)) (K.map (F.map q)) hqB
    ((hN.baseChange b).baseChange ell) ((hQ.baseChange b).baseChange ell) hsplit
  have : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : LocallyOfFinitePresentation (F.obj G).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd G.X.hom b)
    infer_instance
  obtain ⟨U, hU, v, hvflat, hvfp, hvpoint, hvdiag⟩ :=
    LocalMultiplicativeType.exists_fppf_diagonalizing_neighbourhood (F.obj G)
      (Langlands.AlgebraicGeometry.LocalEtaleLimit.ofLocalization A E.point) hGB
  let := hU
  let := hvflat
  let := hvfp
  have : Etale b := inferInstanceAs (Etale (Spec.algebraMap R E.ring))
  refine ⟨U, inferInstance, v ≫ b, inferInstance, inferInstance, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hvpoint
    exact ⟨w, by change b (v w) = p; rw [hw]; exact E.point_over⟩
  · exact RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (baseChangeCompIso b v G) hvdiag

end Langlands.GroupScheme.ExtensionReduction
