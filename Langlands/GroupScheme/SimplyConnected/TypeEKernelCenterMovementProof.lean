import Langlands.GroupScheme.Rational.SpecialLinearNumberedWeightTransport
import Langlands.Algebra.DivisionBrauerClass
import Langlands.Algebra.BrauerSplitting
import Langlands.Algebra.CentralDivisionTensorCubeProof
import Langlands.GroupScheme.MatrixRepresentation.ComponentIntertwiners
import Langlands.GroupScheme.Rational.HighestWeightIntertwiners
import Langlands.GroupScheme.Reductive.GaloisPinningIso
import Langlands.GroupScheme.Reductive.GroundAdjointExterior
import Langlands.GroupScheme.Reductive.GroundKernelIsotypicWeights
import Langlands.GroupScheme.Reductive.PinnedIsoAlignment
import Langlands.GroupScheme.Reductive.SpecialLinearHighestWeight
import Langlands.GroupScheme.Reductive.TitsAlgebraTransport
import Langlands.GroupScheme.Reductive.TitsObstructionSimplyConnected
import Langlands.GroupScheme.SimplyConnected.NormOneGaloisPointMatrix
import Langlands.GroupScheme.SimplyConnected.TypeE6KernelMarkedWeights
import Langlands.GroupScheme.SimplyConnected.TypeE7KernelCenterMovement
import Langlands.GroupScheme.SimplyConnected.TypeEKernelCenterMovementStatement

/-! # Full-centre movement in the branch-marked E6 and E7 cases -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace SplitPinning

open Opposite
open scoped Matrix CategoryTheory.MonObj

open MatrixRepresentation

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- The numbering of the supplied based root datum for an actual special-linear
chart, with its first weight realized by the column representation. -/
private theorem numberedFirstWeightOfSpecialLinearIso {m : ℕ} (hm : 2 ≤ m)
    (E : G ≅ SpecialLinear.groupScheme (Fin m) (CommRingCat.of k))
    (hspan : p.rootDatum.corootSpan ℤ = ⊤) :
    ∃ number : p.base.support ≃ Fin (m - 1),
      (∀ a b : p.base.support, p.rootDatum.pairing a b =
        CartanMatrix.A (m - 1) (number a) (number b)) ∧
      p.IsHighestWeight
        (MatrixRepresentation.restrict (SpecialLinear.inclusion (Fin m) (CommRingCat.of k))
          E.hom)
        (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan
          (number.symm ⟨0, by omega⟩)) := by
  classical
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hm
  have hsize : m = n + 1 + 1 := by omega
  clear hn
  subst m
  open SpecialLinear.FinSucc in
  obtain ⟨J, hJ, P, hP, hred, B, num, hspanQ, hnum, hcartan⟩ :=
    exists_coordinateRootDatum (n + 1) k
  let : Finite J := hJ
  let q := SpecialLinear.FinSucc.coordinatePinning P hP hred B
  obtain ⟨g, φ, e, ht, he, hb⟩ := p.exists_inner_comp_based q E
  let s := e.indexEquiv.subtypeEquiv hb
  let number : p.base.support ≃ Fin (n + 1) := s.trans num
  let a := number.symm 0
  have ha : s a = num.symm 0 := s.apply_symm_apply (num.symm 0)
  have hwa (c : p.base.support) :
      e.weightEquiv (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan c) =
        Langlands.RootDatum.fundamentalWeightBasis P B hspanQ (s c) := by
    apply (Langlands.RootDatum.fundamentalWeightBasis P B hspanQ).repr.injective
    ext j
    obtain ⟨i, rfl⟩ := s.surjective j
    rw [Langlands.RootDatum.fundamentalWeightBasis_repr, Langlands.RootDatum.fundamentalWeightBasis_repr,
      Langlands.RootDatum.fundamentalWeightBasis_pairing]
    change q.rootDatum.coroot' (e.indexEquiv i)
      (e.weightEquiv (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan c)) = _
    rw [e.coroot'_weightEquiv]
    change p.rootDatum.toLinearMap
      (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan c)
      (p.rootDatum.coroot i.val) = _
    rw [Langlands.RootDatum.fundamentalWeightBasis_pairing, if_congr s.apply_eq_iff_eq rfl rfl]
  refine ⟨number, ?_, ?_⟩
  · intro i j
    exact (e.toHom.pairing (i := (i : p.rootIndex)) (j := (j : p.rootIndex))).symm.trans
      (hcartan (s i) (s j))
  · change p.IsHighestWeight _ (Langlands.RootDatum.fundamentalWeightBasis _ _ hspan a)
    apply p.isHighestWeight_restrict_of_innerComp E g
    have he' (χ : characterLattice p.torus) :
        e.weightMap χ = characterLattice.congr φ χ := he χ
    apply (isHighestWeight_restrict_iso_iff (E ≪≫ _) φ ht e he' hb _ _).mpr
    change q.IsHighestWeight _ (e.weightEquiv
      (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan a))
    rw [hwa a, ha, SpecialLinear.FinSucc.first_fundamentalWeightBasis hP B num hnum hspanQ]
    exact SpecialLinear.FinSucc.inclusion_isHighestWeight P hP hred B num hnum

end SplitPinning

section Arithmetic

variable {k D : Type u} [Field k] [DivisionRing D] [Algebra k D]
  [FiniteDimensional k D] [Algebra.IsCentral k D]

end Arithmetic

section E6

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

private def normOneColumnChart {H : GroupScheme (Spec (CommRingCat.of k))}
    (D : Type u) [DivisionRing D] [Algebra k D] [FiniteDimensional k D] [Algebra.IsCentral k D]
    (model : H ≅ CentralSimpleUnits.normOne k D) :
    ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj H) ≅
      SpecialLinear.groupScheme (Fin (CentralSimple.reducedDegree k D))
        (CommRingCat.of (SeparableClosure k)) :=
  (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).mapIso model ≪≫
    CentralSimpleUnits.Splitting.splittingIso k D (CentralSimple.separableClosureChart k D)

open MatrixRepresentation CentralSimpleUnits.SplitRepresentation CentralSimpleUnits.TitsDescent in
set_option maxHeartbeats 800000 in
/-- The column representation on an actual norm-one model recovers the original algebra. -/
private theorem normOneColumnObstruction
    (a : GaloisPinningData k (SeparableClosure k) G) (hsc : IsSimplyConnected G)
    (D : Type u) [DivisionRing D] [Algebra k D] [FiniteDimensional k D] [Algebra.IsCentral k D]
    (model : G ≅ CentralSimpleUnits.normOne k D) (w : a.starFixedWeights)
    (hhighest : a.toSplitPinning.IsHighestWeight
      (MatrixRepresentation.restrict (SpecialLinear.inclusion (Fin (CentralSimple.reducedDegree k D))
        (CommRingCat.of (SeparableClosure k))) (normOneColumnChart D model).hom) w.val) :
    a.titsObstruction hsc w = Brauer.classOf (Brauer.divisionAlgebra k D) := by
  let L := SeparableClosure k
  let H := CentralSimpleUnits.normOne k D
  let b := algebraBaseMap k L
  let chart := CentralSimple.separableClosureChart k D
  let ρ₀ := representation k D chart
  let ρ := ρ₀.restrict ((GroupScheme.baseChange b).map model.hom)
  have hρ : a.toSplitPinning.IsHighestWeight ρ w.val := by
    simpa only [ρ, ρ₀, representation, normOneColumnChart, restrict_comp, Iso.trans_hom,
      Functor.mapIso_hom] using hhighest
  let : IsAffineHom H.X.hom := inferInstance
  let : IsAffineHom ((GroupScheme.baseChange b).obj H).X.hom := by
    change IsAffineHom (Limits.pullback.snd H.X.hom b)
    infer_instance
  let : Nonempty (Fin (CentralSimple.reducedDegree k D)) := a.nonempty_of_isHighestWeight hρ
  let P (σ : L ≃ₐ[k] L) := (galoisConjugator chart σ).val
  have hPu (σ : L ≃ₐ[k] L) : IsUnit (P σ) := (galoisConjugator chart σ).isUnit
  have hP (σ : L ≃ₐ[k] L) : ρ.Intertwines (galoisTwist σ ρ) (P σ) := by
    have h₀ : ρ₀.Intertwines (galoisTwist σ ρ₀) (P σ) := by
      apply (intertwines_iff_universal_pointMatrix _ _ _).mpr
      rw [pointMatrix_transport]
      exact galoisConjugator_representation_pointMatrix chart σ _ _
    exact intertwines_restrict_galoisTwist σ h₀ model.hom
  have hB : titsAlgebra ρ = (matrixAction chart).fixed := by
    rw [titsAlgebra_eq_twistedFixed ρ hρ.1
      (SplitPinning.IsHighestWeight.intertwiner_eq_scalar a.toSplitPinning hρ) P hPu hP]
    ext X
    exact (mem_fixed_iff_galoisConjugator chart X).symm
  rw [a.titsObstruction_eq_classOf hsc w hρ.isDominantWeight hρ]
  apply Brauer.classOf_eq_of_algEquiv
  change titsAlgebra ρ ≃ₐ[k] D
  exact (Subalgebra.equivOfEq _ _ hB).trans (fixedEquivOfIsGalois chart).symm

set_option maxHeartbeats 900000 in
private theorem false_of_E6_ground_obstruction
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6) (hsc : IsSimplyConnected G)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e)
    (hstar : d.StarIsTrivial) : False := by
  classical
  let p := d.anisotropicKernelIndex
  let a := p.index.pinning
  let q := a.toSplitPinning
  let hkernel := p.isSimplyConnected hsc
  let hspan := p.index.pinning_corootSpan_eq_top hkernel
  have hkernelStar : p.index.StarIsTrivial := by
    intro σ v
    apply p.comparison.vertexEquiv.injective
    rw [p.comparison.vertexEquiv_star σ v]
    apply Subtype.ext
    exact hstar σ (p.comparison.vertexEquiv v).val
  have hfix (lam : characterLattice q.torus) : a.IsStarFixedWeight lam :=
    a.isStarFixedWeight_of_inner hkernel
      (fun σ v => congrArg (fun b : p.index.Vertex => b.val) (hkernelStar σ v)) lam
  let fixed : characterLattice q.torus →+ a.starFixedWeights :=
    { toFun := fun lam => ⟨lam, (a.mem_starFixedWeights lam).mpr (hfix lam)⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let obstruction := (a.titsObstruction hkernel).comp fixed
  have hneutral {lam : characterLattice q.torus} (hground : a.HasGroundMaximalWeight lam) :
      obstruction lam = 0 := by
    obtain ⟨m, τ, hmult, hmax⟩ := hground
    change a.titsObstruction hkernel (fixed lam) = 0
    rw [a.titsObstruction_apply]
    exact a.titsObstructionValue_eq_zero_of_rational hspan
      (GaloisPinningData.isGaloisRational_baseChange τ) (hfix lam) hmult hmax
  let : Fintype d.pinning.toSplitPinning.rootIndex := Fintype.ofFinite _
  let δ := IntegralWeylVector.positiveRootSum d.pinning.toSplitPinning.rootDatum
    d.pinning.toSplitPinning.base
  have hrestrictedGround (O : Finset d.pinning.toSplitPinning.base.support) :
      a.HasGroundMaximalWeight (p.comparison.weightRestriction (δ - d.pinning.simpleRootSum O)) := by
    obtain ⟨m, ρ, hmult, hmax⟩ :=
      d.pinning.exists_groundRepresentation_positiveRootSum_sub_simpleRoots O
    exact TitsIndexData.groundKernelMaximalWeightTransfer
      (fun hk hs => TitsIndexData.eq_of_e6Branch_kernel_and_split_restrictions e h hsc hk hs)
      ρ (δ - d.pinning.simpleRootSum O) hmult hmax
  let marked : characterLattice q.torus :=
    p.comparison.weightRestriction (d.e6DistinguishedRoot e)
  have hmarked : obstruction marked = 0 := by
    have hδ := hneutral (hrestrictedGround ∅)
    rw [GaloisPinningData.simpleRootSum, Finset.sum_empty, sub_zero] at hδ
    have hδm := hneutral (hrestrictedGround {e.symm 1})
    rw [GaloisPinningData.simpleRootSum, Finset.sum_singleton] at hδm
    change obstruction (p.comparison.weightRestriction (δ - d.e6DistinguishedRoot e)) = 0 at hδm
    rwa [map_sub, map_sub, hδ, zero_sub, neg_eq_zero] at hδm
  have hroot (lam : characterLattice q.torus) (hlam : lam ∈ q.rootDatum.rootSpan ℤ) :
      obstruction lam = 0 := by
    let : Fintype q.rootIndex := Fintype.ofFinite _
    let δD := IntegralWeylVector.positiveRootSum q.rootDatum q.base
    exact a.titsObstruction_eq_zero_of_mem_rootSpan hkernel (hfix δD)
      (fun O => a.exists_groundRepresentation_positiveRootSum_sub_simpleRoots O) (fixed lam) hlam
  obtain ⟨D, _, _, _, _, hdegree, ⟨model⟩⟩ :=
    d.anisotropicKernel_divisionModel_of_E6_branch_mark e hsc h hstar
  have hsize : 2 ≤ CentralSimple.reducedDegree k D := by rw [hdegree]; decide
  let : IsAffineHom
      ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj p.kernel).X.hom := by
    change IsAffineHom (Limits.pullback.snd p.kernel.X.hom (algebraBaseMap k (SeparableClosure k)))
    infer_instance
  obtain ⟨number, hcartan, hhighest⟩ :=
    SplitPinning.numberedFirstWeightOfSpecialLinearIso q hsize (normOneColumnChart D model) hspan
  let cast := finCongr (congrArg (· - 1) hdegree)
  let number5 : p.index.Vertex ≃ Fin 5 := number.trans cast
  have hnumber5 (v w : p.index.Vertex) : p.index.cartan v w =
      CartanMatrix.A 5 (number5 v) (number5 w) := by
    change q.rootDatum.pairing v.val w.val = _
    rw [hcartan v w]
    simp only [number5, cast, Equiv.trans_apply, CartanMatrix.A, Matrix.of_apply,
      Fin.ext_iff, finCongr_apply, Fin.val_cast]
    rfl
  have hnumber0 : number5.symm 0 = number.symm ⟨0, by omega⟩ := by
    apply number5.injective
    rw [Equiv.apply_symm_apply]
    change (0 : Fin 5) = cast (number (number.symm ⟨0, by omega⟩))
    rw [Equiv.apply_symm_apply]
    rfl
  let w := Langlands.RootDatum.fundamentalWeightBasis q.rootDatum q.base hspan
    (number5.symm 0)
  have hsum : (3 : ℤ) • w + marked ∈ q.rootDatum.rootSpan ℤ :=
    TitsIndexData.three_zsmul_kernelFirstWeight_add_e6DistinguishedRoot_mem_rootSpan
      e h hsc number5 hnumber5
  have hzero := hroot _ hsum
  rw [map_add, map_zsmul, hmarked, add_zero] at hzero
  have hw : (fixed w).val =
      Langlands.RootDatum.fundamentalWeightBasis q.rootDatum q.base hspan
        (number.symm ⟨0, by omega⟩) := by
    change Langlands.RootDatum.fundamentalWeightBasis q.rootDatum q.base hspan
      (number5.symm 0) = _
    rw [hnumber0]
  have hclass := normOneColumnObstruction a hkernel D model (fixed w) (hw.symm ▸ hhighest)
  apply Langlands.Brauer.three_zsmul_classOf_divisionAlgebra_ne_zero _ _ hdegree
  change (3 : ℤ) • a.titsObstruction hkernel (fixed w) = 0 at hzero
  rwa [← hclass]

end E6

/-- Full-centre movement in both branch-marked exceptional cases. -/
theorem rankOneTypeEKernelCenterMovement : RankOneTypeEKernelCenterMovementStatement.{u} := by
  intro k _ G _ _ d hsc _ _ hstar hcases
  rcases hcases with ⟨e, h⟩ | ⟨e, h⟩
  · exact (false_of_E6_ground_obstruction d e hsc h hstar).elim
  · exact d.hasCenterMovingAutomorphism_of_E7_branch_mark e hsc h hstar

end Langlands.GroupScheme
