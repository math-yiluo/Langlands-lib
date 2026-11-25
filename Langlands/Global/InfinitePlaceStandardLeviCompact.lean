import Langlands.Global.AdelicStandardLeviCompactAssembly
import Langlands.Global.InfinitePlaceLeviIwasawaRealization
import Langlands.GroupScheme.Dynamic.RCLikeLeviIwasawa
import Langlands.GroupScheme.Dynamic.StarLeviIwasawa
import Langlands.GroupScheme.Dynamic.PresentationComparison
import Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof

/-! # One archimedean compact for all standard Levis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Dynamic

section Cocharacters

variable {k : Type u} [RCLike k] {G C M : GroupScheme (Spec (CommRingCat.of k))}
  {d : ℕ} (rho : MatrixRepresentation G (Fin d))
  {chi eta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}

private theorem restrict_range_star_stable {P : GroupScheme (Spec (CommRingCat.of k))}
    {p : P ⟶ G} {j : C ⟶ G} {e : Fin d → ℤ}
    (hpair : IsDiagonalLeviPair rho chi e p j)
    (hstar : ∀ x ∈ (rho.affineMatrix (CommAlgCat.of k k)).range,
      star x ∈ (rho.affineMatrix (CommAlgCat.of k k)).range) :
    ∀ x ∈ ((rho.restrict j).affineMatrix (CommAlgCat.of k k)).range,
      star x ∈ ((rho.restrict j).affineMatrix (CommAlgCat.of k k)).range := by
  have hs (x : G.affinePoints (CommAlgCat.of k k)) :
      ∃ y, (rho.affineMatrix (CommAlgCat.of k k) y).val =
        star (rho.affineMatrix (CommAlgCat.of k k) x).val := by
    obtain ⟨y, hy⟩ := hstar _ ⟨x, rfl⟩
    exact ⟨y, congrArg Units.val hy⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hpair.restrict_star_stable hs x
  exact ⟨y, Units.ext hy⟩

private theorem hermitianWeights_of_star_stable_centralizer
    (j : C ⟶ G) (hj : (centralizer chi).IsRepresentedBy j)
    (heta : SubgroupFunctor.range eta ≤ centralizer chi)
    (hcomm : centralizer chi ≤ centralizer eta)
    (hstar : ∀ x ∈ ((rho.restrict j).affineMatrix (CommAlgCat.of k k)).range,
      star x ∈ ((rho.restrict j).affineMatrix (CommAlgCat.of k k)).range) :
    GeneralLinear.HasHermitianWeightProjectors (eta ≫ rho) := by
  apply GeneralLinear.HasNormalPositivePoint.hasHermitianWeightProjectors
  let A := CommAlgCat.of k k
  let X := (algSpec (CommRingCat.of k)).obj (op A)
  let t := GeneralLinear.positiveTwoUnit k
  let a : X ⟶ (Gm (Spec (CommRingCat.of k))).X := (Gm.algebraPointsEquiv k).symm t
  have ha := heta X (SubgroupFunctor.mem_range.mpr ⟨a, rfl⟩)
  rw [← hj.2] at ha
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp ha
  obtain ⟨y, hy⟩ := hstar _ ⟨x, rfl⟩
  have hyc : y ≫ j.hom.hom ∈ (centralizer chi).carrier X := by
    rw [← hj.2]
    exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
  have hc := (commute_cocharacter_of_mem_centralizer eta (hcomm X hyc) a).map
    (rho.affineMatrix A)
  have hxrho : (rho.restrict j).affineMatrix A x =
      GeneralLinear.cocharacterUnitsHom (eta ≫ rho) k t := by
    rw [MatrixRepresentation.affineMatrix_restrict, hx]
    exact rho.affineMatrix_cocharacterPointHom_eq_cocharacterUnitsHom eta t
  rw [← MatrixRepresentation.affineMatrix_restrict, hy, hxrho] at hc
  change Commute (star (GeneralLinear.cocharacterUnitsHom (eta ≫ rho) k t))
    (rho.affineMatrix A (cocharacterPointHom eta A t)) at hc
  rw [MatrixRepresentation.affineMatrix_cocharacterPointHom_eq_cocharacterUnitsHom] at hc
  exact ⟨by
    simpa only [Units.coeHom_apply, Units.coe_star] using hc.map (Units.coeHom _)⟩

local instance localAffinePointsTopology (H : GroupScheme (Spec (CommRingCat.of k))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of k k)) :=
  H.affinePointsTopologicalSpace (CommAlgCat.of k k)

private theorem unitarySubgroup_conjugate_baseOfMatrix
    (g : GL (Fin d) k) (hg : (g : Matrix (Fin d) (Fin d) k) ∈ Matrix.unitaryGroup (Fin d) k) :
    (rho.conjugate (GeneralLinear.baseOfMatrix (CommRingCat.of k) g)).affineUnitarySubgroup (S := k) =
      rho.affineUnitarySubgroup (S := k) := by
  let U := (Unitary.toUnits (R := Matrix (Fin d) (Fin d) k)).range
  have hgU : g ∈ U :=
    (Langlands.Group.MatrixPolarCompact.mem_unitarySubgroup (MonoidHom.id _) g).mpr hg
  ext x
  change (rho.conjugate (GeneralLinear.baseOfMatrix (CommRingCat.of k) g)).affineMatrix _ x ∈ U ↔
    rho.affineMatrix _ x ∈ U
  rw [MatrixRepresentation.conjugate_baseOfMatrix_affineMatrix,
    U.mul_mem_cancel_right (U.inv_mem hgU), U.mul_mem_cancel_left hgU]

private theorem isMaximalCompact_comap_affineUnitarySubgroup_of_hermitian [IsAffine G.X.left]
    (hrho : IsClosedSubgroup rho)
    (hstar : ∀ x ∈ (rho.affineMatrix (CommAlgCat.of k k)).range,
      star x ∈ (rho.affineMatrix (CommAlgCat.of k k)).range)
    (m : M ⟶ G) (hm : (centralizer eta).IsRepresentedBy m)
    (hEta : GeneralLinear.HasHermitianWeightProjectors (eta ≫ rho)) :
    CompactIwasawa.IsMaximalCompact
      ((rho.affineUnitarySubgroup (S := k)).comap (M.affinePointsTarget m (CommAlgCat.of k k))) := by
  obtain ⟨g, e, hg, he⟩ :=
    GeneralLinear.exists_unitary_innerIso_comp_eq_diagonalCocharacter (eta ≫ rho) hEta
  let sigma := rho.conjugate (GeneralLinear.baseOfMatrix (CommRingCat.of k) g)
  have hsigmac : IsClosedSubgroup sigma := by
    let : IsClosedImmersion rho.hom.hom.left := hrho
    change IsClosedImmersion (rho.hom.hom.left ≫ _)
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
    infer_instance
  have hSigmad : eta ≫ sigma = GeneralLinear.diagonalCocharacter (Fin d) (CommRingCat.of k) e := by
    simpa only [sigma, MatrixRepresentation.conjugate, Category.assoc] using he
  let p := Affine.parabolicHom eta
  have hpair : IsDiagonalLeviPair sigma eta e p m :=
    ⟨hsigmac, hSigmad, Affine.isRepresentedBy_parabolicHom eta, hm⟩
  have hMax := (hpair.isLeviCompatibleDecomposition_affineUnitarySubgroup
    (rho.conjugate_baseOfMatrix_star_stable g hg hstar)).2.2.2
  rw [unitarySubgroup_conjugate_baseOfMatrix rho g hg] at hMax
  exact hMax

end Cocharacters

end Langlands.GroupScheme.Dynamic

namespace Langlands.Global.InfinitePlaceGroupPoints

open Langlands.GroupScheme AdelicGroupPoints CompactIwasawa

local instance completionPointsTopology {F : Type u} [Field F]
    (H : GroupScheme (Spec (CommRingCat.of F))) (v : NumberField.InfinitePlace F) :
    TopologicalSpace ((completionBaseChange F H v).affinePoints
      (CommAlgCat.of v.Completion v.Completion)) :=
  (completionBaseChange F H v).affinePointsTopologicalSpace _

/-- Every infinite place has a single compact with minimal Iwasawa coverage and
simultaneously maximal compact inverse images in all standard Levis. -/
def InfinitePlaceStandardLeviCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (v : NumberField.InfinitePlace F),
    ∃ K, fam.IsStandardLeviCompact (.inl v) K

set_option maxHeartbeats 1200000 in
theorem infinitePlaceStandardLeviCompact : InfinitePlaceStandardLeviCompactStatement.{u} := by
  intro F _ _ G _ _ _ fam v
  let : IsRCLikeNormedField v.Completion := v.completion_isRCLikeNormedField
  let := IsRCLikeNormedField.rclike v.Completion
  let b := Spec.algebraMap F v.Completion
  let B := GroupScheme.baseChange b
  let Gv := completionBaseChange F G v
  let hGv := isConnectedReductive_completionBaseChange F G fam.connectedReductive v
  let : IsAffineHom Gv.X.hom := hGv.isAffineHom
  let : IsAffine Gv.X.left := isAffine_of_isAffineHom Gv.X.hom
  let A := CommAlgCat.of v.Completion v.Completion
  let p₀ := fam.p fam.minimalIndex
  let j₀ := fam.l fam.minimalIndex ≫ p₀
  let chi (z : cocharacterLattice fam.T) := CommGroupScheme.groupHom z ≫ fam.i
  have hZ := genericCentralizer F G fam.connectedReductive fam.T fam.i fam.maximalSplit fam.ν fam.generic
  have hp₀c : IsClosedSubgroup p₀ := (fam.isCompatible fam.minimalIndex).parabolic.isClosedSubgroup
  have hj₀c : IsClosedSubgroup j₀ :=
    (fam.isCompatible fam.minimalIndex).levi.isClosedSubgroup.comp hp₀c
  let : IsClosedImmersion p₀.hom.hom.left := hp₀c
  let : IsClosedImmersion j₀.hom.hom.left := hj₀c
  have hp₀ : (Dynamic.parabolic (chi fam.ν)).IsRepresentedBy p₀ := by
    refine ⟨Over.mono_of_mono_left _, ?_⟩
    exact (fam.isCompatible fam.minimalIndex).parabolic_eq.trans
      (standardParabolic_empty_eq_dynamic_of_generic fam.i fam.ν fam.connectedReductive fam.maximalSplit fam.generic)
  have hj₀ : (Dynamic.centralizer (chi fam.ν)).IsRepresentedBy j₀ := by
    refine ⟨Over.mono_of_mono_left _, ?_⟩
    rw [(fam.isCompatible fam.minimalIndex).levi_eq, hZ]
    exact standardLevi_empty_eq_torusCentralizer_of_generic fam.i fam.ν
      fam.connectedReductive fam.maximalSplit fam.generic
  let psi (z : cocharacterLattice fam.T) := Dynamic.baseChangeCocharacter b (chi z)
  have hp : (Dynamic.parabolic (psi fam.ν)).IsRepresentedBy (B.map p₀) := by
    rw [Dynamic.parabolic_baseChange]
    exact hp₀.baseChange b
  have hj : (Dynamic.centralizer (psi fam.ν)).IsRepresentedBy (B.map j₀) := by
    rw [Dynamic.centralizer_baseChange]
    exact hj₀.baseChange b
  obtain ⟨d, rho, _, e, hpair, hstar⟩ :=
    (show MatrixRepresentation.HasClosedStarRealization Gv from
      SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement
        v.Completion Gv hGv).hasRCLikeDiagonalStarLeviRealization (psi fam.ν) hp hj
  let U := rho.affineUnitarySubgroup (S := v.Completion)
  have hLocal := hpair.isLeviCompatibleDecomposition_affineUnitarySubgroup hstar
  have hjStar := Dynamic.restrict_range_star_stable rho hpair hstar
  let eG := completionBaseChangeHomeomorph F G v
  have hComm {H : GroupScheme (Spec (CommRingCat.of F))} (j : H ⟶ G)
      (x : (B.obj H).affinePoints A) :
      H.affinePointsTarget j (CommAlgCat.of F v.Completion)
          ((affinePointsBaseChangeMulEquiv F v.Completion v.Completion H).symm x) =
        eG.symm ((B.obj H).affinePointsTarget (B.map j) A x) := by
    apply eG.injective
    rw [eG.apply_symm_apply]
    exact (affinePointsBaseChangeMulEquiv_target F v.Completion v.Completion j
      ((affinePointsBaseChangeMulEquiv F v.Completion v.Completion H).symm x)).trans
        (congrArg ((B.obj H).affinePointsTarget (B.map j) A) (MulEquiv.apply_symm_apply _ _))
  let eP := affinePointsBaseChangeMulEquiv F v.Completion v.Completion (fam.P fam.minimalIndex)
  let eM₀ := completionBaseChangeHomeomorph F (fam.M fam.minimalIndex) v
  have hOriginal := hLocal.transport eP.symm eM₀.symm eG.symm (hComm p₀) (hComm j₀)
  refine ⟨U.map eG.symm.toMonoidHom, ⟨hOriginal.1, hOriginal.2.1⟩, ?_⟩
  intro J
  let j := fam.l J ≫ fam.p J
  let eM := completionBaseChangeHomeomorph F (fam.M J) v
  obtain ⟨z, hz⟩ := StandardLeviSplitComponent.exists_standardLevi_eq_dynamicCentralizer
    fam.connectedReductive fam.maximalSplit.isSplitSubtorus.1 fam.i fam.ν J.val
  have hc : IsClosedSubgroup j :=
    (fam.isCompatible J).levi.isClosedSubgroup.comp (fam.isCompatible J).parabolic.isClosedSubgroup
  let : IsClosedImmersion j.hom.hom.left := hc
  have hrep : (Dynamic.centralizer (psi z)).IsRepresentedBy (B.map j) := by
    rw [Dynamic.centralizer_baseChange]
    exact (show (Dynamic.centralizer (chi z)).IsRepresentedBy j from
      ⟨Over.mono_of_mono_left _, (fam.isCompatible J).levi_eq.trans hz⟩).baseChange b
  let Tv := (CommGroupScheme.baseChange b).obj fam.T
  let iv : Tv.toGrp ⟶ B.obj G := B.map fam.i
  have hZbase : Dynamic.centralizer (psi fam.ν) = torusCentralizer (T := Tv) iv := by
    rw [Dynamic.centralizer_baseChange, hZ, ← torusCentralizer_baseChange]
  have hpsiZ : SubgroupFunctor.range (psi z) ≤ Dynamic.centralizer (psi fam.ν) := by
    rw [hZbase, show psi z = Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom z) ≫ iv from
      Dynamic.baseChangeCocharacter_comp_hom b _ _]
    intro X x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply range_le_torusCentralizer (T := Tv) iv X
    exact SubgroupFunctor.mem_range.mpr
      ⟨y ≫ (Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom z)).hom.hom,
        by simp only [Grp.comp_hom_hom, Category.assoc]⟩
  have hZpsi : Dynamic.centralizer (psi fam.ν) ≤ Dynamic.centralizer (psi z) := by
    rw [hZbase, show psi z = Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom z) ≫ iv from
      Dynamic.baseChangeCocharacter_comp_hom b _ _]
    exact torusCentralizer_le_dynamicCentralizer (T := Tv) iv _
  have hEta := Dynamic.hermitianWeights_of_star_stable_centralizer rho (B.map j₀) hj hpsiZ hZpsi hjStar
  have hMax := Dynamic.isMaximalCompact_comap_affineUnitarySubgroup_of_hermitian rho
    hpair.1 hstar (B.map j) hrep hEta
  change IsMaximalCompact ((U.map eG.symm.toMonoidHom).comap
    ((fam.M J).affinePointsTarget j (CommAlgCat.of F v.Completion)))
  rw [comap_map_eq_of_comm _ _ eM.symm.toMulEquiv eG.symm.toMulEquiv (hComm j)]
  exact hMax.map eM.symm

end Langlands.Global.InfinitePlaceGroupPoints
