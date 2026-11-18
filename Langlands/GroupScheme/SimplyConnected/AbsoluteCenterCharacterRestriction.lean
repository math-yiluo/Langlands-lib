import Langlands.GroupScheme.SimplyConnected.TypeD4CenterCharacters
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof
import Langlands.GroupScheme.Reductive.SplitExistence
import Langlands.GroupScheme.Reductive.SplitCentralIsogenyExistenceProof
import Langlands.GroupScheme.Reductive.SplitSemisimplicity
import Langlands.GroupScheme.CentralIsogeny.TorusKernelGalois
import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisExactnessProof
import Langlands.LinearAlgebra.AdjointRootDatum

/-! # Kernel of restriction to the actual full centre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TitsIndexData

open Langlands.LinearAlgebra

/-- The universal point of the diagonalizable quotient detects membership
in the full integral character submodule. -/
private theorem mem_of_trivial_on_annihilator
    {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (N : Submodule ℤ (characterLattice T))
    (χ : characterLattice T)
    (hχ : ∀ (U : Over (Spec (CommRingCat.of k))) (y : U ⟶ T.X),
      y ∈ (characterLattice.annihilatorSubgroupFunctor T N).carrier U →
        characterLattice.pointCharacters T U y (.ofAdd χ) = 1) : χ ∈ N := by
  let A := Diagonalizable.groupScheme (CommRingCat.of k) (characterLattice T ⧸ N)
  let ψ := Diagonalizable.characterPointsEquiv (CommRingCat.of k)
    (characterLattice T ⧸ N) A.X (𝟙 A.X)
  let c := characterLattice.pointCharactersEquiv T hT A.X
  let φ := ψ.comp (AddMonoidHom.toMultiplicative (N.mkQ.toAddMonoidHom))
  let y := c.symm φ
  have hy (weight : characterLattice T) :
      characterLattice.pointCharacters T A.X y (.ofAdd weight) = ψ (.ofAdd (N.mkQ weight)) := by
    change c y (.ofAdd weight) = φ (.ofAdd weight)
    rw [c.apply_symm_apply φ]
  have hyN : y ∈ (characterLattice.annihilatorSubgroupFunctor T N).carrier A.X := by
    intro weight hweight
    have hzero : N.mkQ weight = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hweight
    rw [hy, hzero, ofAdd_zero, map_one]
  have hψ : ψ (.ofAdd (N.mkQ χ)) = ψ (.ofAdd (0 : characterLattice T ⧸ N)) := by
    rw [← hy, hχ A.X y hyN, ofAdd_zero, map_one]
  have hclass : N.mkQ χ = 0 := Multiplicative.ofAdd.injective
    (MultiplicativeTypeGaloisExactness.characterPointsEquiv_id_injective (K := k)
      (characterLattice T ⧸ N) hψ)
  exact (Submodule.Quotient.mk_eq_zero N).mp hclass

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G)

/-- Restriction of actual absolute torus characters to the full geometric
centre selected by the index datum. -/
def centerCharacterRestriction :
    characterLattice d.pinning.toSplitPinning.torus →ₗ[ℤ]
      characterLattice
        ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj
          d.toralCenter.group) :=
  (characterLattice.precompose
    ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
      d.toralCenter.torusMap)).toIntLinearMap

/-- The kernel of actual character restriction is the integral root span. -/
theorem ker_centerCharacterRestriction :
    LinearMap.ker d.centerCharacterRestriction = d.pinning.rootDatum.rootSpan ℤ := by
  classical
  apply le_antisymm _ (Submodule.span_le.mpr ?_)
  · intro χ hχ
    let L := SeparableClosure K
    let b := algebraBaseMap K L
    let H := (GroupScheme.baseChange b).obj G
    let T := (CommGroupScheme.baseChange b).obj d.pinning.torus
    change characterLattice T at χ
    let i : T.toGrp ⟶ H := d.pinning.toSplitPinning.inclusion
    let P := d.pinning.rootDatum
    let : Finite d.pinning.rootIndex := d.pinning.finiteRootIndex
    let : P.IsReduced := d.pinning.isReduced
    have hH : IsSemisimple H := isSemisimpleFieldExtension K L G d.isSemisimple
    have hHr := d.pinning.isConnectedReductive
    have hfin : Finite (characterLattice T ⧸ P.rootSpan ℤ) :=
      (splitSemisimpleRootDatum L H hHr T d.pinning.isSplitTorus
        i d.pinning.isMaximalTorus d.pinning.rootIndex P d.pinning.isRootDatum).1.mp hH
    obtain ⟨Q, hQ, T', i', hT', hi', P', hP', ⟨e⟩⟩ :=
      splitReductiveExistence L d.pinning.rootIndex (P.rootSpan ℤ)
        (Module.Dual ℤ (P.rootSpan ℤ)) (AdjointRootDatum.rootDatum P) inferInstance
    let f : RootPairing.Hom P' P := (AdjointRootDatum.fromRootDatum P).comp e.symm.toHom
    have hfw : Function.Injective f.weightMap :=
      (AdjointRootDatum.injective_fromRootDatum_weightMap P).comp
        e.symm.bijective_weightMap.injective
    have hfc : Function.Injective f.coweightMap :=
      e.symm.bijective_coweightMap.injective.comp
        (AdjointRootDatum.injective_fromRootDatum_coweightMap P hfin)
    obtain ⟨φ, t, hsquare, hweight, hφ⟩ :=
      splitCentralIsogenyExistence L H Q hHr hQ T T' d.pinning.isSplitTorus hT'
        i i' d.pinning.isMaximalTorus hi' d.pinning.rootIndex d.pinning.rootIndex
        P P' d.pinning.isRootDatum hP' f hfw hfc
    let N := (characterLattice.comapHom (CommGroupScheme.groupHom t)).toIntLinearMap.range
    have hN : N = P.rootSpan ℤ := by
      ext weight
      constructor
      · rintro ⟨ψ, rfl⟩
        change t ≫ ψ ∈ P.rootSpan ℤ
        rw [← hweight ψ]
        exact (e.symm.toHom.weightMap ψ).property
      · intro hmem
        let ψ := e.weightEquiv ⟨weight, hmem⟩
        refine ⟨ψ, ?_⟩
        change t ≫ ψ = weight
        rw [← hweight ψ]
        change (e.symm.weightEquiv ψ).val = weight
        exact congrArg Subtype.val (e.weightEquiv.symm_apply_apply ⟨weight, hmem⟩)
    change χ ∈ P.rootSpan ℤ
    rw [← hN]
    apply mem_of_trivial_on_annihilator d.pinning.isSplitTorus N χ
    intro U y hyN
    have hyC : y ≫ i.hom.hom ∈ (center H).carrier U := by
      apply hφ.kernel_range_le_center U
      rw [range_kernel_eq_torus_characterAnnihilator hφ hHr d.pinning.isMaximalTorus
        hi'.2.1 hT' hsquare]
      exact ⟨y, hyN, rfl⟩
    let w := (CommGroupScheme.baseChange b).map d.toralCenter.torusMap
    have hzC : IsSchemeTheoreticCenter (CommGroupScheme.groupHom w ≫ i) :=
      d.toralCenter_baseChange_isCenter
    rw [← hzC.2] at hyC
    obtain ⟨z, hz⟩ := hyC
    change U ⟶ ((CommGroupScheme.baseChange b).obj d.toralCenter.group).X at z
    have hiClosed : IsClosedImmersion i.hom.hom.left := d.pinning.isMaximalTorus.2.1
    let : Mono i.hom.hom.left := (IsClosedImmersion.iff_isFinite_and_mono _).mp hiClosed |>.2
    let : Mono i.hom.hom := Over.mono_of_mono_left _
    have hyz : z ≫ (CommGroupScheme.groupHom w).hom.hom = y := by
      apply (cancel_mono i.hom.hom).mp
      exact hz
    have hzero : w ≫ χ = 0 := hχ
    have hyχ : y ≫ (CommGroupScheme.groupHom χ).hom.hom = 1 := by
      calc
        _ = (z ≫ (CommGroupScheme.groupHom w).hom.hom) ≫
            (CommGroupScheme.groupHom χ).hom.hom := by rw [hyz]
        _ = z ≫ (CommGroupScheme.groupHom (w ≫ χ)).hom.hom :=
          (comp_groupHom_comp z w χ).symm
        _ = 1 := (congrArg (fun c : characterLattice _ =>
          z ≫ (CommGroupScheme.groupHom c).hom.hom) hzero).trans (comp_groupHom_zero z)
    exact (congrArg (Gm.pointsEquiv (Spec (CommRingCat.of L)) U) hyχ).trans (map_one _)
  · rintro _ ⟨a, rfl⟩
    exact d.toralCenter_root_comp_eq_zero a

/-- A character is trivial on the full centre precisely when it belongs
to the integral root lattice. -/
theorem centerCharacterRestriction_eq_zero_iff
    (χ : characterLattice d.pinning.toSplitPinning.torus) :
    d.centerCharacterRestriction χ = 0 ↔ χ ∈ d.pinning.rootDatum.rootSpan ℤ := by
  rw [← d.ker_centerCharacterRestriction]
  rfl

end Langlands.GroupScheme.TitsIndexData
