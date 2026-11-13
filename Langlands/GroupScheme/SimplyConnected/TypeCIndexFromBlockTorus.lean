import Langlands.GroupScheme.Reductive.AlignedMaximalTorus
import Langlands.GroupScheme.Reductive.TorusTransportPinning
import Langlands.GroupScheme.Reductive.TitsIndexFromSimpleRestrictions
import Langlands.GroupScheme.SimplyConnected.TypeCIndexCoordinates
import Langlands.GroupScheme.SymplecticMatrix.TypeCBlockRestrictions
import Langlands.LinearAlgebra.TypeCBlockPositivity

/-! # Actual type C index coordinates from a prescribed block torus -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Quaternionic.DegreeSplitting SymplecticMatrix

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "Ks" => SeparableClosure K
local notation "bK" => algebraBaseMap K Ks
local notation "F" => GroupScheme.baseChange bK
local notation "C" => CommGroupScheme.baseChange bK
local notation "𝕊" r => splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift (Fin r))
local notation "𝔻" n => splitTorus.commGroupScheme (Spec (CommRingCat.of Ks)) (ULift (Fin n))

/-- Integer coordinates obtained from the standard split torus over the
separable closure, using its canonical base-change identification. -/
def typeCBlockTorusCoordinates (r : ℕ) : characterLattice (𝕊 r) ≃+ (Fin r → ℤ) :=
  (characterLattice.baseChangeEquiv bK (𝕊 r)
    (isSplitTorus_splitTorus (ULift.{u} (Fin r)))).trans
      ((characterLattice.congr (splitTorus.commBaseChangeIso bK (ULift.{u} (Fin r)))).trans
        (GeneralLinear.characterCoordEquiv (Fin r) Ks).toAddEquiv)

set_option maxHeartbeats 800000 in
/-- A maximal split torus with the prescribed repeated-block image yields
actual Tits index data with those simple-root restriction coordinates. -/
theorem exists_typeCIndex_of_blockTorus {degree r n : ℕ}
    (hG : IsSemisimple G) (hd : 0 < degree)
    (s : (𝕊 r).toGrp ⟶ G) (hs : IsMaximalSplitTorus s)
    (Φ : (F).obj G ≅ groupScheme (Fin n) (CommRingCat.of Ks))
    (hΦ : (F).map s ≫ Φ.hom =
      CommGroupScheme.groupHom ((splitTorus.commBaseChangeIso bK (ULift.{u} (Fin r))).hom ≫
        blockTorusHom Ks degree r n) ≫ diagonalTorus (Fin n) (CommRingCat.of Ks)) :
    ∃ d : TitsIndexData G, HasTypeCRestrictionCoordinates d n degree r := by
  classical
  obtain ⟨J, hJ, P, hP, hred, B, e, _hspan, hcart, hroots⟩ :=
    TypeCPinning.exists_coordinateRootDatum_simpleRoots n Ks
  let : Finite J := hJ
  have hSp := SymplecticMatrix.isConnectedReductive (Fin n) Ks
  let q : SplitPinning (groupScheme (Fin n) (CommRingCat.of Ks)) := {
    isConnectedReductive := hSp
    torus := 𝔻 n
    inclusion := diagonalTorus (Fin n) (CommRingCat.of Ks)
    isSplitTorus := isSplitTorus_diagonalTorus (Fin n) Ks
    isMaximalTorus := isMaximalTorus_diagonalTorus (Fin n) Ks
    rootIndex := J
    rootDatum := P
    isRootDatum := hP
    isReduced := hred
    base := B
    pinning := RootPinning.ofSplitMaximalTorus hSp (isSplitTorus_diagonalTorus (Fin n) Ks) _
      (isMaximalTorus_diagonalTorus (Fin n) Ks) P hP B }
  let c := splitTorus.commBaseChangeIso bK (ULift (Fin r))
  let ψ := c.hom ≫ blockTorusHom Ks degree r n
  have hS : IsSplitTorus (𝕊 r).toGrp := hs.1.1
  have hG' := hG.isConnectedReductive
  obtain ⟨T, i, f, hi, hf, E, Φ', he, hψ⟩ :=
    hasAlignedMaximalTorus (S := 𝕊 r) (D := 𝔻 n) hG' hSp hS s hs.1.2
      q.inclusion q.isMaximalTorus q.isSplitTorus Φ ψ hΦ
  let p := GaloisPinningData.ofTorusIso hG' T i hi q E Φ' he
  let g := GaloisPinningData.ofTorusIsoSimpleEquiv hG' T i hi q E Φ' he
  let coords := typeCBlockTorusCoordinates (K := K) r
  have hcoord (a : q.rootIndex) :
      coords (absoluteRootRestriction p (𝕊 r) hS f a) =
        typeCBlockRestriction Ks degree r n (q.rootDatum.root a) := by
    rw [GaloisPinningData.ofTorusIso_absoluteRootRestriction hG' T i hi q E Φ' he
      (𝕊 r) hS f ψ hψ a]
    change GeneralLinear.characterCoordEquiv (Fin r) Ks
      (c.inv ≫ (characterLattice.baseChangeEquiv bK (𝕊 r) hS)
        ((characterLattice.baseChangeEquiv bK (𝕊 r) hS).symm
          (ψ ≫ q.rootDatum.root a))) = _
    rw [AddEquiv.apply_symm_apply]
    change GeneralLinear.characterCoordEquiv (Fin r) Ks
      (c.inv ≫ ((c.hom ≫ blockTorusHom Ks degree r n) ≫ q.rootDatum.root a)) = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  have hsimple (a : q.base.support) :
      coords (absoluteRootRestriction p (𝕊 r) hS f a.val) =
        TypeCBlockWeights.simpleRestriction degree r (e a) := by
    rw [hcoord]
    exact typeCBlockRestriction_simple _ (e a) (hroots a)
  let ℓ : characterLattice (𝕊 r) →ₗ[ℤ] ℤ :=
    ((TypeCBlockWeights.height r).comp coords.toAddMonoidHom).toIntLinearMap
  obtain ⟨ν, hν⟩ := (LinearMap.IsPerfPair.bijective_right (latticePairing (𝕊 r))).surjective ℓ
  have hpair (χ : characterLattice (𝕊 r)) :
      latticePairing (𝕊 r) χ ν = TypeCBlockWeights.height r (coords χ) :=
    LinearMap.congr_fun hν χ
  have hpos : p.SimpleRestrictionsPositive (𝕊 r) hS f ν := by
    intro a ha
    let a' : q.base.support := g.symm ⟨a, ha⟩
    have ha' : coords (absoluteRootRestriction p (𝕊 r) hS f a) =
        TypeCBlockWeights.simpleRestriction degree r (e a') := hsimple a'
    rcases TypeCBlockWeights.simpleRestriction_zero_or_height_pos (r := r) hd (e a') with hz | hp
    · left
      apply coords.injective
      rw [coords.map_zero, ha', hz]
    · right
      rw [hpair, ha']
      exact hp
  let d := p.titsIndexOfSimpleRestrictions hG hi s hs hf hpos
  refine ⟨d, g.symm.trans e, coords, ?_, ?_⟩
  · intro a b
    change p.rootDatum.pairing a.val b.val =
      CartanMatrix.C n (e (g.symm a)) (e (g.symm b))
    rw [GaloisPinningData.ofTorusIso_pairing hG' T i hi q E Φ' he]
    exact hcart (g.symm a) (g.symm b)
  · intro a
    change coords (absoluteRootRestriction p (𝕊 r) hS f a.val) =
      TypeCBlockWeights.simpleRestriction degree r (e (g.symm a))
    exact hsimple (g.symm a)

end Langlands.GroupScheme
