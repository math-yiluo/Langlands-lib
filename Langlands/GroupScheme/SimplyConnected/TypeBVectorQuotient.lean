import Langlands.GroupScheme.SimplyConnected.TypeDVectorQuotient
import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.OddOrthogonalMatrix.FullVectorCentralIsogeny
import Langlands.GroupScheme.CentralIsogeny.TorusKernelGalois
import Langlands.GroupScheme.Torus.FundamentalWeightGaloisRootSpan
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # The descended actual vector quotient of a numbered type-B group -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

variable (n : ℕ) (e : d.Vertex ≃ Fin n) (hn : 2 ≤ n) (hsc : IsSimplyConnected G)

/-- The supplied actual type-B numbering determines a split vector isogeny package. -/
def typeBVectorCentralIsogeny
    (he : ∀ a b, d.cartan a b = CartanMatrix.B n (e a) (e b)) :
    OddOrthogonalMatrix.TypeBNumbering.VectorCentralIsogeny (n := n)
      d.pinning.rootDatum
      ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map d.pinning.inclusion) := by
  letI := d.pinning.isReduced
  haveI : IsAffineHom
      ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj G).X.hom := by
    change IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap K (SeparableClosure K)))
    infer_instance
  exact OddOrthogonalMatrix.TypeBNumbering.vectorCentralIsogeny
    d.pinning.rootDatum d.pinning.base (d.pinning_corootSpan_eq_top hsc) hn e _
    d.pinning.isConnectedReductive d.pinning.isSplitTorus
    d.pinning.isMaximalTorus d.pinning.isRootDatum he

/-- The ordinary Galois action preserves the exact torus character image. -/
theorem typeBVectorCentralIsogeny_characterImage_galois
    (he : ∀ a b, d.cartan a b = CartanMatrix.B n (e a) (e b))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    (characterLattice.comapHom (CommGroupScheme.groupHom
      (d.typeBVectorCentralIsogeny n e hn hsc he).torusMap)).toIntLinearMap.range.map
        (characterLattice.galoisRepresentation K (SeparableClosure K) d.pinning.torus σ) =
      (characterLattice.comapHom (CommGroupScheme.groupHom
        (d.typeBVectorCentralIsogeny n e hn hsc he).torusMap)).toIntLinearMap.range := by
  rw [(d.typeBVectorCentralIsogeny n e hn hsc he).characterImage]
  exact Langlands.RootDatum.map_rootSpan_weightEquiv d.pinning.rootDatum (d.pinning.galoisAction σ)

/-- An actual affine ground-field quotient recovers the full split odd vector map. -/
def typeBVectorQuotientRecovery
    (he : ∀ a b, d.cartan a b = CartanMatrix.B n (e a) (e b)) :
    Descent.CentralIsogenyRecovery (algebraBaseMap K (SeparableClosure K))
      ((d.typeBVectorCentralIsogeny n e hn hsc he).fullMap _ _ hn) := by
  let s := d.typeBVectorCentralIsogeny n e hn hsc he
  have : IsAffine (OddOrthogonalMatrix.groupScheme (Fin n) (SeparableClosure K)).X.left :=
    isAffine_of_isAffineHom (OddOrthogonalMatrix.groupScheme (Fin n) (SeparableClosure K)).X.hom
  exact Descent.centralIsogenyRecoveryOfStableTorusCharacterImage
    (s.central_fullMap _ _ hn) d.pinning.isConnectedReductive d.pinning.isMaximalTorus
    (OddOrthogonalMatrix.isSplitSubtorus_diagonalTorus (Fin n) (SeparableClosure K)).2
    (SymplecticMatrix.isSplitTorus_diagonalTorus (Fin n) (SeparableClosure K))
    (s.commutes_fullMap _ _ hn) (d.typeBVectorCentralIsogeny_characterImage_galois n e hn hsc he)

/-- Local finite type of the full split odd model descends to the actual quotient. -/
theorem typeBVectorQuotientRecovery_locallyOfFiniteType
    (he : ∀ a b, d.cartan a b = CartanMatrix.B n (e a) (e b)) :
    LocallyOfFiniteType (d.typeBVectorQuotientRecovery n e hn hsc he).obj.X.hom := by
  let R := d.typeBVectorQuotientRecovery n e hn hsc he
  let b := algebraBaseMap K (SeparableClosure K)
  have hiso : IsIso R.iso.hom.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso R.iso.hom
  have hbc : LocallyOfFiniteType ((GroupScheme.baseChange b).obj R.obj).X.hom := by
    rw [← Over.w R.iso.hom.hom.hom]
    infer_instance
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc K (SeparableClosure K)
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @LocallyOfFiniteType) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := R.obj.X.hom) (g := b) ⟨⟨hsurj, hflat⟩, hqc⟩ hbc

end Langlands.GroupScheme.TitsIndexData
