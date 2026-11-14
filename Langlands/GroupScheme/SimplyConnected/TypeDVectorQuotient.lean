import Langlands.GroupScheme.SimplyConnected.TypeDVectorQuotientStatement
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.OrthogonalMatrix.VectorCentralIsogeny
import Langlands.GroupScheme.CentralIsogeny.TorusKernelGalois
import Langlands.GroupScheme.Torus.FundamentalWeightGaloisRootSpan
import Langlands.LinearAlgebra.RootDatumSimpleCorootEquiv
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # The descended vector quotient of a numbered type-D group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace TitsIndexData

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- Simple connectedness supplies full integral coroot span for the actual
absolute pinning root datum. -/
theorem pinning_corootSpan_eq_top (hsc : IsSimplyConnected G) :
    d.pinning.rootDatum.corootSpan ℤ = ⊤ := by
  have hs := isSimplyConnectedFieldExtension K (SeparableClosure K) G hsc
  exact splitSimplyConnectedCorootSpan (SeparableClosure K) _ hs _
    d.pinning.isSplitTorus _ d.pinning.isMaximalTorus _
    d.pinning.rootDatum d.pinning.isRootDatum d.pinning.isReduced

variable (n : ℕ) (e : d.Vertex ≃ Fin n) (hn : 4 ≤ n) (hsc : IsSimplyConnected G)

/-- The actual split vector isogeny selected by the supplied numbering of the
absolute pinning. -/
def typeDVectorCentralIsogeny
    (he : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b)) :
    OrthogonalMatrix.TypeDNumbering.VectorCentralIsogeny
      d.pinning.rootDatum d.pinning.base (d.pinning_corootSpan_eq_top hsc) hn e
      ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
        d.pinning.inclusion) := by
  letI := d.pinning.isReduced
  haveI : IsAffineHom
      ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj G).X.hom := by
    change IsAffineHom (Limits.pullback.snd G.X.hom
      (algebraBaseMap K (SeparableClosure K)))
    infer_instance
  exact OrthogonalMatrix.TypeDNumbering.vectorCentralIsogeny
    d.pinning.rootDatum d.pinning.base (d.pinning_corootSpan_eq_top hsc) hn e _
    d.pinning.isConnectedReductive d.pinning.isSplitTorus
    d.pinning.isMaximalTorus d.pinning.isRootDatum he

/-- The vector torus character image is stable under the ordinary Galois
action when the numbered vector vertex is star-fixed. -/
theorem typeDVectorCentralIsogeny_characterImage_galois
    (he : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (hstar : ∀ (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      (e a).val = 0 → d.star τ a = a)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    (characterLattice.comapHom (CommGroupScheme.groupHom
      (d.typeDVectorCentralIsogeny n e hn hsc he).torusMap)).toIntLinearMap.range.map
        (characterLattice.galoisRepresentation K (SeparableClosure K) d.pinning.torus σ) =
      (characterLattice.comapHom (CommGroupScheme.groupHom
        (d.typeDVectorCentralIsogeny n e hn hsc he).torusMap)).toIntLinearMap.range := by
  rw [(d.typeDVectorCentralIsogeny n e hn hsc he).characterImage]
  have hv : (d.pinning.starAction σ).val.indexEquiv (e.symm ⟨0, by omega⟩).val =
      (e.symm ⟨0, by omega⟩).val :=
    congrArg Subtype.val (hstar σ _ (by simp))
  exact d.pinning.galoisAction_map_fundamentalWeightRootSpan
    (d.pinning_corootSpan_eq_top hsc) σ _ hv

/-- An actual affine vector quotient over the ground field, with the exact
isomorphism and quotient equation recovering the chosen split vector map. -/
def typeDVectorQuotientRecovery
    (he : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (hstar : ∀ (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      (e a).val = 0 → d.star τ a = a) :
    Descent.CentralIsogenyRecovery (algebraBaseMap K (SeparableClosure K))
      (d.typeDVectorCentralIsogeny n e hn hsc he).map := by
  let s := d.typeDVectorCentralIsogeny n e hn hsc he
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have : IsAffine
      (identityComponent (OrthogonalMatrix.groupScheme (Fin n)
        (CommRingCat.of (SeparableClosure K)))).X.left :=
    isAffine_of_isAffineHom (identityComponent (OrthogonalMatrix.groupScheme (Fin n)
      (CommRingCat.of (SeparableClosure K)))).X.hom
  exact Descent.centralIsogenyRecoveryOfStableTorusCharacterImage
    s.central d.pinning.isConnectedReductive d.pinning.isMaximalTorus
    (OrthogonalMatrix.isClosedSubgroup_identityTorus (Fin n) (SeparableClosure K))
    (SymplecticMatrix.isSplitTorus_diagonalTorus (Fin n) (SeparableClosure K))
    s.commutes (d.typeDVectorCentralIsogeny_characterImage_galois n e hn hsc he hstar)

variable (he : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (hstar : ∀ (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      (e a).val = 0 → d.star τ a = a)

/-- Finite type of the split orthogonal form descends along the separable
closure, using the actual recovery isomorphism. -/
theorem typeDVectorQuotientRecovery_locallyOfFiniteType :
    LocallyOfFiniteType (d.typeDVectorQuotientRecovery n e hn hsc he hstar).obj.X.hom := by
  let R := d.typeDVectorQuotientRecovery n e hn hsc he hstar
  let b := algebraBaseMap K (SeparableClosure K)
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hiso : IsIso R.iso.hom.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso R.iso.hom
  have hbc : LocallyOfFiniteType ((GroupScheme.baseChange b).obj R.obj).X.hom := by
    rw [← Over.w R.iso.hom.hom.hom]
    infer_instance
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc K (SeparableClosure K)
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @LocallyOfFiniteType) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := R.obj.X.hom) (g := b) ⟨⟨hsurj, hflat⟩, hqc⟩ hbc

/-- The descended quotient has the required full-test-scheme fundamental
weight alignment at every vertex numbered zero. -/
theorem typeDVectorQuotientRecovery_fundamentalWeight (v : d.Vertex) (hv : (e v).val = 0) :
    d.FundamentalWeightTrivialOnKernel v
      (d.typeDVectorQuotientRecovery n e hn hsc he hstar).hom := by
  classical
  let s := d.typeDVectorCentralIsogeny n e hn hsc he
  let R := d.typeDVectorQuotientRecovery n e hn hsc he hstar
  intro χ hχ hχ' U t ht
  have hweight : χ = Langlands.RootDatum.fundamentalWeightBasis
      d.pinning.rootDatum d.pinning.base (d.pinning_corootSpan_eq_top hsc) v := by
    apply Langlands.RootDatumSimpleCorootEquiv.eq_of_pairing_simpleCoroot
      d.pinning.base (d.pinning_corootSpan_eq_top hsc)
    intro j
    rw [Langlands.RootDatum.fundamentalWeightBasis_pairing, d.pinning.isRootDatum.1]
    split_ifs with hj
    · subst j
      exact hχ
    · exact hχ' j hj
  have hv0 : v = e.symm ⟨0, by omega⟩ := by
    apply e.injective
    apply Fin.ext
    simpa using hv
  rw [hweight, hv0]
  apply OrthogonalMatrix.TypeDNumbering.VectorCentralIsogeny.fundamentalWeight_kills_kernel
    d.pinning.rootDatum d.pinning.base (d.pinning_corootSpan_eq_top hsc) hn e _ s U t
  have hcomp :
      (GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
          d.pinning.inclusion ≫ s.map =
        (GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
          (d.pinning.inclusion ≫ R.hom) ≫ R.iso.hom := by
    rw [Functor.map_comp, Category.assoc, R.hom_comp]
  rw [hcomp, Grp.comp_hom_hom, ← Category.assoc, ht, MonObj.one_comp]

end TitsIndexData

/-- The vector quotient exists over the original field with its prescribed
numbered-vertex alignment in every characteristic. -/
theorem typeDVectorQuotient : TypeDVectorQuotientStatement.{u} := by
  intro K _ G _ _ d n e hn hsc _ he hstar
  let R := d.typeDVectorQuotientRecovery n e hn hsc he hstar
  have : IsAffine R.obj.X.left := R.isAffine
  have : IsAffineHom R.obj.X.hom := inferInstance
  exact ⟨R.obj, inferInstance,
    d.typeDVectorQuotientRecovery_locallyOfFiniteType n e hn hsc he hstar,
    R.hom, R.isCentralIsogeny, ⟨R.iso⟩,
    d.typeDVectorQuotientRecovery_fundamentalWeight n e hn hsc he hstar⟩

end Langlands.GroupScheme
