import Langlands.GroupScheme.Rational.NumberFieldInnerTypeAHasseReduction
import Langlands.GroupScheme.Rational.NumberFieldWeilCocycleTransfer
import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.Reductive.TitsIndexFieldExtensionCartan
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.SimplyConnected.TypeDVectorQuotient
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization

/-! # The Hasse kernel for forms of one-vertex groups and their Weil restrictions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.CentralSimple

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section GeometricRank

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [Algebra.IsSeparable F L]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- A geometric isomorphism after separable scalar extension identifies the
full absolute Cartan matrices of two Tits indices. -/
theorem TitsIndexData.exists_vertexEquiv_cartan_of_separableBaseChangeIso
    (d : TitsIndexData G) (e : TitsIndexData H)
    (f : (GroupScheme.baseChange (algebraBaseMap F L)).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap F L)).obj H) :
    ∃ s : d.Vertex ≃ e.Vertex, ∀ a b, e.cartan (s a) (s b) = d.cartan a b := by
  classical
  let K := SeparableClosure F
  let ι : L →ₐ[F] K := IsSepClosed.lift
  let : Algebra L K := ι.toRingHom.toAlgebra
  let : IsScalarTower F L K := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  let τ := (GaloisPointComparison.towerBaseChangeIso F L K G).symm ≪≫
    (GroupScheme.baseChange (algebraBaseMap L K)).mapIso f ≪≫
    GaloisPointComparison.towerBaseChangeIso F L K H
  obtain ⟨φ⟩ := nonempty_rootDatumEquiv_of_iso d.pinning.isConnectedReductive
    e.pinning.isConnectedReductive d.pinning.isSplitTorus e.pinning.isSplitTorus
    d.pinning.isMaximalTorus e.pinning.isMaximalTorus τ d.pinning.isRootDatum e.pinning.isRootDatum
  obtain ⟨w, _, hw⟩ := StarActionIndependence.exists_weyl_comp_preserves_base
    d.pinning.toSplitPinning e.pinning.toSplitPinning φ
  let ψ := RootPairing.Equiv.comp w φ
  let s : d.Vertex ≃ e.Vertex := Equiv.subtypeEquiv ψ.indexEquiv hw
  exact ⟨s, fun _ _ => ψ.toHom.pairing⟩

end GeometricRank

section Hasse

variable {F L : Type u} [Field F] [NumberField F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]

/-- A simply connected absolutely almost-simple group with a one-vertex
absolute diagram satisfies the finite-Galois Hasse kernel under reduced-norm locality. -/
theorem isTrivial_typeAOne_of_reducedNormLocality
    (hn : NumberFieldReducedNormLocalityStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of F))} (hsc : IsSimplyConnected G)
    (habs : IsAbsolutelyAlmostSimple G)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 1)
    (ξ : Cocycle G (GaloisCocycle.cover F L)) (hξ : ξ.LocallyTrivial) : ξ.IsTrivial := by
  have htype : d.HasInnerTypeA 1 := by
    refine ⟨by decide, ⟨e, ?_⟩, d.starIsTrivial_of_equiv_fin_one e⟩
    intro a b
    have h : a = b := e.injective (Subsingleton.elim _ _)
    subst b
    simp only [TitsIndexData.cartan, RootPairing.pairing_same, CartanMatrix.A, Matrix.of_apply]
    simp
  exact numberFieldInnerTypeASimplyConnectedGaloisHasseKernel_of_reducedNormLocality hn
    F G d 1 hsc habs htype L ξ hξ

/-- For the rank-one Hasse argument it suffices to know the simply connected
one-vertex type and absolute almost-simplicity on one group in the form class. -/
theorem isTrivial_typeAOneForm_of_reducedNormLocality
    (hn : NumberFieldReducedNormLocalityStatement.{u})
    {G H : GroupScheme (Spec (CommRingCat.of F))} (hsc : IsSimplyConnected G)
    (habs : IsAbsolutelyAlmostSimple G)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 1)
    (f : (GroupScheme.baseChange (algebraBaseMap F L)).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap F L)).obj H)
    (ξ : Cocycle H (GaloisCocycle.cover F L)) (hξ : ξ.LocallyTrivial) : ξ.IsTrivial := by
  have hscH := (isSimplyConnected_fieldExtension_iff (K := L) H).mp
    (IsSimplyConnected.of_iso f.symm (isSimplyConnectedFieldExtension F L G hsc))
  have habsH : IsAbsolutelyAlmostSimple H := IsAbsolutelyAlmostSimple.of_fieldExtension
    ((habs.baseChange_of_algebraicExtension (K := L)).of_iso f.symm)
  let := hscH.isSemisimple.isConnectedReductive.isAffineHom
  let := hscH.isSemisimple.isConnectedReductive.smooth
  obtain ⟨dH⟩ := titsIndexExistence F H hscH.isSemisimple
  obtain ⟨s, _⟩ := d.exists_vertexEquiv_cartan_of_separableBaseChangeIso dH f
  exact isTrivial_typeAOne_of_reducedNormLocality hn hscH habsH dH (s.symm.trans e) ξ hξ

omit [IsGalois F L] in
/-- A Weil restriction of an actual simply connected group of type A1 inherits
its Hasse kernel on finite field covers of the original base field. -/
theorem isTrivial_weilTypeAOne_of_reducedNormLocality
    (hn : NumberFieldReducedNormLocalityStatement.{u})
    {B : Type u} [Field B] [NumberField B] [Algebra F B] [FiniteDimensional F B]
    {G : GroupScheme (Spec (CommRingCat.of B))} (hsc : IsSimplyConnected G)
    (habs : IsAbsolutelyAlmostSimple G)
    [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 1)
    (ξ : Cocycle (AffineWeil.groupScheme F B G) (GaloisCocycle.cover F L))
    (hξ : ξ.LocallyTrivial) : ξ.IsTrivial := by
  obtain ⟨M, _, _, _, _, r, hl, ht⟩ := AffineWeil.exists_finiteGalois_transfer F B G ξ hξ
  let δ : Cocycle G (GaloisCocycle.cover B M) := (AffineWeil.transferCocycle F B G ξ).refine r
  exact ht (isTrivial_typeAOne_of_reducedNormLocality hn hsc habs d e δ hl)

end Hasse

end Langlands.GroupScheme
