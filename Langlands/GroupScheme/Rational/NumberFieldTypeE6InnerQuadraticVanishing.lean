import Langlands.GroupScheme.Rational.NumberFieldTypeE6BranchLeviReduction
import Langlands.GroupScheme.Rational.NumberFieldTypeE6BranchOfIsotropy
import Langlands.GroupScheme.Rational.TypeE6InnerQuadraticTwistIsotropy
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # Quadratic cover vanishing for split type E6 over totally complex number fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000

section SplitIndex

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- In a split semisimple group the maximal split torus of any index is the
whole absolute maximal torus of that index. -/
theorem TitsIndexData.isIso_torusMap_of_hasSplitMaximalTorus
    (hsplit : HasSplitMaximalTorus G) : IsIso (CommGroupScheme.groupHom d.torusMap) := by
  obtain ⟨T, i, hT, hi⟩ := hsplit
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy F G d.isSemisimple.isConnectedReductive).1
    d.splitTorus T d.splitInclusion i d.maximalSplit (hi.isMaximalSplitTorus hT)
  have hmax : IsMaximalTorus d.splitInclusion := by
    apply (IsMaximalTorus.comp_iso_iff d.splitInclusion (G.innerIso g)).mp
    rw [he]
    exact hi.iso_comp e
  exact hmax.2.2 d.pinning.torus d.pinning.inclusion (CommGroupScheme.groupHom d.torusMap)
    d.maximalTorus.1 d.maximalTorus.2.1 d.square

/-- Every simple vertex of the actual index is distinguished for a split group. -/
theorem TitsIndexData.mem_distinguishedVertices_of_hasSplitMaximalTorus
    (hsplit : HasSplitMaximalTorus G) (a : d.Vertex) : a ∈ d.distinguishedVertices := by
  let : IsIso (CommGroupScheme.groupHom d.torusMap) :=
    d.isIso_torusMap_of_hasSplitMaximalTorus hsplit
  let e := CommGroupScheme.isoOfGroupIso (asIso (CommGroupScheme.groupHom d.torusMap))
  let B := CommGroupScheme.baseChange (algebraBaseMap F (SeparableClosure F))
  let : IsIso (B.map d.torusMap) := (B.mapIso e).isIso_hom
  change ¬ d.rootRestriction a.val = 0
  intro h
  unfold TitsIndexData.rootRestriction absoluteRootRestriction at h
  have hzero := (AddEquiv.map_eq_zero_iff _).mp h
  have hr : d.pinning.rootDatum.root a.val = 0 := by
    apply (cancel_epi (B.map d.torusMap)).mp
    rw [comp_zero]
    exact hzero
  apply d.pinning.rootDatum.root'_ne_zero (i := a.val)
  change d.pinning.rootDatum.toLinearMap (d.pinning.rootDatum.root a.val) = 0
  rw [hr, map_zero]

end SplitIndex

section SplitVanishing

variable {F : Type u} [Field F] [NumberField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

/-- A finite Galois cover cocycle of split E6 over a totally complex number
field is trivial if its actual pure twist is isotropic. -/
theorem Cocycle.isTrivial_of_splitE6_isotropicTwist
    (ξ : Cocycle G (GaloisCocycle.cover F L)) (hF : IsTotallyComplex F)
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (hE : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b))
    (hsc : IsSimplyConnected G) (hsplit : HasSplitMaximalTorus G)
    (t : LocalGroupIso G H (GaloisCocycle.cover F L))
    (ht : t.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ)
    (hscH : IsSimplyConnected H) (dH : TitsIndexData H)
    (hisoH : ¬ IsAnisotropic H) : ξ.IsTrivial := by
  let : IsIso (CommGroupScheme.groupHom d.torusMap) :=
    d.isIso_torusMap_of_hasSplitMaximalTorus hsplit
  have hsplitT : IsSplitTorus d.pinning.torus.toGrp :=
    IsSplitTorus.of_iso (asIso (CommGroupScheme.groupHom d.torusMap)).symm d.maximalSplit.1.1
  obtain ⟨M, _, _, _, _, _, _, ⟨p⟩⟩ :=
    exists_typeE6BranchCentralizerCocycle_of_marked_twist d e hE hsc L ξ t ht hscH dH
      (d.mem_distinguishedVertices_of_hasSplitMaximalTorus hsplit (e.symm 1))
      (fun eH hEH => dH.typeE6Branch_distinguished_of_not_isAnisotropic hF eH hscH hEH hisoH)
  obtain ⟨q, hstar⟩ := p.exists_leviFactorization hsc hE
  have hvanish := q.isTrivial_of_derivedVanishing (fun N _ _ _ _ τ =>
    numberFieldInnerTypeASimplyConnectedGaloisHasseKernel_of_reducedNormLocality
      Langlands.CentralSimple.numberFieldReducedNormLocality F q.derivedGroup q.index 5
      q.simplyConnected q.absolutelyAlmostSimple
      ⟨by decide, ⟨q.numbering, q.cartan_eq⟩, hstar hsplitT⟩ N τ
      (τ.locallyTrivial_of_totallyComplex hF q.simplyConnected))
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite F L M
  let : IsGalois L M := IsGalois.tower_top_of_isGalois F L M
  exact GaloisCocycle.isTrivial_of_refine F L M ξ hvanish

end SplitVanishing

/-- Over a totally complex number field, every degree-two cover cocycle of a
quasi-split simply connected inner group of type E6 is trivial. -/
def NumberFieldTotallyComplexInnerTypeE6QuadraticVanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
      IsSimplyConnected G → IsQuasiSplit G →
      (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
      (∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex), d.star σ a = a) →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
        Module.finrank F L = 2 →
        ∀ ξ : Cocycle G (GaloisCocycle.cover F L), ξ.IsTrivial

theorem numberFieldTotallyComplexInnerTypeE6QuadraticVanishing :
    NumberFieldTotallyComplexInnerTypeE6QuadraticVanishingStatement.{u} := by
  intro F _ _ hF G _ _ d e hsc hqs hE hinner L _ _ _ _ hL ξ
  have hstar (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) : d.pinning.starAction σ = 1 := by
    apply Subtype.ext
    apply StarActionIndependence.equiv_ext_of_weightMap
    exact d.pinning.starAction_weight_of_inner hsc (fun τ a => congrArg Subtype.val (hinner τ a)) σ
  have hsplit := (quasiSplitStarCriterion F G hqs d.pinning).mpr hstar
  let a := AutomorphicAction.conjugation (𝟙 G)
  obtain ⟨H, t, hHa, ht⟩ := finiteGaloisTwistExistence F L G G inferInstance a ξ
  let : IsAffineHom H.X.hom := hHa
  let j := t.toBaseChangeIso
  have hscH : IsSimplyConnected H := (isSimplyConnected_fieldExtension_iff (K := L) H).mp
    (IsSimplyConnected.of_iso j.symm (isSimplyConnectedFieldExtension F L G hsc))
  let : Smooth H.X.hom := hscH.isSemisimple.isConnectedReductive.smooth
  obtain ⟨dH⟩ := titsIndexExistence F H hscH.isSemisimple
  obtain ⟨_, _, _, hisoH⟩ :=
    typeE6InnerQuadraticTwistIsotropy F G d e hsc hqs hE hinner L hL ξ H t ht dH
  exact ξ.isTrivial_of_splitE6_isotropicTwist hF d e hE hsc hsplit t ht hscH dH hisoH

end Langlands.GroupScheme
