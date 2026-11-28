import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexQuasiSplitTypeE6
import Langlands.GroupScheme.Rational.NumberFieldTypeE6BranchLeviReduction
import Langlands.GroupScheme.Rational.NumberFieldTypeE6BranchOfIsotropy
import Langlands.GroupScheme.Rational.NumberFieldTypeE6QuadraticSplitIsotropy
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormBaseChange
import Langlands.GroupScheme.Rational.QuasiSplitRootRestriction
import Langlands.GroupScheme.Rational.TypeE6OuterQuadraticStarField
import Langlands.GroupScheme.Reductive.InnerStarWeights
import Langlands.GroupScheme.Reductive.QuasiSplitStarCriterionProof
import Langlands.GroupScheme.SimplyConnected.TypeARankOneOrbit

/-! # Outer quasi-split type E6 via the quadratic star field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000

private local instance affineBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

private local instance finiteTypeBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [LocallyOfFiniteType G.X.hom] : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹LocallyOfFiniteType G.X.hom›

/-- Every simple root of an actual Tits index of a quasi-split group has
nonzero restriction to its maximal split torus. -/
theorem TitsIndexData.mem_distinguishedVertices_of_isQuasiSplit
    {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (hqs : IsQuasiSplit G) (a : d.Vertex) : a ∈ d.distinguishedVertices := by
  have ha : d.pinning.rootDatum.root a.val ∈ roots ((GroupScheme.baseChange
      (algebraBaseMap F (SeparableClosure F))).map d.pinning.inclusion) := by
    rw [← d.pinning.isRootDatum.2.1]
    exact Set.mem_range_self a.val
  have hn := hqs.root_restrict_ne_zero d.splitInclusion d.pinning.inclusion d.torusMap
    d.maximalSplit d.maximalTorus d.square d.pinning.isSplitTorus ha
  change d.rootRestriction a.val ≠ 0
  unfold TitsIndexData.rootRestriction absoluteRootRestriction
  exact fun h => hn ((AddEquiv.map_eq_zero_iff _).mp h)

/-- Over a totally complex number field, vanishing holds for a quadratic
cover splitting a quasi-split E6 group if the outer type A Hasse kernel is trivial. -/
theorem Cocycle.isTrivial_of_quasiSplitE6_quadraticSplittingCover
    (hOuter : NumberFieldOuterTypeAHasseStatement.{u})
    {F L : Type u} [Field F] [NumberField F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [IsGalois F L] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (hF : IsTotallyComplex F) (hsc : IsSimplyConnected G) (hqs : IsQuasiSplit G)
    (hE : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b))
    (hL : Module.finrank F L = 2)
    (hsplit : HasSplitMaximalTorus ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (ξ : Cocycle G (GaloisCocycle.cover F L)) : ξ.IsTrivial := by
  let a := AutomorphicAction.conjugation (𝟙 G)
  obtain ⟨H, t, hHa, ht⟩ := finiteGaloisTwistExistence F L G G inferInstance a ξ
  let : IsAffineHom H.X.hom := hHa
  let j := t.toBaseChangeIso
  have hscH : IsSimplyConnected H := (isSimplyConnected_fieldExtension_iff (K := L) H).mp
    (IsSimplyConnected.of_iso j.symm (isSimplyConnectedFieldExtension F L G hsc))
  let : Smooth H.X.hom := hscH.isSemisimple.isConnectedReductive.smooth
  obtain ⟨dH⟩ := titsIndexExistence F H hscH.isSemisimple
  have hsplitH : HasSplitMaximalTorus ((GroupScheme.baseChange (algebraBaseMap F L)).obj H) := by
    obtain ⟨T, i, hT, hi⟩ := hsplit
    exact ⟨T, i ≫ j.hom, hT, hi.comp_iso j⟩
  obtain ⟨M, _, _, _, _, _, _, ⟨p⟩⟩ := exists_typeE6BranchCentralizerCocycle_of_marked_twist
    d e hE hsc L ξ t ht hscH dH (d.mem_distinguishedVertices_of_isQuasiSplit hqs (e.symm 1))
    (fun eH hEH => dH.typeE6Branch_distinguished_of_not_isAnisotropic hF eH hscH hEH
      (dH.not_isAnisotropic_of_typeE6_quadraticSplit eH hF hscH hEH hL hsplitH))
  obtain ⟨q, _⟩ := p.exists_leviFactorization hsc hE
  have hvanish := q.isTrivial_of_derivedVanishing (fun N _ _ _ _ τ => by
    have hlocal := τ.locallyTrivial_of_totallyComplex hF q.simplyConnected
    by_cases hin : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : q.index.Vertex), q.index.star σ a = a
    · exact numberFieldInnerTypeASimplyConnectedGaloisHasseKernel_of_reducedNormLocality
        Langlands.CentralSimple.numberFieldReducedNormLocality F q.derivedGroup q.index 5
        q.simplyConnected q.absolutelyAlmostSimple ⟨by decide, ⟨q.numbering, q.cartan_eq⟩, hin⟩ N τ hlocal
    · push Not at hin
      exact hOuter F q.derivedGroup q.index 5 q.numbering q.simplyConnected
        q.absolutelyAlmostSimple q.cartan_eq hin N τ hlocal)
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite F L M
  let : IsGalois L M := IsGalois.tower_top_of_isGalois F L M
  exact GaloisCocycle.isTrivial_of_refine F L M ξ hvanish

/-- Inner quasi-split type E6 on arbitrary finite Galois covers over totally
complex number fields. -/
def NumberFieldTotallyComplexQuasiSplitInnerTypeE6VanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
      (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6), IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) → IsQuasiSplit G →
      (∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex), d.star σ a = a) →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
        (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.IsTrivial

/-- Inner quasi-split E6 vanishing and the outer type A Hasse kernel imply
quasi-split E6 vanishing for either star action. -/
def NumberFieldQuasiSplitTypeE6OuterReductionStatement : Prop :=
  NumberFieldTotallyComplexQuasiSplitInnerTypeE6VanishingStatement.{u} →
    NumberFieldOuterTypeAHasseStatement.{u} → NumberFieldTotallyComplexQuasiSplitTypeE6VanishingStatement.{u}

theorem numberFieldQuasiSplitTypeE6OuterReduction : NumberFieldQuasiSplitTypeE6OuterReductionStatement.{u} := by
  intro hInner hOuter F _ _ hF G _ _ d e hsc habs hE hqs L _ _ _ _ ξ
  by_cases hin : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex), d.star σ a = a
  · exact hInner F hF G d e hsc habs hE hqs hin L ξ
  let E := d.starField
  obtain ⟨hquad, hgal, p, f, hcart, hInnerE⟩ := typeE6OuterQuadraticStarField F G d e hE hin
  let : IsGalois F E := hgal
  let : Algebra.IsQuadraticExtension F E := hquad
  have hdeg : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let : FiniteDimensional F E := .of_finrank_pos (by rw [hdeg]; decide)
  let : NumberField E := NumberField.of_module_finite F E
  let : IsTotallyComplex F := hF
  have hEc : IsTotallyComplex E := isTotallyComplex_of_algebra F E
  let : Algebra E (SeparableClosure E) := (separableClosure E (AlgebraicClosure E)).algebra
  let GE := (GroupScheme.baseChange (algebraBaseMap F E)).obj G
  have hscE : IsSimplyConnected GE := isSimplyConnectedFieldExtension F E G hsc
  have habsE : IsAbsolutelyAlmostSimple GE := habs.baseChange_of_algebraicExtension
  have hqsE : IsQuasiSplit GE := hqs.baseChange_of_algebraicExtension
  have hstar (σ : SeparableClosure E ≃ₐ[E] SeparableClosure E) : p.pinning.starAction σ = 1 := by
    apply Subtype.ext
    apply StarActionIndependence.equiv_ext_of_weightMap
    exact p.pinning.starAction_weight_of_inner hscE (fun τ a => congrArg Subtype.val (hInnerE τ a)) σ
  have hspl := (quasiSplitStarCriterion E GE hqsE p.pinning).mpr hstar
  obtain ⟨M, φL, φE, hMfin, hMgal⟩ := TypeE6HasseReduction.exists_common_galois F L E
  let : Algebra L M := φL.toRingHom.toAlgebra
  let : Algebra E M := φE.toRingHom.toAlgebra
  let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq fun x => (φL.commutes x).symm
  let : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun x => (φE.commutes x).symm
  let : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite F E M
  let : IsGalois E M := IsGalois.tower_top_of_isGalois F E M
  have hext : (ξ.baseChangePullback (Spec.algebraMap F E)).IsTrivial :=
    GaloisCocycle.isTrivial_baseChange_of_scalarExtension (M := M) ξ
      (hInner E hEc GE p f hscE habsE hcart hqsE hInnerE M _)
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact ξ.isTrivial_of_baseChange_isTrivial_of_kernel M (ξ.locallyTrivial_of_totallyComplex hF hsc) hext
    (fun τ _ => τ.isTrivial_of_quasiSplitE6_quadraticSplittingCover hOuter d e hF hsc hqs hE hdeg hspl)

end Langlands.GroupScheme
