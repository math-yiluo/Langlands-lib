import Langlands.GroupScheme.Rational.QuadraticSplitMaximalTorus
import Langlands.GroupScheme.Rational.TypeE6QuadraticTorusIsotropy
import Langlands.GroupScheme.Reductive.SpecialLinearTorusAutomorphismProof
import Langlands.GroupScheme.Reductive.StarActionFiniteStageTorus
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.Reductive.TitsIndexFieldExtensionCartan
import Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitarySplitReduction
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleReduction
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.LinearAlgebra.TypeANegationWeyl

/-! # The scalar unitary presentation of anisotropic type A split by a quadratic field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.RootDatumNegation

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 100000

private local instance affineBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

section AnisotropicIndex

variable {k K : Type u} [Field k] [Infinite k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

private theorem exists_quadratically_split_torus_index
    (hG : IsAnisotropic G) (hs : IsSemisimple G) (hK : Module.finrank k K = 2)
    (hsp : HasSplitMaximalTorus ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    ∃ d : TitsIndexData G, IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj d.pinning.torus).toGrp := by
  obtain ⟨T, i, hi, hT⟩ := quadraticSplitMaximalTorus k K hK G hs.isConnectedReductive hsp
  let : Smooth G.X.hom := hs.isConnectedReductive.smooth
  let E := SeparableClosure k
  let b := algebraBaseMap k E
  let BE := GroupScheme.baseChange b
  let TE := (CommGroupScheme.baseChange b).obj T
  have hTE := GaloisPinningData.isSplitTorus_separableClosure T hi.1
  have hiE : IsMaximalTorus (T := TE) (BE.map i) :=
    (maximalTorusBaseChange k E G T i hi.1 hi.2.1).mp hi
  have hGE := connectedReductiveFieldExtensionStatement k E G hs.isConnectedReductive
  obtain ⟨J, _, P, hP, hred⟩ := rootDatumExistence E (BE.obj G) hGE TE hTE (BE.map i) hiE
  let B := Langlands.LinearAlgebra.RootDatumBase.base P
  let p : GaloisPinningData k E G :=
    { torus := T
      inclusion := i
      isConnectedReductive := hGE
      isSplitTorus := hTE
      isMaximalTorus := hiE
      rootIndex := J
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := B
      pinning := RootPinning.ofSplitMaximalTorus hGE hTE (BE.map i) hiE P hP B }
  obtain ⟨d₀⟩ := titsIndexExistence k G hs
  let : Subsingleton (d₀.splitTorus.toGrp ⟶ G) :=
    hG.subsingleton_hom_of_isSplitSubtorus d₀.maximalSplit.1 G
  let d : TitsIndexData G :=
    { d₀ with
      pinning := p
      maximalTorus := hi
      torusMap := 0
      square := Subsingleton.elim _ _
      compatible := fun a ha => by
        exfalso
        apply ha
        unfold absoluteRootRestriction
        rw [Functor.map_zero, zero_comp, map_zero] }
  exact ⟨d, hT⟩

omit [Infinite k] [FiniteDimensional k K] [IsGalois k K] in
private theorem exists_numbering_of_typeA_split_pinning
    [Algebra K (SeparableClosure k)] [IsScalarTower k K (SeparableClosure k)]
    (d : TitsIndexData G) (q : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    {n : ℕ} (e : q.base.support ≃ Fin n)
    (hA : ∀ a b, q.rootDatum.pairing a.val b.val = CartanMatrix.A n (e a) (e b)) :
    ∃ f : d.Vertex ≃ Fin n, ∀ a b, d.cartan a b = CartanMatrix.A n (f a) (f b) := by
  let E := SeparableClosure k
  let : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.tower_top (K := k) K
  let qE := q.baseChange (F := E)
  let a := d.splitMaximalTorusRootDatumEquiv q.isSplitTorus q.isMaximalTorus q.isRootDatum
  let aE : RootPairing.Equiv qE.rootDatum d.pinning.rootDatum :=
    a.comp (q.baseChangeRootDatumEquiv (F := E)).symm
  obtain ⟨w, _, hw⟩ :=
    StarActionIndependence.exists_weyl_comp_preserves_base qE d.pinning.toSplitPinning aE
  let r := RootPairing.Equiv.comp w aE
  let v : q.base.support ≃ d.Vertex :=
    (q.baseChangeSimpleEquiv (F := E)).trans (r.indexEquiv.subtypeEquiv hw)
  let f := v.symm.trans e
  refine ⟨f, fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := v.surjective x
  obtain ⟨y, rfl⟩ := v.surjective y
  change d.cartan (v x) (v y) = CartanMatrix.A n (e (v.symm (v x))) (e (v.symm (v y)))
  rw [v.symm_apply_apply, v.symm_apply_apply]
  have hp : d.cartan (v x) (v y) = q.rootDatum.pairing x.val y.val :=
    (r.comp (q.baseChangeRootDatumEquiv (F := E))).toHom.pairing
  exact hp.trans (hA x y)

end AnisotropicIndex

section HermitianDescent

open SpecialLinearTitsCocycle Matrix SU3Root

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
  [IsGalois k K] [Algebra.IsQuadraticExtension k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] {n : ℕ}

private theorem exists_hermitian_presentation_of_outer_discrepancy
    (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of k)) G (cover k K))
    (X : GeneralLinearGroup (Fin (n + 1)) K)
    (hX : HasOuterDiscrepancy E (conjugation k K) X) :
    ∃ J : HermitianMatrix.Form (fieldInvolution k K) (Fin (n + 1)),
      Nonempty (HermitianMatrix.SchemeModel.Presentation k K J G) := by
  let f := AlgHom.id k K
  have htriv : HasTrivialDiscrepancy E f.fieldRange.fixingSubgroup := by
    intro τ Z a g
    have hτ : τ.val = 1 := by
      apply AlgEquiv.ext
      intro x
      exact ((IntermediateField.mem_fixingSubgroup_iff _ _).mp τ.property) x ⟨x, rfl⟩
    rw [hτ, discrepancy_one]
  have hnontrivial : ∃ z : K, (fieldInvolution k K).bar z ≠ z := by
    by_contra! h
    exact conjugation_ne_one k K (AlgEquiv.ext h)
  obtain ⟨J, hJ⟩ := exists_hermitian_outer_representative E f (fieldInvolution k K) hnontrivial
    htriv (conjugation k K) (fun _ => rfl) X hX
  have hin : OuterTypeAHermitian.InnerTrivial K E := by
    intro σ hσ Z a g
    have hs : σ = 1 := AlgEquiv.ext fun x => by
      change σ x = x
      simpa only [Algebra.algebraMap_self, RingHom.id_apply] using hσ x
    rw [hs, discrepancy_one]
  have hout : OuterTypeAHermitian.OuterHermitian K J E := by
    intro σ hσ Z a g
    have hs : σ = conjugation k K := by
      have hs₀ : σ ≠ 1 := by
        rintro rfl
        exact hσ.elim fun y hy => hy rfl
      have htwo : Nat.card (K ≃ₐ[k] K) = 2 :=
        (IsGalois.card_aut_eq_finrank k K).trans (Algebra.IsQuadraticExtension.finrank_eq_two k K)
      obtain ⟨_, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[k] K)).mp htwo
      exact (huniq σ hs₀).trans (huniq _ (conjugation_ne_one k K)).symm
    exact OuterTypeAUnitarySplit.isOuterMatrixFormula_of_hasOuterDiscrepancy E
      (hJ σ (fun y => by rw [hs]; rfl)) Z a g
  let iso := OuterTypeAHermitian.descendedIso K J E hin hout
  exact ⟨J, ⟨HermitianMatrix.SchemeModel.Presentation.ofMatrixPoints k K J G
    (OuterTypeAHermitian.matrixPoints k K J iso)
    (OuterTypeAHermitian.matrixPoints_injective k K J iso)
    (fun T g => OuterTypeAHermitian.mem_range_matrixPoints k K J iso T g)
    (fun a y => OuterTypeAHermitian.matrixPoints_naturality k K J iso a y)⟩⟩

end HermitianDescent

open SpecialLinearTitsCocycle StarActionFiniteStage StarActionIndependence

/-- An anisotropic simply connected group with a type-A split pinning
over a quadratic extension is scalar unitary over that same extension. -/
theorem IsAnisotropic.exists_quadratic_typeA_hermitian_presentation
    {k K : Type u} [Field k] [Infinite k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [Algebra.IsQuadraticExtension k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hG : IsAnisotropic G) (hsc : IsSimplyConnected G)
    (q : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) {n : ℕ}
    (hn : 2 ≤ n) (f : q.base.support ≃ Fin n)
    (hA : ∀ a b, q.rootDatum.pairing a.val b.val = CartanMatrix.A n (f a) (f b)) :
    ∃ J : HermitianMatrix.Form (SU3Root.fieldInvolution k K) (Fin (n + 1)),
      Nonempty (HermitianMatrix.SchemeModel.Presentation k K J G) := by
  have hK := Algebra.IsQuadraticExtension.finrank_eq_two k K
  obtain ⟨d, hT⟩ := exists_quadratically_split_torus_index hG hsc.isSemisimple hK
    ⟨q.torus, q.inclusion, q.isSplitTorus, q.isMaximalTorus⟩
  let E := SeparableClosure k
  let φ : K →ₐ[k] E := IsSepClosed.lift
  let : Algebra K E := φ.toRingHom.toAlgebra
  let : IsScalarTower k K E := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  obtain ⟨e, he⟩ := exists_numbering_of_typeA_split_pinning d q f hA
  have hb : algebraBaseMap K E ≫ algebraBaseMap k K = algebraBaseMap k E := by
    rw [algebraBaseMap, algebraBaseMap, algebraBaseMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq k K E]
  obtain ⟨s, t, r, hinc, hr, hbase, hstar⟩ := exists_stage_torus d.pinning hb hT
  let eK := (r.indexEquiv.subtypeEquiv hbase).trans e
  have hcart (x y : s.base.support) :
      s.rootDatum.pairing x.val y.val = CartanMatrix.A n (eK x) (eK y) := by
    exact (r.toHom.pairing (i := x.val) (j := y.val)).symm.trans
      (he ⟨r.indexEquiv x.val, (hbase x.val).mp x.property⟩
        ⟨r.indexEquiv y.val, (hbase y.val).mp y.property⟩)
  have hscK := isSimplyConnectedFieldExtension k K G hsc
  obtain ⟨c⟩ := exists_coordinatePinnedIso s.toSplitPinning hscK eK hcart
  let p : Presentation d e :=
    { L := K
      embedding := φ
      stage := s
      torusIso := t
      rootEquiv := r
      inclusion_eq := hinc
      tower_commutes := hb
      weight_eq := hr
      base_iff := hbase
      star_eq := hstar
      coordinate := c }
  let σ := SU3Root.conjugation k K
  let τ : E ≃ₐ[k] E := σ.liftNormal E
  have hστ (x : K) : τ (φ x) = φ (σ x) := AlgEquiv.liftNormal_commutes σ E x
  let tG : s.torus.toGrp ≅ d.pinning.torus.toGrp :=
    ⟨CommGroupScheme.groupHom t.hom, CommGroupScheme.groupHom t.inv,
      congrArg CommGroupScheme.groupHom t.hom_inv_id,
      congrArg CommGroupScheme.groupHom t.inv_hom_id⟩
  have hc : IsClosedSubgroup s.inclusion :=
    hinc ▸ d.maximalTorus.2.1.iso_comp tG
  have ht := isTorus_of_isSplitTorus_baseChange K s.isSplitTorus
  have hneg : s.galoisAction σ = negAut s.rootDatum := by
    apply equiv_ext_of_weightMap
    intro x
    rw [galoisAction_weightMap_apply, negAut_weightMap]
    exact hG.quadratic_character_action_eq_neg hc ht hK σ (SU3Root.conjugation_ne_one k K) x
  have hspan : s.rootDatum.corootSpan ℤ = ⊤ := splitSimplyConnectedCorootSpan K _ hscK
    _ s.isSplitTorus _ s.isMaximalTorus s.rootIndex s.rootDatum s.isRootDatum s.isReduced
  have hmove : ∃ v : d.Vertex, d.star τ v ≠ v := by
    by_contra! hall
    have hfixed (a : s.base.support) : (s.starAction σ).val.indexEquiv a.val = a.val := by
      apply r.indexEquiv.injective
      exact (p.star_vertex σ τ hστ a).trans
        (congrArg Subtype.val (hall ⟨r.indexEquiv a.val, (hbase a.val).mp a.property⟩))
    have hu : s.starAction σ = 1 := by
      apply Subtype.ext
      exact InnerTypeANormOneReduction.aut_eq_one_of_simple s.base hspan _ hfixed
    exact Langlands.TypeANegationWeyl.negAut_not_mem_weylGroup s.rootDatum s.base eK hcart hspan hn
      (hneg ▸ (s.starAction_eq_one_iff σ).mp hu)
  let hAut := SpecialLinearTorusAutomorphism.specialLinearTorusAutomorphism
  let X := p.discrepancyMatrices hAut σ
  have hX : HasOuterDiscrepancy p.localIso σ X :=
    OuterTypeAUnitarySplit.hasOuterDiscrepancy_of_matrix p.localIso (fun Z a g =>
      (p.hasTitsMatrixFormulas_discrepancyMatrices hAut σ τ hστ Z a g).2 hmove)
  exact exists_hermitian_presentation_of_outer_discrepancy p.localIso X hX

/-- An anisotropic simply connected group of type A of rank at least two
that splits on a quadratic cover has a scalar Hermitian presentation
over that quadratic field. -/
def AnisotropicQuadraticTypeAScalarPresentationStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Infinite k] [Field K] [Algebra k K]
      [FiniteDimensional k K] [IsGalois k K] [Algebra.IsQuadraticExtension k K]
      (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom], IsAnisotropic G → IsSimplyConnected G →
    ∀ (q : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
      (n : ℕ), 2 ≤ n →
      ∀ (f : q.base.support ≃ Fin n),
        (∀ a b, q.rootDatum.pairing a.val b.val = CartanMatrix.A n (f a) (f b)) →
        ∃ J : HermitianMatrix.Form (SU3Root.fieldInvolution k K) (Fin (n + 1)),
          Nonempty (HermitianMatrix.SchemeModel.Presentation k K J G)

theorem anisotropicQuadraticTypeAScalarPresentation :
    AnisotropicQuadraticTypeAScalarPresentationStatement.{u} := by
  intro k K _ _ _ _ _ _ _ G _ _ hG hsc q n hn f hA
  exact hG.exists_quadratic_typeA_hermitian_presentation hsc q hn f hA

end Langlands.GroupScheme
