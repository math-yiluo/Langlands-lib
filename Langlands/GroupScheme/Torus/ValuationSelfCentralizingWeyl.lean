import Langlands.GroupScheme.Torus.NoetherianSelfCentralizingWeyl
import Langlands.AlgebraicGeometry.AlgClosedValuativeSpecialization

/-! # Arbitrary-base finite Weyl models from valuation affineness -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Langlands.AlgebraicGeometry

/-- Algebraically closed valuation lifts are stable under arbitrary change of base. -/
theorem HasAlgClosedValuationLifts.baseChange
    {X Y : Scheme.{u}} {f : X ⟶ Y} (H : HasAlgClosedValuationLifts f)
    {T : Scheme.{u}} (g : T ⟶ Y) : HasAlgClosedValuationLifts (pullback.snd f g) := by
  intro K _ _ A b a ha
  have hw : (a ≫ pullback.fst f g) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ (b ≫ g) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, Category.assoc]
  obtain ⟨l, hl₁, hl₂⟩ := H K A (b ≫ g) (a ≫ pullback.fst f g) hw
  refine ⟨pullback.lift l b hl₂, ?_, pullback.lift_snd _ _ _⟩
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullback.lift_fst] using hl₁
  · simpa only [Category.assoc, pullback.lift_snd] using ha.symm

/-- Finiteness of every algebraically closed valuation pullback supplies
restricted valuative lifts of the original morphism. -/
theorem hasAlgClosedValuationLifts_of_finite_pullbacks
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
      (b : Spec (CommRingCat.of A) ⟶ Y), IsFinite (pullback.snd f b)) :
    HasAlgClosedValuationLifts f := by
  intro K _ _ A b a ha
  let p := pullback.snd f b
  let : IsFinite p := H K A b
  have hp : ValuativeCriterion.Existence p := by
    have h : UniversallyClosed p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq p :=
    { R := A
      K := K
      i₁ := pullback.lift a
        (Spec.map (CommRingCat.ofHom (algebraMap A K))) ha
      i₂ := 𝟙 _
      commSq := ⟨by simp [p]⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (hp S).exists_lift
  refine ⟨l ≫ pullback.fst f b, ?_, ?_⟩
  · rw [← Category.assoc, hl₁]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (l ≫ p) ≫ b = b
    rw [hl₂, Category.id_comp]

/-- A quasi-compact separated etale morphism is finite if every pullback to
a valuation subring of an algebraically closed field is finite. -/
theorem isFinite_etale_of_algClosed_valuation_pullbacks
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [IsSeparated f] [Etale f]
    (H : ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
      (b : Spec (CommRingCat.of A) ⟶ Y), IsFinite (pullback.snd f b)) : IsFinite f := by
  have hval : HasAlgClosedValuationLifts f :=
    hasAlgClosedValuationLifts_of_finite_pullbacks f H
  apply EtaleLocalCardinality.finite_of_specializing_pullbacks f
  intro T g
  exact specializingMap_of_algClosed_valuation_lifts _ (hval.baseChange g)

end Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme.SelfCentralizingWeyl

/-- Over an algebraically closed valuation subring, supplied etale affineness
and the supplied Weyl criterion make the ambient group affine. -/
theorem isAffineHom_over_algClosed_valuation
    (hcrit : SelfCentralizingTorusWeylAffinenessStatement.{u})
    (hval : ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
      (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A)),
        QuasiCompact f → IsSeparated f → Etale f → IsAffineHom f)
    (K : Type u) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
    (G : GroupScheme (Spec (CommRingCat.of A)))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasConnectedReductiveResidueFibers G)
    (T : CommGroupScheme (Spec (CommRingCat.of A))) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hself : (torusCentralizer t).IsRepresentedBy t) : IsAffineHom G.X.hom := by
  obtain ⟨N, n, W, q, hnclosed, hn, hN, hsep, hqc, het,
    hflat, hsurj, hfp, hker, haff⟩ :=
    hcrit _ G inferInstance inferInstance inferInstance
      (fun s => ⟨(hG s).connectedSpace, (hG s).isAffineHom⟩)
      T t hT ht hmax hself
  exact haff.mpr (hval K A W.X.left W.X.hom hqc hsep het)

/-- The two supplied affineness inputs force every actual Weyl quotient to
be finite over an arbitrary base. -/
theorem isFinite_suppliedWeyl_of_valuation_affineness
    (hcrit : SelfCentralizingTorusWeylAffinenessStatement.{u})
    (hval : ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
      (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A)),
        QuasiCompact f → IsSeparated f → Etale f → IsAffineHom f)
    (S : Scheme.{u}) (G : GroupScheme S)
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasConnectedReductiveResidueFibers G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hself : (torusCentralizer t).IsRepresentedBy t)
    (N : GroupScheme S) (n : N ⟶ G) (W : GroupScheme S) (q : N ⟶ W)
    (hnclosed : IsClosedSubgroup n) (hn : (torusNormalizer t).IsRepresentedBy n)
    (hqc : QuasiCompact W.X.hom) (hsep : IsSeparated W.X.hom) (het : Etale W.X.hom)
    (hq : Surjective q.hom.hom.left)
    (hker : ∀ (U : Over S) (y : U ⟶ N.X),
      y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (SubgroupFunctor.range t).carrier U) :
    IsFinite W.X.hom := by
  let : QuasiCompact W.X.hom := hqc
  let : IsSeparated W.X.hom := hsep
  let : Etale W.X.hom := het
  have hkerC : ∀ (U : Over S) (y : U ⟶ N.X),
      y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (torusCentralizer t).carrier U := by
    simpa only [hself.2] using hker
  apply Langlands.AlgebraicGeometry.isFinite_etale_of_algClosed_valuation_pullbacks W.X.hom
  intro K _ _ A b
  let Gb := (baseChange b).obj G
  let Tb := (CommGroupScheme.baseChange b).obj T
  let tb : Tb.toGrp ⟶ Gb := (baseChange b).map t
  let Nb := (baseChange b).obj N
  let nb : Nb ⟶ Gb := (baseChange b).map n
  let Wb := (baseChange b).obj W
  let qb : Nb ⟶ Wb := (baseChange b).map q
  let : Smooth Gb.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  let : IsSeparated Gb.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom b))
  let : QuasiCompact Gb.X.hom := inferInstanceAs (QuasiCompact (pullback.snd G.X.hom b))
  have hGb : HasConnectedReductiveResidueFibers Gb :=
    connectedReductive_residueFibers_baseChange G hG b
  have hTb : RelativeTorus.IsTorus Tb.toGrp := hT.baseChange b
  have htb : IsClosedSubgroup tb := ht.baseChange b
  have hmaxb : IsFibrewiseMaximalTorus tb := isFibrewiseMaximalTorus_baseChange hG hmax b
  have hselfb : (torusCentralizer tb).IsRepresentedBy tb := by
    rw [torusCentralizer_baseChange]
    exact hself.baseChange b
  let : IsAffineHom Gb.X.hom :=
    isAffineHom_over_algClosed_valuation hcrit hval K A Gb hGb Tb tb hTb htb hmaxb hselfb
  have hredb : IsReductive Gb :=
    isReductive_of_isAffineHom_of_connectedReductive_residueFibers Gb hGb
  change IsFinite Wb.X.hom
  exact weylQuotientFinitenessReduction
    Langlands.AlgebraicGeometry.etaleLocalCardinalityFiniteness
    _ Gb hredb Tb tb hTb htb hmaxb Nb nb Wb qb
    (hnclosed.baseChange b) (torusNormalizer_isRepresentedBy_baseChange b t hn)
    (inferInstanceAs (QuasiCompact (pullback.snd W.X.hom b)))
    (inferInstanceAs (IsSeparated (pullback.snd W.X.hom b)))
    (inferInstanceAs (Etale (pullback.snd W.X.hom b)))
    (MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom hq)
    (torusCentralizerKernel_baseChange b t q hkerC)

/-- Construct actual finite Weyl data over every base using the supplied
structural criterion and supplied valuation-subring etale affineness. -/
def valuationFiniteWeylModel
    (hcrit : SelfCentralizingTorusWeylAffinenessStatement.{u})
    (hval : ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
      (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A)),
        QuasiCompact f → IsSeparated f → Etale f → IsAffineHom f)
    (S : Scheme.{u}) (G : GroupScheme S)
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasConnectedReductiveResidueFibers G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hself : (torusCentralizer t).IsRepresentedBy t) : FiniteWeylModel t := by
  apply Classical.choice
  obtain ⟨N, n, W, q, hnclosed, hn, hN, hsep, hqc, het,
    hflat, hsurj, hfp, hker, haff⟩ :=
    hcrit S G inferInstance inferInstance inferInstance
      (fun s => ⟨(hG s).connectedSpace, (hG s).isAffineHom⟩)
      T t hT ht hmax hself
  have hfinite : IsFinite W.X.hom :=
    isFinite_suppliedWeyl_of_valuation_affineness hcrit hval S G hG T t hT ht hmax hself
      N n W q hnclosed hn hqc hsep het hsurj hker
  let : IsFinite W.X.hom := hfinite
  refine ⟨?_⟩
  exact
    { normalizer := N
      inclusion := n
      quotient := W
      projection := q
      closed := hnclosed
      represents := hn
      normalizer_smooth := hN
      quotient_finite := hfinite
      quotient_etale := het
      projection_flat := hflat
      projection_surjective := hsurj
      projection_lfp := hfp
      kernel := hker
      group_affine := haff.mpr inferInstance }

end Langlands.GroupScheme.SelfCentralizingWeyl
