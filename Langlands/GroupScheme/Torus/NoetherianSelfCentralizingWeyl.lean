import Langlands.AlgebraicGeometry.FiniteBaseQuasiFiniteAffineness
import Langlands.AlgebraicGeometry.NoetherianValuativeCriterion
import Langlands.GroupScheme.Reductive.ResidueFiberGeometry
import Langlands.GroupScheme.Torus.SelfCentralizingWeylAffinenessStatement
import Langlands.GroupScheme.Torus.WeylGroupSchemeBaseChange
import Langlands.GroupScheme.Torus.WeylQuotientFinitenessReduction
import Langlands.AlgebraicGeometry.EtaleLocalCardinalityFinitenessProof

/-! # Finite Weyl models over Noetherian bases from a supplied affineness criterion -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Langlands.AlgebraicGeometry

/-- Over a Noetherian affine base, a separated quasi-finite morphism is finite
when all of its discrete-valuation-ring pullbacks are finite. -/
theorem isFinite_of_noetherian_dvr_pullbacks
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [IsSeparated f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (H : ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      (b : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of R)),
        IsFinite (pullback.snd f b)) : IsFinite f := by
  let : UniversallyClosed f :=
    universallyClosed_of_forall_isDiscreteValuationRing_hasLift f (by
      intro S hS
      let : IsDiscreteValuationRing S.R := hS
      let p := pullback.snd f S.i₂
      let : IsFinite p := H S.R S.i₂
      have hp : ValuativeCriterion.Existence p := by
        have h : UniversallyClosed p := inferInstance
        rw [UniversallyClosed.eq_valuativeCriterion] at h
        exact h.1
      let S' : ValuativeCommSq p :=
        { R := S.R
          K := S.K
          i₁ := pullback.lift S.i₁
            (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) S.commSq.w
          i₂ := 𝟙 _
          commSq := ⟨by simp [p]⟩ }
      obtain ⟨l, hl₁, hl₂⟩ := (hp S').exists_lift
      refine ⟨⟨⟨l ≫ pullback.fst f S.i₂, ?_, ?_⟩⟩⟩
      · rw [← Category.assoc, hl₁]
        exact pullback.lift_fst _ _ _
      · rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (l ≫ p) ≫ S.i₂ = S.i₂
        rw [hl₂, Category.id_comp])
  let : IsProper f := (isProper_iff f).mpr ⟨inferInstance, inferInstance, inferInstance⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme.SelfCentralizingWeyl

/-- Residue-fibre maximality extends to a supplied field point using affineness
of that residue fibre alone. -/
theorem isMaximalTorus_fieldPoint_of_connectedReductive_residueFibers
    {S : Scheme.{u}} {G : GroupScheme S} {T : CommGroupScheme S}
    {t : T.toGrp ⟶ G} (hG : HasConnectedReductiveResidueFibers G)
    (hmax : IsFibrewiseMaximalTorus t)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map t) := by
  let : Algebra (S.residueField (b (IsLocalRing.closedPoint k))) k :=
    (fieldPointResidueMap b).hom.toAlgebra
  let a := S.fromSpecResidueField (b (IsLocalRing.closedPoint k))
  let c := Spec.map (fieldPointResidueMap b)
  have ha := hG (b (IsLocalRing.closedPoint k))
  let : Smooth ((baseChange a).obj G).X.hom := ha.smooth
  let : IsAffineHom ((baseChange a).obj G).X.hom := ha.isAffineHom
  have hm := (maximalTorusBaseChange (S.residueField (b (IsLocalRing.closedPoint k))) k
    ((baseChange a).obj G) ((CommGroupScheme.baseChange a).obj T)
    ((baseChange a).map t) (hmax _).1 (hmax _).2.1).mp (hmax _)
  have hc := isMaximalTorus_of_baseChange_comp a c T t hm
  dsimp only [a, c] at hc
  rwa [fieldPointResidueMap_factorization] at hc

/-- Fibrewise maximality commutes with arbitrary base change when the ambient
residue fibres are connected reductive; global affineness is unnecessary. -/
theorem isFibrewiseMaximalTorus_baseChange
    {S S' : Scheme.{u}} {G : GroupScheme S} {T : CommGroupScheme S}
    {t : T.toGrp ⟶ G} (hG : HasConnectedReductiveResidueFibers G)
    (hmax : IsFibrewiseMaximalTorus t) (b : S' ⟶ S) :
    IsFibrewiseMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map t) := by
  intro s
  exact isMaximalTorus_baseChange_comp b (S'.fromSpecResidueField s) T t
    (isMaximalTorus_fieldPoint_of_connectedReductive_residueFibers hG hmax
      (S'.fromSpecResidueField s ≫ b))

/-- The supplied Weyl-affineness criterion gives affineness over every DVR. -/
theorem isAffineHom_over_dvr
    (hcrit : SelfCentralizingTorusWeylAffinenessStatement.{u})
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G : GroupScheme (Spec (CommRingCat.of R)))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasConnectedReductiveResidueFibers G)
    (T : CommGroupScheme (Spec (CommRingCat.of R))) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hself : (torusCentralizer t).IsRepresentedBy t) : IsAffineHom G.X.hom := by
  obtain ⟨N, n, W, q, hnclosed, hn, hN, hsep, hqc, het,
    hflat, hsurj, hfp, hker, haff⟩ :=
    hcrit _ G inferInstance inferInstance inferInstance
      (fun s => ⟨(hG s).connectedSpace, (hG s).isAffineHom⟩)
      T t hT ht hmax hself
  let : IsSeparated W.X.hom := hsep
  let : QuasiCompact W.X.hom := hqc
  let : Etale W.X.hom := het
  exact haff.mpr (Langlands.AlgebraicGeometry.isAffineHom_etale_over_dvr R W.X.hom)

end Langlands.GroupScheme.SelfCentralizingWeyl

namespace Langlands.GroupScheme.SelfCentralizingWeyl

/-- Over a Noetherian affine base, the criterion forces every supplied actual
Weyl quotient of the self-centralizing maximal torus to be finite. -/
theorem isFinite_suppliedWeyl_over_noetherian
    (hcrit : SelfCentralizingTorusWeylAffinenessStatement.{u})
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (G : GroupScheme (Spec (CommRingCat.of R)))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasConnectedReductiveResidueFibers G)
    (T : CommGroupScheme (Spec (CommRingCat.of R))) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hself : (torusCentralizer t).IsRepresentedBy t)
    (N : GroupScheme (Spec (CommRingCat.of R))) (n : N ⟶ G)
    (W : GroupScheme (Spec (CommRingCat.of R))) (q : N ⟶ W)
    (hnclosed : IsClosedSubgroup n) (hn : (torusNormalizer t).IsRepresentedBy n)
    (hqc : QuasiCompact W.X.hom) (hsep : IsSeparated W.X.hom) (het : Etale W.X.hom)
    (hq : Surjective q.hom.hom.left)
    (hker : ∀ (U : Over (Spec (CommRingCat.of R))) (y : U ⟶ N.X),
      y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (SubgroupFunctor.range t).carrier U) :
    IsFinite W.X.hom := by
  let : QuasiCompact W.X.hom := hqc
  let : IsSeparated W.X.hom := hsep
  let : Etale W.X.hom := het
  let : LocallyQuasiFinite W.X.hom :=
    Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale _
  have hkerC : ∀ (U : Over (Spec (CommRingCat.of R))) (y : U ⟶ N.X),
      y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (torusCentralizer t).carrier U := by
    simpa only [hself.2] using hker
  apply Langlands.AlgebraicGeometry.isFinite_of_noetherian_dvr_pullbacks R W.X.hom
  intro V _ _ _ b
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
    isAffineHom_over_dvr hcrit V Gb hGb Tb tb hTb htb hmaxb hselfb
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

/-- Actual finite etale normalizer-quotient data, including the induced
relative affineness of the original group. -/
structure FiniteWeylModel
    {S : Scheme.{u}} {G : GroupScheme S} {T : CommGroupScheme S} (t : T.toGrp ⟶ G) where
  normalizer : GroupScheme S
  inclusion : normalizer ⟶ G
  quotient : GroupScheme S
  projection : normalizer ⟶ quotient
  closed : IsClosedSubgroup inclusion
  represents : (torusNormalizer t).IsRepresentedBy inclusion
  normalizer_smooth : Smooth normalizer.X.hom
  quotient_finite : IsFinite quotient.X.hom
  quotient_etale : Etale quotient.X.hom
  projection_flat : Flat projection.hom.hom.left
  projection_surjective : Surjective projection.hom.hom.left
  projection_lfp : LocallyOfFinitePresentation projection.hom.hom.left
  kernel : ∀ (U : Over S) (y : U ⟶ normalizer.X),
    y ≫ projection.hom.hom = 1 ↔
      y ≫ inclusion.hom.hom ∈ (SubgroupFunctor.range t).carrier U
  group_affine : IsAffineHom G.X.hom

/-- Construct a finite Weyl model over a Noetherian affine base from the
supplied self-centralizing maximal-torus affineness criterion. -/
def noetherianFiniteWeylModel
    (hcrit : SelfCentralizingTorusWeylAffinenessStatement.{u})
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (G : GroupScheme (Spec (CommRingCat.of R)))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasConnectedReductiveResidueFibers G)
    (T : CommGroupScheme (Spec (CommRingCat.of R))) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hself : (torusCentralizer t).IsRepresentedBy t) : FiniteWeylModel t := by
  apply Classical.choice
  obtain ⟨N, n, W, q, hnclosed, hn, hN, hsep, hqc, het,
    hflat, hsurj, hfp, hker, haff⟩ :=
    hcrit _ G inferInstance inferInstance inferInstance
      (fun s => ⟨(hG s).connectedSpace, (hG s).isAffineHom⟩)
      T t hT ht hmax hself
  have hfinite : IsFinite W.X.hom :=
    isFinite_suppliedWeyl_over_noetherian hcrit R G hG T t hT ht hmax hself
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
