import Langlands.GroupScheme.Reductive.RankOneFlagCell
import Langlands.GroupScheme.Reductive.RankOneLocalAssembly
import Langlands.GroupScheme.Absolute.TorusFixedCosetBound
import Langlands.GroupScheme.Absolute.SolvableTorusNormalizer
import Langlands.GroupScheme.Rational.RankOneWeylQuotient
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # The ordinary flag variety in semisimple rank one

For a connected reductive group of semisimple rank one over an algebraically closed
field, an ordinary proper Borel subgroup containing the maximal torus has a proper quotient
`X = G/B`. Its base point `x₀` and the translate `x₁ = n · x₀` by a nonidentity Weyl point are
distinct, both are fixed by the torus, and they are the only torus-fixed rational points. See the
paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RankOneFlag

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The rational base point `Spec k` over `Spec k`. -/
abbrev pt (k : Type u) [Field k] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (𝟙 (Spec (CommRingCat.of k)))

/-- **Flag data.** An ordinary proper Borel subgroup containing the torus, torus conjugacy in
it, a proper quotient with exact coset fibres, and a nonidentity Weyl point. -/
structure FlagData (i : T.toGrp ⟶ G) where
  B : GroupScheme (Spec (CommRingCat.of k))
  b : B ⟶ G
  t : T.toGrp ⟶ B
  ht : t ≫ b = i
  borel : IsBorelSubgroup b
  conj : MaximalToriAreConjugate B
  quot : IsBorelSubgroup.ProperQuotientData b
  n : normalizerPoints i
  hn : (QuotientGroup.mk n : relativeWeylGroup i) ≠ 1

/-- Flag data exist in semisimple rank one as soon as there is a root. -/
theorem nonempty_flagData [IsAlgClosed k] (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    {α : characterLattice T} (hα : haveI := hG.isAffineHom; α ∈ roots i) :
    Nonempty (FlagData i) := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨B, b, t, hpair, -, ht⟩ :=
    exists_proper_isBorelPair_of_relativeRoot hG.isPseudoReductive i hT hi hα
  have : Smooth B.X.hom := hpair.1.smooth
  have : IsAffineHom B.X.hom := hpair.1.isClosedSubgroup.isAffineHom_source
  have : ConnectedSpace B.X.left := hpair.1.connectedSpace
  have hconj : MaximalToriAreConjugate B :=
    solvableMaximalTorusConjugacy k B hpair.1.isSolvableGroupScheme
  let D := hpair.1.properQuotientData_of_solvableProperFixedPoint solvableProperFixedPoint
  have : IsProper D.quotient.hom := D.proper
  have : Smooth D.projection.left := D.smooth
  have : Surjective D.projection.left := D.surjective
  have : QuasiCompact D.projection.left := D.quasiCompact
  let n := nonidentityNormalizerOfRootedSolvableQuotient
    hG.isPseudoReductive i hi hT hα b hpair.1.isClosedSubgroup
    hpair.1.isSolvableGroupScheme t ht hconj D.projection D.fibers
  exact ⟨⟨B, b, t, ht, hpair.1, hconj, D, n.val, n.property⟩⟩

namespace FlagData

variable {i : T.toGrp ⟶ G} (F : FlagData i)

/-- The flag variety `G/B`. -/
abbrev X : Over (Spec (CommRingCat.of k)) := F.quot.quotient

/-- The quotient map `G → G/B`. -/
abbrev q : G.X ⟶ F.X := F.quot.projection

instance : IsProper F.X.hom := F.quot.proper
instance : Smooth F.q.left := F.quot.smooth
instance : Surjective F.q.left := F.quot.surjective
instance : QuasiCompact F.q.left := F.quot.quasiCompact

theorem fibers {W : Over (Spec (CommRingCat.of k))} (g h : W ⟶ G.X) :
    g ≫ F.q = h ≫ F.q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range F.b).carrier W :=
  F.quot.fibers W g h

/-- The left translation action of `G` on `G/B`. -/
@[instance_reducible] def act : SchemeAction G F.X :=
  Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range F.b) F.q F.quot.fibers

theorem act_lift {W : Over (Spec (CommRingCat.of k))} (g h : W ⟶ G.X) :
    F.act.act g (h ≫ F.q) = (g * h) ≫ F.q :=
  Dynamic.flagQuotientSchemeAction_act_lift G _ F.q F.quot.fibers g h

/-- The base point `x₀ = B`. -/
def x₀ : pt k ⟶ F.X := (1 : pt k ⟶ G.X) ≫ F.q

/-- The Weyl translate `x₁ = n B`. -/
def x₁ : pt k ⟶ F.X := (F.n : pt k ⟶ G.X) ≫ F.q

/-- Right multiplication by a rational point. -/
def rmul (g : pt k ⟶ G.X) : G.X ⟶ G.X :=
  𝟙 G.X * (toUnit G.X ≫ g)

theorem rmul_rmul (g h : pt k ⟶ G.X) : rmul g ≫ rmul h = rmul (g * h) := by
  simp only [rmul, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, mul_assoc]

theorem rmul_one : rmul (1 : pt k ⟶ G.X) = 𝟙 G.X := by
  rw [rmul, MonObj.comp_one, mul_one]

instance (g : pt k ⟶ G.X) : IsIso (rmul g) :=
  ⟨rmul g⁻¹, by rw [rmul_rmul, mul_inv_cancel, rmul_one],
    by rw [rmul_rmul, inv_mul_cancel, rmul_one]⟩

/-- The orbit map of a translate of the base point is right multiplication followed by the
quotient map. -/
theorem orbitMap_eq (g : pt k ⟶ G.X) : F.act.orbitMap (g ≫ F.q) = rmul g ≫ F.q := by
  rw [SchemeAction.orbitMap, ← Category.assoc, F.act_lift, rmul]

instance (g : pt k ⟶ G.X) : IsIso (rmul g).left :=
  (Over.forget _).map_isIso (rmul g)

instance (g : pt k ⟶ G.X) : Smooth (F.act.orbitMap (g ≫ F.q)).left := by
  rw [orbitMap_eq, Over.comp_left]; infer_instance

instance (g : pt k ⟶ G.X) : Flat (F.act.orbitMap (g ≫ F.q)).left := inferInstance

instance (g : pt k ⟶ G.X) : LocallyOfFinitePresentation (F.act.orbitMap (g ≫ F.q)).left :=
  inferInstance

instance (g : pt k ⟶ G.X) : QuasiCompact (F.act.orbitMap (g ≫ F.q)).left := by
  rw [orbitMap_eq, Over.comp_left]; infer_instance

theorem toUnit_comp (W : Over (Spec (CommRingCat.of k))) (g : pt k ⟶ G.X) :
    toUnit W ≫ g = G.constantPoint g W := by
  rw [GroupScheme.constantPoint]
  congr 1

/-- **Fixed translates.** A translate `g · x₀` is fixed by a subgroup `j` exactly when
`g⁻¹ j g` lies in `B` on every test. -/
theorem isFixed_iff {J : GroupScheme (Spec (CommRingCat.of k))} (j : J ⟶ G) (g : pt k ⟶ G.X) :
    (F.act.restrict j).IsFixed (g ≫ F.q) ↔
      ∀ (W : Over (Spec (CommRingCat.of k))) (s : W ⟶ J.X),
        (toUnit W ≫ g)⁻¹ * ((s ≫ j.hom.hom) * (toUnit W ≫ g)) ∈
          (SubgroupFunctor.range F.b).carrier W := by
  constructor
  · intro h W s
    have e := h W (toUnit W) s
    rw [SchemeAction.restrict_act, ← Category.assoc, F.act_lift] at e
    exact (F.fibers _ _).mp e.symm
  · intro h W c s
    rw [SchemeAction.restrict_act, ← Category.assoc, F.act_lift, toUnit_unique c (toUnit W)]
    exact ((F.fibers _ _).mpr (h W s)).symm

theorem mem_range_i {W : Over (Spec (CommRingCat.of k))} (s : W ⟶ T.toGrp.X) :
    s ≫ i.hom.hom ∈ (SubgroupFunctor.range F.b).carrier W :=
  SubgroupFunctor.mem_range.mpr ⟨s ≫ F.t.hom.hom, by
    rw [Category.assoc, ← Grp.comp_hom_hom, F.ht]⟩

/-- The torus fixes the base point. -/
theorem isFixed_x₀ : (F.act.restrict i).IsFixed F.x₀ := by
  rw [x₀, isFixed_iff]
  intro W s
  rw [MonObj.comp_one, inv_one, one_mul, mul_one]
  exact F.mem_range_i s

/-- Conjugating the torus by a rational normalizer point stays in the torus. -/
theorem conj_mem_range_of_mem_normalizerPoints {m : pt k ⟶ G.X} (hm : m ∈ normalizerPoints i)
    {W : Over (Spec (CommRingCat.of k))} (s : W ⟶ T.toGrp.X) :
    ∃ s' : W ⟶ T.toGrp.X, s' ≫ i.hom.hom =
      (toUnit W ≫ m)⁻¹ * (s ≫ i.hom.hom) * (toUnit W ≫ m) := by
  obtain ⟨σ, hσ⟩ := inv_mem hm
  refine ⟨s ≫ (CommGroupScheme.groupHom σ.hom).hom.hom, ?_⟩
  have h := congrArg (fun f => s ≫ f.hom.hom) hσ
  simp only [Grp.comp_hom_hom] at h
  rw [Category.assoc, ← h, ← Category.assoc, comp_innerIso_hom, toUnit_comp, constantPoint_inv,
    inv_inv]

/-- The torus fixes the Weyl translate. -/
theorem isFixed_x₁ : (F.act.restrict i).IsFixed F.x₁ := by
  rw [x₁, isFixed_iff]
  intro W s
  obtain ⟨s', hs'⟩ := conj_mem_range_of_mem_normalizerPoints F.n.property s
  rw [← mul_assoc, ← hs']
  exact F.mem_range_i s'

/-- **The Weyl translate is not the base point.** Otherwise a nonidentity Weyl point would lie
in the solvable group `B`, where normalizing points of a torus centralize it. -/
theorem x₀_ne_x₁ [IsAlgClosed k] [IsAffineHom G.X.hom] (hi : IsMaximalTorus i) :
    F.x₀ ≠ F.x₁ := by
  intro h
  have hmem := (F.fibers _ _).mp h
  rw [inv_one, one_mul] at hmem
  obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp hmem
  have : Smooth F.B.X.hom := F.borel.smooth
  have : IsAffineHom F.B.X.hom := F.borel.isClosedSubgroup.isAffineHom_source
  have : ConnectedSpace F.B.X.left := F.borel.connectedSpace
  have : IsClosedImmersion F.b.hom.hom.left := F.borel.isClosedSubgroup
  have : Mono F.b.hom.hom := Over.mono_of_mono_left _
  have : Mono F.b := (Grp.forget _).mono_of_mono_map (inferInstance : Mono F.b.hom.hom)
  have htc : IsClosedSubgroup F.t := by
    have : IsClosedImmersion (F.t.hom.hom.left ≫ F.b.hom.hom.left) := by
      rw [← Over.comp_left, ← Grp.comp_hom_hom, F.ht]
      exact hi.2.1
    exact IsClosedImmersion.of_comp _ F.b.hom.hom.left
  obtain ⟨σ, hσ⟩ := F.n.property
  have hnorm : m ∈ normalizerPoints F.t := by
    refine ⟨σ, ?_⟩
    apply (cancel_mono F.b).mp
    change F.t ≫ (F.B.innerIso m).hom ≫ F.b = CommGroupScheme.groupHom σ.hom ≫ F.t ≫ F.b
    rw [innerIso_hom_comp F.b m, ← Category.assoc, F.ht, hm]
    exact hσ
  have hcent := hi.1.mem_centralizerPoints_of_mem_normalizerPoints_of_isSolvable
    F.borel.isSolvableGroupScheme htc m hnorm
  have hn : (F.n : pt k ⟶ G.X) ∈ centralizerPoints i := by
    have h2 : F.t ≫ F.b ≫ (G.innerIso (m ≫ F.b.hom.hom)).hom = F.t ≫ F.b := by
      rw [← innerIso_hom_comp, ← Category.assoc, (mem_centralizerPoints F.t).mp hcent]
    rw [hm, ← Category.assoc, F.ht] at h2
    exact (mem_centralizerPoints i).mpr h2
  exact F.hn ((QuotientGroup.eq_one_iff _).mpr hn)

/-- **Torus-fixed points.** In semisimple rank one the only torus-fixed rational points of
`G/B` are `x₀` and `x₁`. -/
theorem eq_or_eq_of_isFixed [IsAlgClosed k] (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    {w : pt k ⟶ F.X} (hw : (F.act.restrict i).IsFixed w) : w = F.x₀ ∨ w = F.x₁ := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have hc : centralizerPoints i ≤
      (SubgroupFunctor.range F.b).carrier (pt k) := by
    intro n hn
    have h1 := centralizerPoints_le_torusCentralizer i hn
    rw [algClosedMaximalTorusCentralizer k G hG T i hi] at h1
    obtain ⟨s, hs⟩ := SubgroupFunctor.mem_range.mp h1
    rw [← hs]
    exact F.mem_range_i s
  have hact : ∀ (V : Over (Spec (CommRingCat.of k))) (s : V ⟶ T.toGrp.X) (g : V ⟶ G.X),
      (F.act.restrict i).act s (g ≫ F.q) = ((s ≫ i.hom.hom) * g) ≫ F.q := by
    intro V s g
    rw [SchemeAction.restrict_act, F.act_lift]
  have hsurj : Function.Surjective (fun g : pt k ⟶ G.X => g ≫ F.q) := by
    have : LocallyOfFiniteType (F.q.left ≫ F.X.hom) := by
      rw [Over.w F.q]
      infer_instance
    have : LocallyOfFiniteType F.q.left := locallyOfFiniteType_of_comp F.q.left F.X.hom
    intro x
    obtain ⟨g, hg⟩ := exists_rationalPoint_lift_of_mem_range F.q.left x.left
      (F.q.left.surjective (x.left (IsLocalRing.closedPoint k)))
    have hgS : g ≫ G.X.hom = 𝟙 (Spec (CommRingCat.of k)) := by
      rw [← Over.w F.q, ← Category.assoc, hg]
      exact Over.w x
    exact ⟨Over.homMk g hgS, Over.OverMorphism.ext hg⟩
  obtain ⟨w', hw'⟩ := exists_relativeWeylCosetMap_eq_of_isFixed i F.b F.q F.quot.fibers hi
    F.borel.isClosedSubgroup F.t F.ht F.conj hc (F.act.restrict i) hact hsurj w hw
  let e := hG.rankOneRelativeWeylQuotientSignEmbedding_of_isMaximalTorus i hi hT hdep
  have key : ∀ a b c : Bool, a ≠ b → a ≠ c → b = c := by decide
  by_cases h1 : w' = 1
  · left
    rw [← hw', h1, ← QuotientGroup.mk_one, relativeWeylCosetMap_mk]
    rfl
  · right
    have h2 : w' = QuotientGroup.mk F.n := e.injective
      (key (e 1) (e w') (e (QuotientGroup.mk F.n)) (fun h => h1 (e.injective h).symm)
        (fun h => F.hn (e.injective h).symm))
    rw [← hw', h2, relativeWeylCosetMap_mk]
    rfl

end FlagData

end RankOneFlag

end Langlands.GroupScheme
