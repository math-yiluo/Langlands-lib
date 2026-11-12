import Langlands.GroupScheme.SimplyConnected.RankOneLeviFactors
import Langlands.GroupScheme.Rational.SimpleRootSubgroupGenerationStatement
import Langlands.GroupScheme.Rational.IsotropicRootSubgroupGenerationStatement
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleRationalGenerationProof
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedProof
import Langlands.GroupScheme.FieldFixedSubgroupRepresentabilityProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.RootFactorPairConsequences
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction
import Langlands.GroupScheme.Rational.CocharacterCentralizer

/-!
# Derived generation by rank-one Levi factors from a factor dichotomy

This module states the dichotomy `RankOneLeviFactorDichotomyStatement` and proves
`RankOneLeviDerivedGenerationStatement` from it and the two root-subgroup generation
statements.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section OppositeRoot

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom] {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A rank-one Levi factor for a relative root `α` also contains the root subgroup of `-α`:
conjugation by a rational reflection representative, which centralizes the kernel of `α`,
normalizes the factor and carries the root subgroup of `α` onto that of `-α`. -/
theorem IsRankOneLeviFactor.subgroup_neg_le_range {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
    (hT : IsSplitTorus S.toGrp) (hfac : RelativeRoot.HasRankOneFactorization i)
    {α : characterLattice S} (hα : α ∈ relativeRoots i)
    {A : GroupScheme (Spec (CommRingCat.of k))} {a : A ⟶ G} (ha : IsRankOneLeviFactor i α a) :
    RelativeRoot.subgroup i (-α) ≤ SubgroupFunctor.range a := by
  obtain ⟨-, -, -, -, hroot, -, hnorm⟩ := ha
  obtain ⟨x, hx, hx1⟩ := RelativeRoot.exists_rootPoint_actual hT i hα
  obtain ⟨⟨p, hp, -⟩, -⟩ := hfac α hα x hx hx1
  let n : normalizerPoints i := ⟨p.1 * x * p.2, hp.2.2⟩
  have hneg : weylAction i n α = -α := hp.weylAction_eq_neg i hT hα.1 hx hx1
  have hker : n.val ∈ (RelativeRoot.kernelCentralizer i α).carrier (Over.mk (𝟙 _)) :=
    hp.mem_kernelCentralizer i hx
  have hinv : weylAction i n⁻¹ (-α) = α := by
    rw [map_inv, ← hneg]
    exact (weylAction i n).symm_apply_apply α
  intro T g hg
  have hy := RelativeRoot.normalizer_conj_mem i (-α) n⁻¹ hg
  rw [hinv] at hy
  have hya := hroot T hy
  have hcent : ∀ ζ : cocharacterLattice S, latticePairing S α ζ = 0 →
      G.constantPoint n.val T ∈
        (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier T := by
    intro ζ hζ
    have hk : G.constantPoint n.val T ∈ (RelativeRoot.kernelCentralizer i α).carrier T := by
      unfold GroupScheme.constantPoint
      exact (RelativeRoot.kernelCentralizer i α).comp_mem _ hker
    exact RelativeRoot.kernelCentralizer_le_dynamicCentralizer_of_pairing_eq_zero i α ζ hζ T hk
  have h7 := hnorm T (G.constantPoint n.val T)
    (G.constantPoint (n⁻¹).val T * g * (G.constantPoint (n⁻¹).val T)⁻¹) hcent hya
  have hc : G.constantPoint (n⁻¹).val T = (G.constantPoint n.val T)⁻¹ := by
    rw [Subgroup.coe_inv, G.constantPoint_inv]
  rw [hc] at h7
  simpa [mul_assoc] using h7

end OppositeRoot

/-- The factor dichotomy for rank-one Levi factors. For a simply connected group `G`, a maximal
split torus `i`, a generic cocharacter `ν`, a representative `j : M ⟶ G` of the centralizer of
`ν`, a simple relative root `α` with a rank-one Levi factor `a : A ⟶ G`, a derived subgroup
`d : D ⟶ M` and a closed normal almost-simple subgroup `b : B ⟶ D`, either the image of `B` in
`G` lies in the image of `a`, or every point of `B` commutes with every point of `A` in `G`. -/
def RankOneLeviFactorDichotomyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom], IsSimplyConnected G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j →
    ∀ α ∈ simpleRelativeRoots i ν,
    ∀ (A : GroupScheme (Spec (CommRingCat.of k))) (a : A ⟶ G), IsRankOneLeviFactor i α a →
    ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ M), IsDerivedSubgroup d →
    ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ D),
      IsAlmostSimple B → IsClosedSubgroup b → (SubgroupFunctor.range b).IsNormal →
      SubgroupFunctor.range (b ≫ d ≫ j) ≤ SubgroupFunctor.range a ∨
        ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ B.X) (y : T ⟶ A.X),
          Commute (x ≫ (b ≫ d ≫ j).hom.hom) (y ≫ a.hom.hom)

section Reduction

/-- Membership in the fixed subgroup of a conjugation action is commutation with every point of
the acting group after every refinement. -/
theorem AutomorphicAction.conjugation_isFixed_iff {S : Scheme.{u}} {H G : GroupScheme S}
    (e : H ⟶ G) {T : Over S} (g : T ⟶ G.X) :
    (AutomorphicAction.conjugation e).IsFixed g ↔
      ∀ (T' : Over S) (c : T' ⟶ T) (h : T' ⟶ H.X), Commute (h ≫ e.hom.hom) (c ≫ g) := by
  refine forall_congr' fun T' => forall_congr' fun c => forall_congr' fun h => ?_
  rw [AutomorphicAction.conjugation_act, mul_inv_eq_iff_eq_mul]
  exact Iff.rfl

/-- Under the dichotomy and the two root-subgroup generation statements, every closed normal
almost-simple subgroup of the derived subgroup of the centralizer lies in some rank-one Levi
factor. -/
theorem exists_range_le_rankOneLeviFactor
    (hdich : RankOneLeviFactorDichotomyStatement.{u})
    (hsimple : SimpleRootSubgroupGenerationStatement.{u})
    (hiso : IsotropicRootSubgroupGenerationStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hsc : IsSimplyConnected G) (hG : IsAlmostSimple G) (hani : ¬ IsAnisotropic G)
    {S : CommGroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {M : GroupScheme (Spec (CommRingCat.of k))} {j : M ⟶ G}
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    {A : simpleRelativeRoots i ν → GroupScheme (Spec (CommRingCat.of k))}
    {a : ∀ α, A α ⟶ G} (ha : ∀ α, IsRankOneLeviFactor i α.1 (a α))
    {D : GroupScheme (Spec (CommRingCat.of k))} {d : D ⟶ M} (hd : IsDerivedSubgroup d)
    {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ D} (hB : IsAlmostSimple B)
    (hbc : IsClosedSubgroup b) (hbn : (SubgroupFunctor.range b).IsNormal) :
    ∃ α : simpleRelativeRoots i ν,
      SubgroupFunctor.range (b ≫ d ≫ j) ≤ SubgroupFunctor.range (a α) := by
  by_contra hno
  push Not at hno
  have hcomm : ∀ α : simpleRelativeRoots i ν, ∀ (T : Over (Spec (CommRingCat.of k)))
      (x : T ⟶ B.X) (y : T ⟶ (A α).X),
      Commute (x ≫ (b ≫ d ≫ j).hom.hom) (y ≫ (a α).hom.hom) := fun α =>
    (hdich k G hsc S i hi ν hν M j hj α.1 α.2 (A α) (a α) (ha α) D d hd B b hB hbc
      hbn).resolve_left (hno α)
  have hGred := hsc.isSemisimple.isConnectedReductive
  have : Smooth G.X.hom := hGred.smooth
  have : ConnectedSpace G.X.left := hGred.connectedSpace
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hT : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  have hBaff : IsAffineHom B.X.hom := hB.isSemisimple.isConnectedReductive.isAffineHom
  let e : B ⟶ G := b ≫ d ≫ j
  let F := (AutomorphicAction.conjugation e).fixedSubgroup
  obtain ⟨C, c, hcrep, hcc⟩ :=
    fieldFixedSubgroupRepresentability k B G hBaff (AutomorphicAction.conjugation e)
  have hfac : RelativeRoot.HasRankOneFactorization i :=
    rootRankOneFactorization k G hGred S i hi
  -- every rank-one Levi factor centralizes `B`
  have haF : ∀ α, SubgroupFunctor.range (a α) ≤ F := by
    intro α T g hg
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hg
    change (AutomorphicAction.conjugation e).IsFixed (y ≫ (a α).hom.hom)
    rw [AutomorphicAction.conjugation_isFixed_iff]
    intro T' c h
    simpa only [Category.assoc] using hcomm α T' h (c ≫ y)
  -- the torus centralizes `B`
  have hMT : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i :=
    IsSplitTorus.dynamicCentralizer_eq_torusCentralizer hT i ν hν
  have hiF : SubgroupFunctor.range i ≤ F := by
    intro T g hg
    obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.1 hg
    change (AutomorphicAction.conjugation e).IsFixed (s ≫ i.hom.hom)
    rw [AutomorphicAction.conjugation_isFixed_iff]
    intro T' c h
    have hmem : h ≫ e.hom.hom ∈ (torusCentralizer i).carrier T' := by
      rw [← hMT, ← hj.2]
      exact SubgroupFunctor.mem_range.2 ⟨h ≫ (b ≫ d).hom.hom, by
        simp only [e, Grp.comp_hom_hom, Category.assoc]⟩
    have := hmem T' (𝟙 T') (c ≫ s)
    simpa only [Category.id_comp, Category.assoc] using this
  -- all root subgroups centralize `B`
  have hrootF : ∀ r ∈ relativeRoots i, RelativeRoot.subgroup i r ≤ F := by
    refine hsimple k G hGred S i hi ν hν F ?_
    intro α hα
    obtain ⟨-, -, -, -, hroot, -, -⟩ := ha ⟨α, hα⟩
    exact ⟨hroot.trans (haF ⟨α, hα⟩),
      (IsRankOneLeviFactor.subgroup_neg_le_range hT hfac hα.1.1 (ha ⟨α, hα⟩)).trans
        (haF ⟨α, hα⟩)⟩
  have htop : SubgroupFunctor.range c = ⊤ :=
    hiso k G hG hani S i hi C c hcc (hcrep.2 ▸ hiF)
      (fun r hr => hcrep.2 ▸ hrootF r hr)
  -- hence `B` is commutative
  apply hB.noncommutative
  intro T x y
  have hx : x ≫ e.hom.hom ∈ F.carrier T := by
    change x ≫ e.hom.hom ∈ (AutomorphicAction.conjugation e).fixedSubgroup.carrier T
    rw [← hcrep.2, htop]
    trivial
  have hxy := ((AutomorphicAction.conjugation_isFixed_iff e _).1 hx) T (𝟙 T) y
  rw [Category.id_comp] at hxy
  have : Mono b.hom.hom := hbc.mono_hom
  have : Mono d.hom.hom := hd.1.mono_hom
  have : Mono j.hom.hom := hj.1
  have : Mono e.hom.hom := by
    simp only [e, Grp.comp_hom_hom]
    infer_instance
  apply (cancel_mono e.hom.hom).1
  rw [MonObj.mul_comp, MonObj.mul_comp]
  exact hxy.symm.eq

/-- `RankOneLeviDerivedGenerationStatement` follows from the factor dichotomy and the two
root-subgroup generation statements. -/
theorem rankOneLeviDerivedGeneration_of_dichotomy
    (hdich : RankOneLeviFactorDichotomyStatement.{u})
    (hsimple : SimpleRootSubgroupGenerationStatement.{u})
    (hiso : IsotropicRootSubgroupGenerationStatement.{u}) :
    RankOneLeviDerivedGenerationStatement.{u} := by
  intro k _ G _ hsc hG hani S i hi ν hν M j hj A a ha D d hd
  have hGred := hsc.isSemisimple.isConnectedReductive
  have : Smooth G.X.hom := hGred.smooth
  have : ConnectedSpace G.X.left := hGred.connectedSpace
  have hT : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  have hjT : (torusCentralizer i).IsRepresentedBy j := by
    rw [← IsSplitTorus.dynamicCentralizer_eq_torusCentralizer hT i ν hν]
    exact hj
  have hDsc : IsSimplyConnected D :=
    splitTorusCentralizerDerivedSimplyConnected k G hsc S i hi.isSplitSubtorus M j hjT D d hd
  let K : Subgroup (rationalPoints M) :=
    Subgroup.closure (⋃ α, ((rationalPoints.map (subgroupIntersectionFst j (a α))).range :
      Set (rationalPoints M)))
  have hH := simplyConnectedAlmostSimpleRationalGeneration k D hDsc
    (K.comap (rationalPoints.map d)) ?_
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ K.comap (rationalPoints.map d) := by
      rw [hH]
      trivial
    exact hx
  · intro B b hB hbc hbn
    obtain ⟨α, hα⟩ := exists_range_le_rankOneLeviFactor hdich hsimple hiso hsc hG hani hi hν
      hj ha hd hB hbc hbn
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_comap]
    apply Subgroup.subset_closure
    refine Set.mem_iUnion.2 ⟨α, ?_⟩
    have hmem : y ≫ (b ≫ d ≫ j).hom.hom ∈
        (SubgroupFunctor.range (a α)).carrier (Over.mk (𝟙 _)) :=
      hα _ (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩)
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.1 hmem
    have hpb := subgroupIntersection_isPullback j (a α)
    refine ⟨hpb.lift (y ≫ (b ≫ d).hom.hom) w ?_, ?_⟩
    · rw [hw]
      simp only [Grp.comp_hom_hom, Category.assoc]
    · rw [rationalPoints.map_apply, hpb.lift_fst, rationalPoints.map_apply,
        rationalPoints.map_apply]
      simp only [Grp.comp_hom_hom, Category.assoc]

end Reduction

end Langlands.GroupScheme
