import Langlands.Representation.Intertwining.PQSupportOrbit
import Langlands.Representation.Intertwining.PQSupportGradedStatement
import Langlands.Representation.Geometric.LeviConjugatePiece
import Langlands.GroupScheme.SubgroupFunctor.IntersectionNormalizer
import Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction
import Langlands.GroupScheme.Rational.ParabolicLeviTorusConjugation
import Langlands.Representation.Geometric.ClosedSubgroupOrbitOrdering

/-! # The identity support subquotient for common-Levi parabolics -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Geometric.OrderedDoubleCosets

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {P Q : Subgroup G} {n : ℕ} (s : OrderedDoubleCosets P Q n)

omit [IsTopologicalGroup G] in
/-- Orbit-closure containment reverses every open-prefix orbit enumeration. -/
theorem bruhatLE_index_antitone
    {x y : DoubleCoset.Quotient (P : Set G) Q} (hxy : BruhatLE P Q x y) :
    s.doubleCosetEquiv.symm y ≤ s.doubleCosetEquiv.symm x := by
  classical
  by_contra hle
  let i := s.doubleCosetEquiv.symm x
  let j := s.doubleCosetEquiv.symm y
  have hij : i < j := lt_of_not_ge hle
  let U := s.initialOrbits j.castSucc
  have hopen : IsOpen U := s.initial_open j.castSucc
  have hclosed : IsClosed (Induction.quotientMap P ⁻¹' U)ᶜ :=
    (hopen.preimage continuous_quotient_mk').isClosed_compl
  have hsub : DoubleCoset.quotToDoubleCoset P Q y ⊆
      (Induction.quotientMap P ⁻¹' U)ᶜ := by
    intro g hg hU
    obtain ⟨a, ha, hag⟩ := hU
    have hjg : Induction.quotientMap P g ∈ cosetOrbit P Q (s.representative j) := by
      apply (quotientMap_mem_cosetOrbit_iff P Q _ g).mpr
      exact (s.doubleCosetEquiv.apply_symm_apply y).trans
        ((DoubleCoset.mem_quotToDoubleCoset_iff y g).mp hg).symm
    exact Set.disjoint_left.mp (s.disjoint (ne_of_lt ha)) hag hjg
  have hg : (s.representative i)⁻¹ ∈ closure (DoubleCoset.quotToDoubleCoset P Q y) :=
    hxy ((DoubleCoset.mem_quotToDoubleCoset_iff x _).mpr
      (s.doubleCosetEquiv.apply_symm_apply x))
  exact (closure_minimal hsub hclosed hg)
    ⟨i, hij, (quotientMap_mem_cosetOrbit_iff P Q _ _).mpr rfl⟩

/-- Reverse the finite orbit order to obtain a linear refinement of Bruhat closure. -/
abbrev bruhatLinearOrder : LinearOrder (DoubleCoset.Quotient (P : Set G) Q) :=
  LinearOrder.lift' (β := (Fin n)ᵒᵈ) (fun x => OrderDual.toDual (s.doubleCosetEquiv.symm x))
    s.doubleCosetEquiv.symm.injective

omit [IsTopologicalGroup G] in
theorem isBruhatRefinement_bruhatLinearOrder :
    IsBruhatRefinement P Q s.bruhatLinearOrder :=
  fun _ _ h => s.bruhatLE_index_antitone h

end Langlands.Geometric.OrderedDoubleCosets

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance identitySupportAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : M ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ 1)
  (hsame : l ≫ p = lQ ≫ q)

include hsame in
omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- At the identity, the source intersection with a parabolic containing the
same Levi is the full original Levi scheme. -/
theorem isIso_source_at_one : IsIso D.p' := by
  have hj : IsClosedSubgroup (l ≫ p) := hl.isClosedSubgroup.comp hp.isClosedSubgroup
  have : IsClosedImmersion (l ≫ p).hom.hom.left := hj
  have : Mono (l ≫ p).hom.hom := Over.mono_of_mono_left _
  have hrange : SubgroupFunctor.range D.p' =
      (SubgroupFunctor.range q).comap (l ≫ p) :=
    SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf D.p' (l ≫ p)
      (SubgroupFunctor.range q) (by
        simpa only [Category.assoc, innerIso_one_hom, Category.comp_id] using D.parabolic_eq)
  have hfull : SubgroupFunctor.range D.p' = ⊤ := by
    rw [hrange]
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    constructor
    · intro _
      trivial
    intro _
    apply SubgroupFunctor.mem_comap.mpr
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨x ≫ lQ.hom.hom, ?_⟩
    have heq := congrArg (fun f : M ⟶ G => f.hom.hom) hsame
    simpa only [Grp.comp_hom_hom, Category.assoc] using congrArg (fun f => x ≫ f) heq.symm
  have : IsClosedImmersion D.p'.hom.hom.left := D.hp'.isClosedSubgroup
  exact isIso_of_full_range D.p' (Over.mono_of_mono_left _) hfull

include hsame in
omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- Conjugation at the identity induces the identity automorphism of the common Levi. -/
theorem leviConjugation_at_one [IsIso D.p'] : D.leviConjugation.hom = 𝟙 M := by
  have hj : IsClosedSubgroup (l ≫ p) := hl.isClosedSubgroup.comp hp.isClosedSubgroup
  have : Mono (l ≫ p) := by
    have : Mono ((Grp.forget _ ⋙ Over.forget _).map (l ≫ p)) := hj.mono
    exact (Grp.forget _ ⋙ Over.forget _).mono_of_mono_map this
  apply (cancel_mono (l ≫ p)).mp
  simpa only [Category.assoc, innerIso_one_hom, Category.comp_id, Category.id_comp] using
    D.leviConjugation_comp hsame.symm

/-- The full intersection piece at the identity is equivariantly the original representation. -/
def identityPieceEquiv [IsIso D.p']
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    (D.pieceFunctor.obj σ).ρ.Equiv σ.representation := by
  letI := leviPointTopology l hl
  exact {
    __ := D.leviPieceEquiv σ
    isIntertwining' m := by
      apply LinearMap.ext
      intro x
      change D.leviPieceEquiv σ ((D.pieceFunctor.obj σ).ρ m x) =
        σ.representation m (D.leviPieceEquiv σ x)
      have h := D.leviPieceEquiv_representation σ m x
      rw [D.leviConjugation_at_one hsame] at h
      simpa only [rationalPoints.map_apply, Grp.id_hom_hom, MonoidHom.id_apply,
        Category.comp_id] using h }

/-- Evaluation at the identity followed by trivial coinvariants is natural
for every original smooth intertwiner. -/
theorem identityPieceEquiv_natural [IsIso D.p']
    (σ τ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (f : σ ⟶ τ) (x : D.pieceFunctor.obj σ) :
    letI := leviPointTopology l hl
    D.identityPieceEquiv hsame τ ((D.pieceFunctor.map f).hom x) =
      SmoothRep.hom f (D.identityPieceEquiv hsame σ x) := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  have := D.isIso_l'_of_isIso_p'
  have := D.isIso_q'_of_isIso_p'_of_iso (Iso.refl M)
  have := D.isIso_lQ'_of_isIso_p'_of_iso (Iso.refl M)
  let J := leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul'
  let y := isoParabolicInductionEquiv D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ' D.hmulQ'
    ((SmoothRep.pullbackFunctor D.e).obj (J.obj σ)) x
  change fullLeviJacquetEquiv D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' τ
      (SmoothRep.hom (J.map f) y) =
    SmoothRep.hom f (fullLeviJacquetEquiv D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' σ y)
  obtain ⟨v, hv⟩ := Jacquet.Localization.mk_surjective σ.representation
    (pointImage (D.r' ≫ D.p')) 1 y
  rw [← hv]
  rfl

end GeometricLemmaIntersectionDatum

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
/-- Renard VII.3.2: all support inclusions and geometric subquotient comparisons,
including the natural identity-functor identification at the identity class. -/
theorem pqSupportGraded : PQSupportGradedStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have hcompare := pqSupportComparisons.{u, v} k G hG P M N Q U
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame
  refine ⟨hcompare, ?_⟩
  obtain ⟨m, c, z₀, hz₀, D₀, hglued⟩ :=
    representedGeometricLemma.{u, v} k G hG P M N Q M U
      p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  have hfinite : Finite (parabolicDoubleCosets p q) := Finite.of_surjective c c.surjective
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have : SigmaCompactSpace (rationalPoints G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨n, ⟨s⟩⟩ := Geometric.closedSubgroupOrbitOrdering (rationalPoints G)
    (pointImage p) (pointImage q) (isClosed_pointImage p hp.isClosedSubgroup)
      (isClosed_pointImage q hq.isClosedSubgroup) hfinite
  let o := s.bruhatLinearOrder
  have ho : Geometric.IsBruhatRefinement (pointImage p) (pointImage q) o :=
    s.isBruhatRefinement_bruhatLinearOrder
  obtain ⟨T, i, hi, t, ht⟩ :=
    ParabolicLeviTorus.exists_maximalSplitTorus_factor parabolicDynamic hG hp hl
  let D := geometricLemmaIntersectionDatumOfTorusFactors parabolicDynamic hG
    p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ 1 i hi t ht t
    (by simpa only [innerIso_one_hom, Category.comp_id, ← hsame] using ht)
  have : IsIso D.p' := D.isIso_source_at_one hsame
  obtain ⟨e₀⟩ := (hcompare o ho (identityParabolicDoubleCoset p q)).2.1
  obtain ⟨e₁⟩ := (hcompare o ho (identityParabolicDoubleCoset p q)).2.2 1 rfl D
  let e := e₀.symm ≪≫ e₁
  refine ⟨fun W => (Representation.equivOfIso (e.app W)).trans (D.identityPieceEquiv hsame W), ?_⟩
  intro W W' f x
  have hn := congrArg (fun a => a.hom x) (e.hom.naturality f)
  change (e.hom.app W').hom
      (((closureSupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (identityParabolicDoubleCoset p q)).quotientMap
          (boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
            (identityParabolicDoubleCoset p q)) f).hom x) =
    (D.pieceFunctor.map f).hom ((e.hom.app W).hom x) at hn
  exact (congrArg (D.identityPieceEquiv hsame W') hn).trans
    (D.identityPieceEquiv_natural hsame W W' f ((e.hom.app W).hom x))

end Langlands.Aubert.General.RepresentedParabolic
