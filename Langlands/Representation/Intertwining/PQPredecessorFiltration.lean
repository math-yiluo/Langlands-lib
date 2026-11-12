import Langlands.Representation.Geometric.OrbitRepresentatives
import Langlands.Representation.Intertwining.PQPredecessorOrder
import Langlands.Representation.Intertwining.PQIdentitySupportProof
import Langlands.Representation.Intertwining.PQRegularityFiltration

/-! # The actual regularity quotient filtered by strict predecessor pieces -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance predecessorAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))

/-- The strict-boundary vanishing subfunctor is support on the complement of
its actual lower class set. -/
theorem boundaryVanishing_eq_bruhatSupport (w : parabolicDoubleCosets p q) :
    boundaryVanishingSubfunctor.{u, v} p l r hp hr hl hmul q w =
      (Geometric.rawSmoothSupportSubfunctor (R := ℂ) (pointImage p) (pointImage q)
        (Geometric.leftQuotientDoubleCoset (pointImage p) (pointImage q) ⁻¹'
          {x | Geometric.BruhatLT (pointImage p) (pointImage q) x w})ᶜ
        (by
          intro x c hc
          simpa only [Set.mem_compl_iff, Set.mem_preimage,
            Geometric.leftQuotientDoubleCoset_right] using hc)).precomp
              (leviInducingFunctor p l r hp hr hl hmul) := by
  have heq : closure (DoubleCoset.quotToDoubleCoset (pointImage p) (pointImage q) w) \
      DoubleCoset.quotToDoubleCoset (pointImage p) (pointImage q) w =
      DoubleCoset.mk (pointImage p) (pointImage q) ⁻¹'
        {x | Geometric.BruhatLT (pointImage p) (pointImage q) x w} := by
    ext g
    simp only [Set.mem_sdiff, Geometric.mem_closure_doubleCoset_iff_bruhatLE,
      DoubleCoset.mem_quotToDoubleCoset_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      Geometric.BruhatLT]
  unfold boundaryVanishingSubfunctor leviVanishingSubfunctor
    Geometric.rawSmoothVanishingSubfunctor
  simp_rw [heq, Geometric.image_preimage_doubleCoset]
  rfl

/-- A prefix complementary to the strict predecessors has exactly the original
boundary-support Jacquet image. -/
theorem supportStep_eq_boundary {a b : ℕ}
    (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) (a + b))
    (hs : s.initialOrbits ⟨a, by omega⟩ =
      (Geometric.leftQuotientDoubleCoset (pointImage p) (pointImage q) ⁻¹'
        {x | Geometric.BruhatLT (pointImage p) (pointImage q) x
          (identityParabolicDoubleCoset p q)})ᶜ) :
    letI := leviPointTopology l hl
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      ((leviJacquetSupportFiltration p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ s).step
        (RepFunctorFiltration.tailIndex a b 0)).obj σ =
        (boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
          (identityParabolicDoubleCoset p q)).obj σ := by
  let := leviPointTopology l hl
  have hpre : (leviInductionSupportFiltration.{u, v} p l r hp hr hl hmul q s).step
      (RepFunctorFiltration.tailIndex a b 0) =
      boundaryVanishingSubfunctor p l r hp hr hl hmul q (identityParabolicDoubleCoset p q) := by
    rw [boundaryVanishing_eq_bruhatSupport p l r hp hr hl hmul q]
    unfold leviInductionSupportFiltration RepFunctorFiltration.precomp
      Geometric.OrderedDoubleCosets.rawSmoothSupportFiltration
    simp_rw [show RepFunctorFiltration.tailIndex a b 0 = ⟨a, by omega⟩ from Fin.ext (by simp
      [RepFunctorFiltration.tailIndex]), hs]
    rfl
  intro σ
  change (leviJacquetImageSubfunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    ((leviInductionSupportFiltration p l r hp hr hl hmul q s).step
      (RepFunctorFiltration.tailIndex a b 0))).obj σ = _
  rw [hpre]
  rfl

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
/-- The actual regularity quotient has a finite natural filtration whose grades
are precisely the supplied geometric pieces at all strict predecessors of identity. -/
theorem exists_pqRegularity_pieceFiltration
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      l ≫ p = lQ ≫ q →
      ∀ (z : parabolicDoubleCosets p q → rationalPoints G),
        (∀ w, DoubleCoset.mk (pointImage p) (pointImage q) (z w) = w) →
        ∀ (D : ∀ w, Geometric.BruhatLT (pointImage p) (pointImage q) w
            (identityParabolicDoubleCoset p q) →
            GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
              (z w)),
          letI := leviPointTopology l hl
          ∃ n, ∃ c : Fin n ≃ {w | Geometric.BruhatLT (pointImage p) (pointImage q) w
              (identityParabolicDoubleCoset p q)},
            ∃ s : RepFunctorFiltration
                (pqRegularityQuotientFunctor.{u, v} p l r hp hr hl hmul
                  q lQ rQ hq hrQ hlQ hmulQ) n,
              ∀ i, Nonempty (s.graded i ≅ (D (c i).val (c i).property).pieceFunctor) := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ _ z hz D
  let := leviPointTopology l hl
  obtain ⟨m, c₀, z₀, hz₀, D₀, hglued⟩ :=
    representedGeometricLemma.{u, v} k G hG P M N Q M U
      p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  have : Finite (parabolicDoubleCosets p q) := Finite.of_surjective c₀ c₀.surjective
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have : SigmaCompactSpace (rationalPoints G) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) :=
    arbitraryParabolicQuotientCompact k G hG P p hp
  obtain ⟨m₀, ⟨s₀⟩⟩ := Geometric.closedSubgroupOrbitOrdering (rationalPoints G)
    (pointImage p) (pointImage q) (isClosed_pointImage p hp.isClosedSubgroup)
      (isClosed_pointImage q hq.isClosedSubgroup) (by infer_instance)
  let o := s₀.bruhatLinearOrder
  have ho : Geometric.IsBruhatRefinement (pointImage p) (pointImage q) o :=
    s₀.isBruhatRefinement_bruhatLinearOrder
  let T : Set (parabolicDoubleCosets p q) :=
    {w | Geometric.BruhatLT (pointImage p) (pointImage q) w (identityParabolicDoubleCoset p q)}
  have hT : ∀ x y, Geometric.BruhatLE (pointImage p) (pointImage q) x y → y ∈ T → x ∈ T := by
    intro x y hxy hy
    refine ⟨Geometric.bruhatLE_trans hxy hy.1, ?_⟩
    intro hx
    apply hy.2
    exact o.le_antisymm _ _ (ho _ _ hy.1) (hx ▸ ho _ _ hxy)
  obtain ⟨a, b, s, c, hs, hc⟩ :=
    Geometric.exists_lowerSet_tail_ordering (pointImage p) (pointImage q) o ho T hT z hz
  have hrep : ∀ i, DoubleCoset.mk (pointImage p) (pointImage q)
      ((z (s.doubleCosetEquiv i))⁻¹)⁻¹ =
      DoubleCoset.mk (pointImage p) (pointImage q) (s.representative i)⁻¹ := by
    intro i
    simpa only [inv_inv] using
      (hz (s.doubleCosetEquiv i)).trans (s.doubleCosetEquiv_apply i)
  let t := s.replaceRepresentatives (fun i => (z (s.doubleCosetEquiv i))⁻¹) hrep
  have ht : t.initialOrbits ⟨a, by omega⟩ =
      (Geometric.leftQuotientDoubleCoset (pointImage p) (pointImage q) ⁻¹' T)ᶜ :=
    (s.initialOrbits_replaceRepresentatives _ hrep _).trans hs
  have hboundary := supportStep_eq_boundary p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ t ht
  let f := pqRegularitySupportFiltration p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ t hboundary
  refine ⟨b, c, f, ?_⟩
  intro i
  obtain ⟨A, aM, haM⟩ := (splitComponentStatement k M hlQ.isConnectedReductive).1
  obtain ⟨pres⟩ := parabolicRootPresentationExistence k G hG Q M A q lQ aM hq hlQ haM
  have hU : Jacquet.Localization.IsLimitOfCompactSubgroups (parabolicRadicalPoints q rQ) :=
    isLimitOfCompactSubgroups_subgroupOf _ _ (isClosed_pointImage q hq.isClosedSubgroup)
      (pointImage_radical_isLimitOfCompactSubgroups_of_presentation hG pres hrQ)
  have hti : t.representative (Fin.natAdd a i) = (z (c i).val)⁻¹ := by
    change (z (s.doubleCosetEquiv (Fin.natAdd a i)))⁻¹ = _
    rw [hc]
  have e₁ := leviJacquetSupportOrbitIso.{u, v} p l r hp hr hl hmul q lQ rQ
    hq hrQ hlQ hmulQ hU t (Fin.natAdd a i)
  rw [hti] at e₁
  obtain ⟨e₂⟩ := representedGeometricLemmaOrbitComparison.{u, v} k G hG P M N Q M U
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ (z (c i).val) (D _ (c i).property)
  exact ⟨(pqRegularitySupportGradedIso p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    t hboundary i).symm ≪≫ e₁ ≪≫ e₂⟩

/-- A chosen actual quotient filtration, its complete strict-predecessor index,
and its natural comparisons with the supplied full geometric pieces. -/
def pqRegularityPieceFiltration
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      l ≫ p = lQ ≫ q →
      ∀ (z : parabolicDoubleCosets p q → rationalPoints G),
        (∀ w, DoubleCoset.mk (pointImage p) (pointImage q) (z w) = w) →
        ∀ (D : ∀ w, Geometric.BruhatLT (pointImage p) (pointImage q) w
            (identityParabolicDoubleCoset p q) →
            GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
              (z w)),
          letI := leviPointTopology l hl
          Σ n, Σ c : Fin n ≃ {w | Geometric.BruhatLT (pointImage p) (pointImage q) w
              (identityParabolicDoubleCoset p q)},
            Σ s : RepFunctorFiltration
                (pqRegularityQuotientFunctor.{u, v} p l r hp hr hl hmul
                  q lQ rQ hq hrQ hlQ hmulQ) n,
              ∀ i, s.graded i ≅ (D (c i).val (c i).property).pieceFunctor := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame z hz D
  let := leviPointTopology l hl
  let h := exists_pqRegularity_pieceFiltration.{u, v} k G hG
    P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame z hz D
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    fun i => (h.choose_spec.choose_spec.choose_spec i).some⟩

end Langlands.Aubert.General.RepresentedParabolic
