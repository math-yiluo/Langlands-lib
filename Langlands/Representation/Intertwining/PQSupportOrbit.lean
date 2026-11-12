import Langlands.Representation.Intertwining.PQSupportInclusions
import Langlands.Representation.Geometric.OpenSupportOrbitQuotient
import Langlands.Representation.Geometric.CompactSmoothComparison
import Langlands.Representation.Geometric.OrbitRepresentatives
import Langlands.Representation.Geometric.RepresentedParabolicSupportJacquet
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof

/-! # Open support pairs for the PQ support quotients -/

noncomputable section

open CategoryTheory

namespace Langlands.Geometric

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual double-coset class of a point of the inducing quotient. -/
def leftQuotientDoubleCoset (P Q : Subgroup G) :
    Induction.LeftQuotient P → DoubleCoset.Quotient (P : Set G) Q :=
  Quotient.lift (DoubleCoset.mk P Q) (by
    intro x y hxy
    have h : x * y⁻¹ ∈ P :=
      QuotientGroup.rightRel_apply.mp ((QuotientGroup.rightRel P).symm hxy)
    simpa only [inv_mul_cancel_right] using
      (DoubleCoset.mk_mem_mul (K := Q) (⟨x * y⁻¹, h⟩ : P) y))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem leftQuotientDoubleCoset_mk (P Q : Subgroup G) (x : G) :
    leftQuotientDoubleCoset P Q (Induction.quotientMap P x) = DoubleCoset.mk P Q x := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Passing a union of double cosets to the inducing quotient preserves its class condition. -/
theorem image_preimage_doubleCoset (P Q : Subgroup G)
    (T : Set (DoubleCoset.Quotient (P : Set G) Q)) :
    Induction.quotientMap P '' (DoubleCoset.mk P Q ⁻¹' T) =
      leftQuotientDoubleCoset P Q ⁻¹' T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    obtain ⟨y, rfl⟩ := Quotient.exists_rep x
    exact ⟨y, hx, rfl⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem leftQuotientDoubleCoset_right (P Q : Subgroup G)
    (q : Q) (x : Induction.LeftQuotient P) :
    leftQuotientDoubleCoset P Q (Induction.quotientRight P (q : G) x) =
      leftQuotientDoubleCoset P Q x := by
  induction x using Quotient.inductionOn with
  | h x => exact DoubleCoset.mk_mul_mem q x

/-- A lower set for the orbit-closure relation is closed when there are finitely many orbits. -/
theorem isClosed_leftQuotientDoubleCoset_preimage (P Q : Subgroup G)
    [Finite (DoubleCoset.Quotient (P : Set G) Q)]
    (T : Set (DoubleCoset.Quotient (P : Set G) Q))
    (hT : ∀ x y, BruhatLE P Q x y → y ∈ T → x ∈ T) :
    IsClosed (leftQuotientDoubleCoset P Q ⁻¹' T) := by
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel P)).isCoinducing.isClosed_preimage.mp
  change IsClosed (DoubleCoset.mk P Q ⁻¹' T)
  have heq : DoubleCoset.mk P Q ⁻¹' T =
      ⋃ w ∈ T, closure (DoubleCoset.quotToDoubleCoset P Q w) := by
    ext g
    constructor
    · intro hg
      exact Set.mem_iUnion.mpr ⟨DoubleCoset.mk P Q g,
        Set.mem_iUnion.mpr ⟨hg, subset_closure
          ((DoubleCoset.mem_quotToDoubleCoset_iff _ _).mpr rfl)⟩⟩
    · intro hg
      obtain ⟨w, hg⟩ := Set.mem_iUnion.mp hg
      obtain ⟨hwT, hg⟩ := Set.mem_iUnion.mp hg
      exact hT _ _ ((mem_closure_doubleCoset_iff_bruhatLE P Q w g).mp hg) hwT
  rw [heq]
  exact (Set.toFinite T).isClosed_biUnion (fun _ _ => isClosed_closure)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The orbit at `z` is the fiber of the double-coset class map. -/
theorem mem_cosetOrbit_inv_iff (P Q : Subgroup G) (z : G)
    (x : Induction.LeftQuotient P) :
    x ∈ cosetOrbit P Q z⁻¹ ↔
      leftQuotientDoubleCoset P Q x = DoubleCoset.mk P Q z := by
  induction x using Quotient.inductionOn with
  | h x =>
    change Induction.quotientMap P x ∈ cosetOrbit P Q z⁻¹ ↔
      DoubleCoset.mk P Q x = DoubleCoset.mk P Q z
    simpa only [inv_inv, eq_comm] using (quotientMap_mem_cosetOrbit_iff P Q z⁻¹ x)

variable (P Q : Subgroup G) [Finite (DoubleCoset.Quotient (P : Set G) Q)]
  (o : LinearOrder (DoubleCoset.Quotient (P : Set G) Q))
  (ho : IsBruhatRefinement P Q o)

/-- The two total-order supports at a double coset form an actual open orbit pair. -/
def initialVanishingSupportPair (z : G) : OpenOrbitSupportPair P Q z⁻¹ where
  lower := (leftQuotientDoubleCoset P Q ⁻¹' {w | o.le w (DoubleCoset.mk P Q z)})ᶜ
  upper := (leftQuotientDoubleCoset P Q ⁻¹' {w | o.lt w (DoubleCoset.mk P Q z)})ᶜ
  lower_invariant := by
    intro q x hx
    simpa only [Set.mem_compl_iff, Set.mem_preimage, leftQuotientDoubleCoset_right] using hx
  upper_invariant := by
    intro q x hx
    simpa only [Set.mem_compl_iff, Set.mem_preimage, leftQuotientDoubleCoset_right] using hx
  lower_open := (isClosed_leftQuotientDoubleCoset_preimage P Q _
    (fun x y hxy hy => o.le_trans _ _ _ (ho _ _ hxy) hy)).isOpen_compl
  upper_open := by
    let := o
    exact (isClosed_leftQuotientDoubleCoset_preimage P Q _
      (fun x y hxy hy => lt_of_le_of_lt (ho _ _ hxy) hy)).isOpen_compl
  lower_subset_upper := by
    intro x hx hlt
    exact hx ((o.lt_iff_le_not_ge _ _).mp hlt).1
  difference := by
    let := o
    ext x
    rw [mem_cosetOrbit_inv_iff]
    change (¬o.lt (leftQuotientDoubleCoset P Q x) (DoubleCoset.mk P Q z) ∧
      ¬¬o.le (leftQuotientDoubleCoset P Q x) (DoubleCoset.mk P Q z)) ↔ _
    rw [not_not]
    exact ⟨fun h => le_antisymm h.2 (not_lt.mp h.1),
      fun h => by rw [h]; exact ⟨lt_irrefl _, le_refl _⟩⟩

include ho in
/-- The strict orbit boundary is closed in the inducing quotient. -/
theorem isClosed_bruhatLT_preimage (w : DoubleCoset.Quotient (P : Set G) Q) :
    IsClosed (leftQuotientDoubleCoset P Q ⁻¹' {x | BruhatLT P Q x w}) := by
  apply isClosed_leftQuotientDoubleCoset_preimage P Q
  intro x y hxy hy
  refine ⟨bruhatLE_trans hxy hy.1, ?_⟩
  intro hxw
  apply hy.2
  exact o.le_antisymm _ _ (ho _ _ hy.1) (hxw ▸ ho _ _ hxy)

/-- The closure and boundary vanishing supports form another open pair for the same orbit. -/
def boundaryVanishingSupportPair (z : G) : OpenOrbitSupportPair P Q z⁻¹ where
  lower := (leftQuotientDoubleCoset P Q ⁻¹' {w | BruhatLE P Q w (DoubleCoset.mk P Q z)})ᶜ
  upper := (leftQuotientDoubleCoset P Q ⁻¹' {w | BruhatLT P Q w (DoubleCoset.mk P Q z)})ᶜ
  lower_invariant := by
    intro q x hx
    simpa only [Set.mem_compl_iff, Set.mem_preimage, leftQuotientDoubleCoset_right] using hx
  upper_invariant := by
    intro q x hx
    simpa only [Set.mem_compl_iff, Set.mem_preimage, leftQuotientDoubleCoset_right] using hx
  lower_open := (isClosed_leftQuotientDoubleCoset_preimage P Q _
    (fun _ _ hxy hy => bruhatLE_trans hxy hy)).isOpen_compl
  upper_open := (isClosed_bruhatLT_preimage P Q o ho _).isOpen_compl
  lower_subset_upper := by
    intro x hx hlt
    exact hx hlt.1
  difference := by
    ext x
    rw [mem_cosetOrbit_inv_iff]
    change (¬BruhatLT P Q (leftQuotientDoubleCoset P Q x) (DoubleCoset.mk P Q z) ∧
      ¬¬BruhatLE P Q (leftQuotientDoubleCoset P Q x) (DoubleCoset.mk P Q z)) ↔ _
    rw [not_not]
    constructor
    · intro h
      by_contra hne
      exact h.1 ⟨h.2, hne⟩
    · intro h
      rw [h]
      exact ⟨fun hlt => hlt.2 rfl, bruhatLE_refl P Q _⟩

namespace OpenOrbitSupportPair

universe uG uV

variable {H : Type uG} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  {P Q : Subgroup H} {w : H} (s : OpenOrbitSupportPair P Q w)

/-- The lower smooth support space of the pair, restricted to smooth covariance data. -/
def lowerSmoothSupport :
    RepSubfunctor
      (SmoothRep.toRep ⋙ rawRestrictedSmoothInduction.{0, uG, uV} (R := ℂ) P Q) :=
  (rawSmoothSupportSubfunctor P Q s.lower s.lower_invariant).precomp SmoothRep.toRep

/-- The upper smooth support space of the pair, restricted to smooth covariance data. -/
def upperSmoothSupport :
    RepSubfunctor
      (SmoothRep.toRep ⋙ rawRestrictedSmoothInduction.{0, uG, uV} (R := ℂ) P Q) :=
  (rawSmoothSupportSubfunctor P Q s.upper s.upper_invariant).precomp SmoothRep.toRep

variable [LocallyCompactSpace H] [SigmaCompactSpace H]
  [T2Space H] [CompactSpace (Induction.LeftQuotient P)]

/-- On a compact inducing quotient, the actual smooth support subquotient of
any open orbit pair is naturally its compact stabilizer-induction piece. -/
def smoothSupportQuotientIso (hP : IsClosed (P : Set H)) (hQ : IsClosed (Q : Set H)) :
    s.lowerSmoothSupport.{uG, uV}.quotientFunctor s.upperSmoothSupport ≅
      orbitPiece.{0, uG, uV} (R := ℂ) P Q w := by
  let S := supportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.lower s.lower_invariant
  let T := supportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.upper s.upper_invariant
  let e : T.toFunctor ≅ s.upperSmoothSupport.toFunctor :=
    Functor.isoWhiskerLeft SmoothRep.toRep
      (rawSupportCompactSmoothIso P Q s.upper s.upper_invariant)
  exact (RepSubfunctor.quotientNatIso S T s.lowerSmoothSupport s.upperSmoothSupport
    e (fun _ _ => Iff.rfl)).symm ≪≫ s.quotientIso hP hQ

end OpenOrbitSupportPair

end Langlands.Geometric

universe u v

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance supportPairAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G)
  [Finite (parabolicDoubleCosets p q)]
  (o : LinearOrder (parabolicDoubleCosets p q))
  (ho : Geometric.IsBruhatRefinement (pointImage p) (pointImage q) o)
  (z : rationalPoints G)

private theorem initialVanishing_eq_pairLower :
    initialVanishingSubfunctor.{u, v} p l r hp hr hl hmul q o
        (DoubleCoset.mk (pointImage p) (pointImage q) z) =
      (Geometric.rawSmoothSupportSubfunctor (R := ℂ) (pointImage p) (pointImage q)
        (Geometric.initialVanishingSupportPair (pointImage p) (pointImage q) o ho z).lower
        (Geometric.initialVanishingSupportPair (pointImage p) (pointImage q) o ho z).lower_invariant).precomp
          (leviInducingFunctor p l r hp hr hl hmul) := by
  unfold initialVanishingSubfunctor leviVanishingSubfunctor
    Geometric.rawSmoothVanishingSubfunctor
  simp_rw [Geometric.image_preimage_doubleCoset]
  rfl

private theorem strictInitialVanishing_eq_pairUpper :
    strictInitialVanishingSubfunctor.{u, v} p l r hp hr hl hmul q o
        (DoubleCoset.mk (pointImage p) (pointImage q) z) =
      (Geometric.rawSmoothSupportSubfunctor (R := ℂ) (pointImage p) (pointImage q)
        (Geometric.initialVanishingSupportPair (pointImage p) (pointImage q) o ho z).upper
        (Geometric.initialVanishingSupportPair (pointImage p) (pointImage q) o ho z).upper_invariant).precomp
          (leviInducingFunctor p l r hp hr hl hmul) := by
  unfold strictInitialVanishingSubfunctor leviVanishingSubfunctor
    Geometric.rawSmoothVanishingSubfunctor
  simp_rw [Geometric.image_preimage_doubleCoset]
  rfl

private theorem closureVanishing_eq_pairLower :
    closureVanishingSubfunctor.{u, v} p l r hp hr hl hmul q
        (DoubleCoset.mk (pointImage p) (pointImage q) z) =
      (Geometric.rawSmoothSupportSubfunctor (R := ℂ) (pointImage p) (pointImage q)
        (Geometric.boundaryVanishingSupportPair (pointImage p) (pointImage q) o ho z).lower
        (Geometric.boundaryVanishingSupportPair (pointImage p) (pointImage q) o ho z).lower_invariant).precomp
          (leviInducingFunctor p l r hp hr hl hmul) := by
  have heq : closure (DoubleCoset.quotToDoubleCoset (pointImage p) (pointImage q)
      (DoubleCoset.mk (pointImage p) (pointImage q) z)) =
      DoubleCoset.mk (pointImage p) (pointImage q) ⁻¹'
        {w | Geometric.BruhatLE (pointImage p) (pointImage q) w
          (DoubleCoset.mk (pointImage p) (pointImage q) z)} :=
    Set.ext (fun g => Geometric.mem_closure_doubleCoset_iff_bruhatLE _ _ _ g)
  unfold closureVanishingSubfunctor leviVanishingSubfunctor
    Geometric.rawSmoothVanishingSubfunctor
  simp_rw [heq, Geometric.image_preimage_doubleCoset]
  rfl

private theorem boundaryVanishing_eq_pairUpper :
    boundaryVanishingSubfunctor.{u, v} p l r hp hr hl hmul q
        (DoubleCoset.mk (pointImage p) (pointImage q) z) =
      (Geometric.rawSmoothSupportSubfunctor (R := ℂ) (pointImage p) (pointImage q)
        (Geometric.boundaryVanishingSupportPair (pointImage p) (pointImage q) o ho z).upper
        (Geometric.boundaryVanishingSupportPair (pointImage p) (pointImage q) o ho z).upper_invariant).precomp
          (leviInducingFunctor p l r hp hr hl hmul) := by
  have heq : closure (DoubleCoset.quotToDoubleCoset (pointImage p) (pointImage q)
      (DoubleCoset.mk (pointImage p) (pointImage q) z)) \
      DoubleCoset.quotToDoubleCoset (pointImage p) (pointImage q)
        (DoubleCoset.mk (pointImage p) (pointImage q) z) =
      DoubleCoset.mk (pointImage p) (pointImage q) ⁻¹'
        {w | Geometric.BruhatLT (pointImage p) (pointImage q) w
          (DoubleCoset.mk (pointImage p) (pointImage q) z)} := by
    ext g
    simp only [Set.mem_sdiff, Geometric.mem_closure_doubleCoset_iff_bruhatLE,
      DoubleCoset.mem_quotToDoubleCoset_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      Geometric.BruhatLT]
  unfold boundaryVanishingSubfunctor leviVanishingSubfunctor
    Geometric.rawSmoothVanishingSubfunctor
  simp_rw [heq, Geometric.image_preimage_doubleCoset]
  rfl

variable [CompactSpace (Induction.LeftQuotient (pointImage p))]
  [T2Space (rationalPoints G)] [SigmaCompactSpace (rationalPoints G)]

/-- The total-order vanishing quotient is the actual compact orbit piece. -/
def initialVanishingQuotientOrbitIso (hq : IsParabolicSubgroup q) :
    letI := leviPointTopology l hl
    (initialVanishingSubfunctor.{u, v} p l r hp hr hl hmul q o
      (DoubleCoset.mk (pointImage p) (pointImage q) z)).quotientFunctor
        (strictInitialVanishingSubfunctor p l r hp hr hl hmul q o
          (DoubleCoset.mk (pointImage p) (pointImage q) z)) ≅
      smoothLeviInducingFunctor p l r hp hr hl hmul ⋙
        Geometric.orbitPiece (pointImage p) (pointImage q) z⁻¹ := by
  letI := leviPointTopology l hl
  rw [initialVanishing_eq_pairLower p l r hp hr hl hmul q o ho z,
    strictInitialVanishing_eq_pairUpper p l r hp hr hl hmul q o ho z]
  exact Functor.isoWhiskerLeft (smoothLeviInducingFunctor p l r hp hr hl hmul)
    ((Geometric.initialVanishingSupportPair (pointImage p) (pointImage q) o ho z).smoothSupportQuotientIso
      (isClosed_pointImage p hp.isClosedSubgroup) (isClosed_pointImage q hq.isClosedSubgroup))

/-- The closure/boundary vanishing quotient is the same actual compact orbit piece. -/
def boundaryVanishingQuotientOrbitIso (hq : IsParabolicSubgroup q) :
    letI := leviPointTopology l hl
    (closureVanishingSubfunctor.{u, v} p l r hp hr hl hmul q
      (DoubleCoset.mk (pointImage p) (pointImage q) z)).quotientFunctor
        (boundaryVanishingSubfunctor p l r hp hr hl hmul q
          (DoubleCoset.mk (pointImage p) (pointImage q) z)) ≅
      smoothLeviInducingFunctor p l r hp hr hl hmul ⋙
        Geometric.orbitPiece (pointImage p) (pointImage q) z⁻¹ := by
  letI := leviPointTopology l hl
  rw [closureVanishing_eq_pairLower p l r hp hr hl hmul q o ho z,
    boundaryVanishing_eq_pairUpper p l r hp hr hl hmul q o ho z]
  exact Functor.isoWhiskerLeft (smoothLeviInducingFunctor p l r hp hr hl hmul)
    ((Geometric.boundaryVanishingSupportPair (pointImage p) (pointImage q) o ho z).smoothSupportQuotientIso
      (isClosed_pointImage p hp.isClosedSubgroup) (isClosed_pointImage q hq.isClosedSubgroup))

variable {U : GroupScheme (Spec (CommRingCat.of k))}
  (lQ : M ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  (hU : Jacquet.Localization.IsLimitOfCompactSubgroups (parabolicRadicalPoints q rQ))

/-- The total-order support-image quotient is normalized target coinvariants
of its actual compact orbit piece. -/
def initialSupportQuotientOrbitIso :
    letI := leviPointTopology l hl
    (initialSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ o
      (DoubleCoset.mk (pointImage p) (pointImage q) z)).quotientFunctor
        (strictInitialSupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ o
          (DoubleCoset.mk (pointImage p) (pointImage q) z)) ≅
      smoothLeviInducingFunctor p l r hp hr hl hmul ⋙
        Geometric.orbitPiece (pointImage p) (pointImage q) z⁻¹ ⋙
          leviParabolicCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ := by
  letI := leviPointTopology l hl
  exact leviJacquetImageQuotientIso p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
      (initialVanishingSubfunctor p l r hp hr hl hmul q o _)
      (strictInitialVanishingSubfunctor p l r hp hr hl hmul q o _) hU
      (fun W => (pqSupportInclusions p l r hp hr hl hmul q o ho _ W).1) ≪≫
    Functor.isoWhiskerRight
      (initialVanishingQuotientOrbitIso p l r hp hr hl hmul q o ho z hq)
      (leviParabolicCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ) ≪≫
    Functor.associator _ _ _

/-- The closure/boundary support-image quotient is normalized target coinvariants
of the same actual compact orbit piece. -/
def boundarySupportQuotientOrbitIso :
    letI := leviPointTopology l hl
    (closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
      (DoubleCoset.mk (pointImage p) (pointImage q) z)).quotientFunctor
        (boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
          (DoubleCoset.mk (pointImage p) (pointImage q) z)) ≅
      smoothLeviInducingFunctor p l r hp hr hl hmul ⋙
        Geometric.orbitPiece (pointImage p) (pointImage q) z⁻¹ ⋙
          leviParabolicCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ := by
  letI := leviPointTopology l hl
  exact leviJacquetImageQuotientIso p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
      (closureVanishingSubfunctor p l r hp hr hl hmul q _)
      (boundaryVanishingSubfunctor p l r hp hr hl hmul q _) hU
      (fun W => (pqSupportInclusions p l r hp hr hl hmul q o ho _ W).2.2) ≪≫
    Functor.isoWhiskerRight
      (boundaryVanishingQuotientOrbitIso p l r hp hr hl hmul q o ho z hq)
      (leviParabolicCoinvariantsFunctor q lQ rQ hq hrQ hlQ hmulQ) ≪≫
    Functor.associator _ _ _

/-- The two support-image subquotients in Renard VII.3.2 are naturally isomorphic. -/
def pqSupportSubquotientIso :
    letI := leviPointTopology l hl
    (initialSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ o
      (DoubleCoset.mk (pointImage p) (pointImage q) z)).quotientFunctor
        (strictInitialSupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ o
          (DoubleCoset.mk (pointImage p) (pointImage q) z)) ≅
      (closureSupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
        (DoubleCoset.mk (pointImage p) (pointImage q) z)).quotientFunctor
          (boundarySupportImage p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
            (DoubleCoset.mk (pointImage p) (pointImage q) z)) :=
  initialSupportQuotientOrbitIso p l r hp hr hl hmul q o ho z lQ rQ hq hrQ hlQ hmulQ hU ≪≫
    (boundarySupportQuotientOrbitIso p l r hp hr hl hmul q o ho z lQ rQ hq hrQ hlQ hmulQ hU).symm

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- The inclusions and both geometric support-subquotient comparisons of VII.3.2.
The final identity-functor identification is not part of this auxiliary theorem. -/
theorem pqSupportComparisons :
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
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
        haveI := hl.isConnectedReductive.isAffineHom
        letI := leviPointTopology l hl
        (∀ (o : LinearOrder (parabolicDoubleCosets p q)),
          Geometric.IsBruhatRefinement (pointImage p) (pointImage q) o →
          ∀ w : parabolicDoubleCosets p q,
            (∀ W : SmoothRep.{0, u, v} ℂ (rationalPoints M),
              (initialVanishingSubfunctor p l r hp hr hl hmul q o w).obj W ≤
                  (strictInitialVanishingSubfunctor p l r hp hr hl hmul q o w).obj W ∧
                (strictInitialVanishingSubfunctor p l r hp hr hl hmul q o w).obj W ≤
                  (boundaryVanishingSubfunctor p l r hp hr hl hmul q w).obj W ∧
                (closureVanishingSubfunctor p l r hp hr hl hmul q w).obj W ≤
                  (boundaryVanishingSubfunctor p l r hp hr hl hmul q w).obj W) ∧
            Nonempty
              ((initialSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ o w).quotientFunctor
                  (strictInitialSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ o w) ≅
                (closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ w).quotientFunctor
                  (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ w)) ∧
            ∀ (z : rationalPoints G),
              DoubleCoset.mk (pointImage p) (pointImage q) z = w →
              ∀ D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z,
                Nonempty
                  ((initialSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ o
                      w).quotientFunctor
                    (strictInitialSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ o w) ≅
                    D.pieceFunctor)) := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ _
  let := leviPointTopology l hl
  obtain ⟨m, c, z₀, hz₀, D₀, hglued⟩ :=
    representedGeometricLemma.{u, v} k G hG P M N Q M U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  have : Finite (parabolicDoubleCosets p q) := Finite.of_surjective c c.surjective
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have : SigmaCompactSpace (rationalPoints G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) :=
    arbitraryParabolicQuotientCompact k G hG P p hp
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hlQ.isConnectedReductive).1
  obtain ⟨pres⟩ := parabolicRootPresentationExistence k G hG Q M A q lQ a hq hlQ ha
  have hU : Jacquet.Localization.IsLimitOfCompactSubgroups (parabolicRadicalPoints q rQ) :=
    isLimitOfCompactSubgroups_subgroupOf _ _ (isClosed_pointImage q hq.isClosedSubgroup)
      (pointImage_radical_isLimitOfCompactSubgroups_of_presentation hG pres hrQ)
  intro o ho w
  refine ⟨fun W => pqSupportInclusions p l r hp hr hl hmul q o ho w W, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := Quotient.exists_rep w
    change DoubleCoset.mk (pointImage p) (pointImage q) z = w at hz
    subst w
    exact ⟨pqSupportSubquotientIso p l r hp hr hl hmul q o ho z lQ rQ hq hrQ hlQ hmulQ hU⟩
  · intro z hz D
    subst w
    obtain ⟨e⟩ := representedGeometricLemmaOrbitComparison.{u, v} k G hG P M N Q M U
      p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ z D
    exact ⟨initialSupportQuotientOrbitIso p l r hp hr hl hmul q o ho z
      lQ rQ hq hrQ hlQ hmulQ hU ≪≫ e⟩

end Langlands.Aubert.General.RepresentedParabolic
