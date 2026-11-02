import Langlands.AlgebraicGeometry.PointTopology.SchemePullbackCharts
import Langlands.AlgebraicGeometry.PointTopology.SchemeCompatiblePairCharts
import Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemePullbackStatements

/-! # Nonaffine pullback point comparison -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

variable [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S]

/-- On a compatible affine chart the inverse point comparison is continuous. -/
theorem continuous_schemePullbackInverse_onChart
    {X Y Z : Over (Spec (CommRingCat.of R))}
    {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) (hc : IsLimit c)
    {U V W : Over (Spec (CommRingCat.of R))}
    [IsAffine U.left] [IsAffine V.left] [IsAffine W.left]
    {F : U ⟶ W} {G : V ⟶ W}
    (a : U ⟶ X) (b : V ⟶ Y) (d : W ⟶ Z)
    (ha : F ≫ d = a ≫ f) (hb : G ≫ d = b ≫ g) :
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    letI : TopologicalSpace (RingPoint R c.pt S) := schemePointTopology R c.pt S
    Continuous ((affineSchemePullbackPointEquiv R S c hc).symm ∘
      schemeCompatiblePairMap R S a b d ha hb) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  let : TopologicalSpace (RingPoint R c.pt S) := schemePointTopology R c.pt S
  let p := relativeSchemePullback R F G
  let hp := relativeSchemePullbackIsLimit R F G
  have hcomm : (p.fst ≫ a) ≫ f = (p.snd ≫ b) ≫ g := by
    calc
      (p.fst ≫ a) ≫ f = (p.fst ≫ F) ≫ d := by
        simp only [Category.assoc, ← ha]
      _ = (p.snd ≫ G) ≫ d := congrArg (fun h => h ≫ d) p.condition
      _ = (p.snd ≫ b) ≫ g := by simp only [Category.assoc, hb]
  let i : p.pt ⟶ c.pt := PullbackCone.IsLimit.lift hc
    (p.fst ≫ a) (p.snd ≫ b) hcomm
  let H := affineSchemePullbackPointHomeomorph R S p hp
  let k : RingPoint R p.pt S → RingPoint R c.pt S := fun r => r ≫ i
  have hk : Continuous k := continuous_affineToSchemePointMap R S i
  have heq : (affineSchemePullbackPointEquiv R S c hc).symm ∘
      schemeCompatiblePairMap R S a b d ha hb = k ∘ H.symm := by
    funext q
    have hq := H.apply_symm_apply q
    have hq₁ : (H.symm q) ≫ p.fst = q.1.1 :=
      congrArg (fun z => z.val.1) hq
    have hq₂ : (H.symm q) ≫ p.snd = q.1.2 :=
      congrArg (fun z => z.val.2) hq
    dsimp only [RingPoint] at q ⊢
    apply PullbackCone.IsLimit.hom_ext hc
    · change (PullbackCone.IsLimit.lift hc (q.1.1 ≫ a) (q.1.2 ≫ b) _) ≫ c.fst =
        ((H.symm q) ≫ i) ≫ c.fst
      calc
        _ = q.1.1 ≫ a := PullbackCone.IsLimit.lift_fst hc _ _ _
        _ = (H.symm q ≫ p.fst) ≫ a :=
          (congrArg (fun t : ringTest R S ⟶ U => t ≫ a) hq₁).symm
        _ = H.symm q ≫ (p.fst ≫ a) := Category.assoc _ _ _
        _ = H.symm q ≫ (i ≫ c.fst) := congrArg
          (fun t : p.pt ⟶ X => H.symm q ≫ t)
          (PullbackCone.IsLimit.lift_fst hc _ _ _).symm
        _ = ((H.symm q) ≫ i) ≫ c.fst := (Category.assoc _ _ _).symm
    · change (PullbackCone.IsLimit.lift hc (q.1.1 ≫ a) (q.1.2 ≫ b) _) ≫ c.snd =
        ((H.symm q) ≫ i) ≫ c.snd
      calc
        _ = q.1.2 ≫ b := PullbackCone.IsLimit.lift_snd hc _ _ _
        _ = (H.symm q ≫ p.snd) ≫ b :=
          (congrArg (fun t : ringTest R S ⟶ V => t ≫ b) hq₂).symm
        _ = H.symm q ≫ (p.snd ≫ b) := Category.assoc _ _ _
        _ = H.symm q ≫ (i ≫ c.snd) := congrArg
          (fun t : p.pt ⟶ Y => H.symm q ≫ t)
          (PullbackCone.IsLimit.lift_snd hc _ _ _).symm
        _ = ((H.symm q) ≫ i) ≫ c.snd := (Category.assoc _ _ _).symm
  rw [heq]
  exact hk.comp H.symm.continuous

/-- Compatible affine charts cover the compatible-pair space, so the inverse
comparison is continuous for arbitrary schemes. -/
theorem continuous_schemePullbackPointEquiv_symm
    {X Y Z : Over (Spec (CommRingCat.of R))}
    {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) (hc : IsLimit c) :
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    letI : TopologicalSpace (RingPoint R c.pt S) := schemePointTopology R c.pt S
    Continuous (affineSchemePullbackPointEquiv R S c hc).symm := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  let : TopologicalSpace (RingPoint R c.pt S) := schemePointTopology R c.pt S
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨W, hW, hqW, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Z.left) (x := (q.1.1 ≫ f).left (IsLocalRing.closedPoint S))
    (U := ⊤) (by trivial)
  let : IsAffine W := hW
  have hqU : q.1.1.left (IsLocalRing.closedPoint S) ∈ f.left ⁻¹ᵁ W := hqW
  have hpoint : (q.1.1 ≫ f).left (IsLocalRing.closedPoint S) =
      (q.1.2 ≫ g).left (IsLocalRing.closedPoint S) :=
    congrArg (fun p : RingPoint R Z S => p.left (IsLocalRing.closedPoint S)) q.2
  have hqV : q.1.2.left (IsLocalRing.closedPoint S) ∈ g.left ⁻¹ᵁ W := by
    change (q.1.2 ≫ g).left (IsLocalRing.closedPoint S) ∈ W
    exact hpoint ▸ hqW
  obtain ⟨U, hU, hqU, hUW⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.left) (x := q.1.1.left (IsLocalRing.closedPoint S))
    (U := f.left ⁻¹ᵁ W) hqU
  obtain ⟨V, hV, hqV, hVW⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y.left) (x := q.1.2.left (IsLocalRing.closedPoint S))
    (U := g.left ⁻¹ᵁ W) hqV
  let : IsAffine U := hU
  let : IsAffine V := hV
  let a := openOverι R X U
  let b := openOverι R Y V
  let d := openOverι R Z W
  let : Mono d.left := inferInstanceAs (Mono W.ι)
  let : Mono d := Over.mono_of_mono_left d
  have haRange : Set.range (a ≫ f).left ⊆ W := by
    rintro z ⟨u, rfl⟩
    exact hUW u.property
  have hbRange : Set.range (b ≫ g).left ⊆ W := by
    rintro z ⟨v, rfl⟩
    exact hVW v.property
  let F := relativeOpenLift R (a ≫ f) W haRange
  let G := relativeOpenLift R (b ≫ g) W hbRange
  have ha : F ≫ d = a ≫ f := relativeOpenLift_fac R (a ≫ f) W haRange
  have hb : G ≫ d = b ≫ g := relativeOpenLift_fac R (b ≫ g) W hbRange
  have haOpen : @IsOpenEmbedding (RingPoint R (openOver R X U) S)
      (RingPoint R X S) inferInstance inferInstance (fun p => p ≫ a) :=
    isOpenEmbedding_schemeAffineChart R S X ⟨U, hU⟩
  have hbOpen : @IsOpenEmbedding (RingPoint R (openOver R Y V) S)
      (RingPoint R Y S) inferInstance inferInstance (fun p => p ≫ b) :=
    isOpenEmbedding_schemeAffineChart R S Y ⟨V, hV⟩
  have hChart := isOpenEmbedding_schemeCompatiblePairMap R S a b d ha hb haOpen hbOpen
  have hrU : Set.range q.1.1.left ⊆ U :=
    (range_subset_open_iff_closedPoint R X S U q.1.1).mpr hqU
  have hrV : Set.range q.1.2.left ⊆ V :=
    (range_subset_open_iff_closedPoint R Y S V q.1.2).mpr hqV
  let pU := openPointLift R X S U q.1.1 hrU
  let pV := openPointLift R Y S V q.1.2 hrV
  have hpU : pU ≫ a = q.1.1 := openPointMap_lift R X S U q.1.1 hrU
  have hpV : pV ≫ b = q.1.2 := openPointMap_lift R Y S V q.1.2 hrV
  have hpair : pU ≫ F = pV ≫ G :=
    (schemeCompatiblePair_iff R S a b d ha hb (pU, pV)).mpr
      ((congrArg (fun p : RingPoint R X S => p ≫ f) hpU).trans
        (q.2.trans (congrArg (fun p : RingPoint R Y S => p ≫ g) hpV).symm))
  let t : {p : RingPoint R (openOver R X U) S ×
      RingPoint R (openOver R Y V) S // p.1 ≫ F = p.2 ≫ G} := ⟨(pU, pV), hpair⟩
  have ht : schemeCompatiblePairMap R S a b d ha hb t = q :=
    Subtype.ext (Prod.ext hpU hpV)
  have hContinuous := continuous_schemePullbackInverse_onChart R S c hc a b d ha hb
  have hAt := hChart.continuousAt_iff.mp (hContinuous.continuousAt (x := t))
  rw [ht] at hAt
  exact hAt

/-- The actual pullback comparison is continuous for the final point topologies. -/
theorem continuous_schemePullbackPointComparison
    {X Y Z : Over (Spec (CommRingCat.of R))}
    {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    letI : TopologicalSpace (RingPoint R c.pt S) := schemePointTopology R c.pt S
    Continuous (affineSchemePullbackPointComparison R S c) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  let : TopologicalSpace (RingPoint R c.pt S) := schemePointTopology R c.pt S
  exact ((schemePointContinuity_proof R S _ _ c.fst).prodMk
    (schemePointContinuity_proof R S _ _ c.snd)).subtype_mk _

/-- The canonical relative-point bijection is a homeomorphism, including for
nonaffine schemes. -/
def schemePullbackPointHomeomorph
    {X Y Z : Over (Spec (CommRingCat.of R))}
    {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) (hc : IsLimit c) :
    letI : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    letI : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    letI : TopologicalSpace (RingPoint R c.pt S) := schemePointTopology R c.pt S
    RingPoint R c.pt S ≃ₜ
      {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g} := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  let : TopologicalSpace (RingPoint R c.pt S) := schemePointTopology R c.pt S
  exact
    { toEquiv := affineSchemePullbackPointEquiv R S c hc
      continuous_toFun := continuous_schemePullbackPointComparison R S c
      continuous_invFun := continuous_schemePullbackPointEquiv_symm R S c hc }

/-- The exact proposition-valued pullback target. -/
theorem schemePointPullback_proof : SchemePointPullbackProperty R S := by
  intro X Y Z f g c hc
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
  let : TopologicalSpace (RingPoint R c.pt S) := schemePointTopology R c.pt S
  exact (schemePullbackPointHomeomorph R S c hc).isHomeomorph

end Langlands.AlgebraicGeometry.PointTopology
