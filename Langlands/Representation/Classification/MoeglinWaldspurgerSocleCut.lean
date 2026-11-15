import Langlands.Representation.Classification.MoeglinWaldspurgerCastCalculus
import Langlands.Representation.Classification.SegmentHeadSupportSplit
import Langlands.Representation.Classification.ArtinianSocleEmbedding
import Langlands.Representation.Twist.RealPower

/-!
# The socle cut

The Zelevinsky socle of a segment `[ρ, …, ν^(m-1) ρ]` with `m ≥ 2` embeds, up to rank
transport, into the binary product of a representative of `ρ` with the socle of the segment
`[νρ, …, ν^(m-1) ρ]`.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

theorem rankCast_map_injective {a b : ℕ} (h : a = b)
    {X Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (hf : letI := T.topology; Function.Injective (SmoothRep.hom f)) :
    letI := T.topology
    Function.Injective (SmoothRep.hom ((Derivative.generalLinearRankCast T h).map f)) := by
  subst h
  exact hf

theorem rankCast_nontrivial {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    [Nontrivial X] :
    letI := T.topology; Nontrivial ((Derivative.generalLinearRankCast T h).obj X) := by
  subst h
  assumption

theorem hasFiniteLength_rankCast' {a b : ℕ} (h : a = b)
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (hY : letI := T.topology; Y.HasFiniteLength) :
    letI := T.topology; ((Derivative.generalLinearRankCast T h).obj Y).HasFiniteLength := by
  subst h
  exact hY

theorem embeds_of_isSubrepresentation_rankCast {a b : ℕ} (h : a = b)
    {Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)}
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (hZ : letI := T.topology;
      SmoothRep.IsSubrepresentation Z ((Derivative.generalLinearRankCast T h).obj X)) :
    Embeds T Z X := by
  subst h
  exact ⟨rfl, hZ⟩

/-- The block `ν^0 A`, lifted, is `A` up to isomorphism. -/
theorem castIso_universeLift_segmentFactor_zero {r : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    CastIso T (SmoothRep.universeLift.{uF} (T.segmentFactor A ((0 : ℕ) : ℝ))) A := by
  let := T.topology
  have e₁ : T.segmentFactor A ((0 : ℕ) : ℝ) ≅ A := by
    rw [Nat.cast_zero]
    exact SmoothRep.mkIso (equivOfRepresentationEq
      (realPowerTwist_zero (T.determinantNorm r) A.representation))
  exact castIso_of_iso
    ((SmoothRep.mkIso (SmoothRep.universeLiftEquiv.{uF} (T.segmentFactor A ((0 : ℕ) : ℝ)))).symm
      ≪≫ e₁)

/-- **Socle cut.** -/
theorem socleCut_embeds {Δ : T.Segment.{max uF uV, uF}} {k : ℕ} (hm : Δ.length = k + 2)
    (A : letI := T.topology;
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A)
    {Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hZ : T.IsSegmentSocle Δ Z)
    {Z' : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((k + 1) * Δ.rank) F.Carrier)}
    (hZ' : T.IsSegmentSocle ⟨Δ.base.twist ((1 : ℕ) : ℝ), k + 1, Nat.succ_pos k⟩ Z') :
    letI := T.topology
    Embeds T Z ((T.binaryNormalizedProductFunctor Δ.rank ((k + 1) * Δ.rank)).obj (A.obj, Z')) := by
  let := T.topology
  have hX := (T.isSegmentSocle_iff Δ Z A hA).mp hZ
  have hA₁ := SegmentHeadSupport.isRepresentedBy_twistRep T ((1 : ℕ) : ℝ) hA
  have hX' := (T.isSegmentSocle_iff ⟨Δ.base.twist ((1 : ℕ) : ℝ), k + 1, Nat.succ_pos k⟩ Z'
    (SegmentHeadSupport.twistRep T ((1 : ℕ) : ℝ) A) hA₁).mp hZ'
  obtain ⟨e⟩ := SegmentHeadSupport.nonempty_iso_segmentInduced_split T Δ.rank_pos hm A.obj
  obtain ⟨-, j', hj', -⟩ := hX'
  let L := SmoothRep.universeLift.{uF} (T.segmentFactor A.obj ((0 : ℕ) : ℝ))
  let R := T.segmentInduced (T.segmentFactor A.obj ((1 : ℕ) : ℝ)) (k + 1) Δ.rank_pos
  let iZ' : Z' ⟶ R := SmoothRep.ofHom j'
  let σ := (T.binaryNormalizedProductFunctor Δ.rank ((k + 1) * Δ.rank)).obj (L, Z')
  let g : (L, Z') ⟶ (L, R) := (𝟙 L, iZ')
  have hg : Function.Injective (SmoothRep.hom
      ((T.binaryNormalizedProductFunctor Δ.rank ((k + 1) * Δ.rank)).map g)) :=
    T.binaryProductMap_injective g (fun _ _ h => h) hj'
  have hLi : L.IsIrreducible := by
    obtain ⟨h, ⟨e₀⟩⟩ := castIso_universeLift_segmentFactor_zero A.obj
    have e₁ : L ≅ A.obj := e₀
    exact (Weil.IsomorphismInvariance.irreducible_iff (SmoothRep.equivOfIso e₁)).mpr A.property.1
  have hZ'i : Z'.IsIrreducible := Aubert.SegmentProductClass.isIrreducible_of_isSegmentSocle F T hZ'
  have : Nontrivial L :=
    Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_of_isIrreducible _ hLi
  have : Nontrivial Z' :=
    Derivative.OrderedCuspidalProductNondegeneracy.nontrivial_of_isIrreducible _ hZ'i
  have : Nontrivial σ := Derivative.ProductVanishing.nontrivial_binary T (L, Z')
  have hσf : σ.HasFiniteLength :=
    Aubert.binaryProduct_preservesFiniteLength F T _ _ L Z'
      (SmoothRep.hasFiniteLength_of_isIrreducible hLi)
      (SmoothRep.hasFiniteLength_of_isIrreducible hZ'i)
  have hσf' := hasFiniteLength_rankCast'
    (SegmentHeadSupport.uniform_split_rank hm) hσf
  have : Nontrivial ((Derivative.generalLinearRankCast T
      (SegmentHeadSupport.uniform_split_rank hm)).obj σ) := rankCast_nontrivial _ σ
  let i := (Derivative.generalLinearRankCast T (SegmentHeadSupport.uniform_split_rank hm)).map
      ((T.binaryNormalizedProductFunctor Δ.rank ((k + 1) * Δ.rank)).map g) ≫ e.inv
  have hi : Function.Injective (SmoothRep.hom i) := by
    have h1 := rankCast_map_injective (SegmentHeadSupport.uniform_split_rank hm) _ hg
    have h2 : Function.Injective (SmoothRep.hom e.inv) := SmoothRep.hom_hom_injective e.symm
    exact fun u v huv => h1 (h2 huv)
  obtain ⟨jZ, hjZ⟩ := hX.finiteLengthSubobjectEmbedding hσf' (SmoothRep.hom i) hi
  have hemb : Embeds T Z σ :=
    embeds_of_isSubrepresentation_rankCast (SegmentHeadSupport.uniform_split_rank hm)
      ⟨SmoothRep.ofHom jZ, hjZ⟩
  exact hemb.castIso_right
    ((castIso_universeLift_segmentFactor_zero A.obj).binary (CastIso.refl Z'))

end Langlands.MoeglinWaldspurger.Derivation
