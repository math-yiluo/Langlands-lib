import Langlands.Representation.Classification.SegmentProductCuspidalMembers
import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Derivative.Homogeneity
import Langlands.Representation.Parabolic.InducedMapSurjectivity
import Langlands.Representation.Tensor.ExternalMapSurjectivityProof
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Classification.SegmentCuspidalContent
import Langlands.Representation.Classification.IrreducibleProductEmbedding
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Representation.Category.Subquotients

/-!
# Segment-socle products inside cuspidal products

A product of segment socles `⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` embeds in an actual product of
supercuspidal representatives of all members of all `Δ_i`, in their order.
We record this as the predicate `EmbedsCuspidal X S`: `X` injects into a
supercuspidal product whose list of cuspidal data has multiset `S`. The
predicate passes to subrepresentations and rank casts, gives a supercuspidal
support to every irreducible `X`, and a nonzero `X` with it has an irreducible
subrepresentation (finite length of the supercuspidal product).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.SegmentProductCuspidalEmbedding

open GeneralLinear Geometric PadicField.TopologicalData Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ## Embeddings in supercuspidal products -/

/-- `X` injects into an actual product of supercuspidal representatives of
cuspidal data whose multiset is `S`. -/
def EmbedsCuspidal {n : ℕ}
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (S : Multiset (CuspidalDatum.{uV, uF} T)) : Prop :=
  letI := T.topology
  ∃ (k : ℕ) (ρ : Fin k → CuspidalDatum.{uV, uF} T) (h : ∑ i, (ρ i).rank = n)
    (A : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)),
    (∀ i, (ρ i).IsRepresentedBy (A i)) ∧
      (List.ofFn ρ : Multiset (CuspidalDatum.{uV, uF} T)) = S ∧
      ∃ f : X ⟶ T.cuspidalProductInduced ρ h A, Function.Injective (SmoothRep.hom f)

variable {T}

theorem EmbedsCuspidal.of_injective {n : ℕ}
    {X Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {S : Multiset (CuspidalDatum.{uV, uF} T)} (hX : EmbedsCuspidal T X S)
    (g : letI := T.topology; Y ⟶ X) (hg : letI := T.topology; Function.Injective (SmoothRep.hom g)) :
    EmbedsCuspidal T Y S := by
  obtain ⟨k, ρ, h, A, hA, hρ, f, hf⟩ := hX
  exact ⟨k, ρ, h, A, hA, hρ, g ≫ f, hf.comp hg⟩

theorem EmbedsCuspidal.of_iso {n : ℕ}
    {X Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {S : Multiset (CuspidalDatum.{uV, uF} T)} (hX : EmbedsCuspidal T X S) (e : Y ≅ X) :
    EmbedsCuspidal T Y S := by
  let := T.topology
  exact hX.of_injective e.hom (SmoothRep.hom_hom_injective e)

theorem EmbedsCuspidal.rankCast {a b : ℕ} (hab : a = b)
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    {S : Multiset (CuspidalDatum.{uV, uF} T)} (hX : EmbedsCuspidal T X S) :
    EmbedsCuspidal T ((generalLinearRankCast T hab).obj X) S := by
  subst hab
  exact hX

/-- Blockwise injective intertwiners induce an injective intertwiner. -/
theorem normalizedProductInducedMap_injective {n : ℕ} (B : BlockShape n)
    {A A' : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    (f : letI := T.topology
      ∀ i, (A i).representation.IntertwiningMap (A' i).representation)
    (hf : ∀ i, Function.Injective (f i)) :
    letI := T.topology
    Function.Injective (T.normalizedProductInducedMap B f) :=
  T.normalizedParabolicInducedMap_injective B (FiniteTensor.externalMap f)
    (FiniteTensor.externalMap_injective f hf)

/-- A product of segment socles embeds in the supercuspidal product of all
members of its segments. -/
theorem embedsCuspidal_induced {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)
    (hd : d.HasSegmentSocles) :
    EmbedsCuspidal T d.induced d.multisegment.cuspidalContent := by
  let := T.topology
  choose A hA hsoc using hd
  obtain ⟨e⟩ := memberInducedIso d A
  refine ⟨_, memberFamily d, memberFamily_sum d, memberRepresentatives d A,
    memberRepresentatives_represent d A hA, memberFamily_content d, ?_⟩
  let ι : ∀ j, (d.blocks j).representation.IntertwiningMap
      (T.segmentInduced (A j).obj (d.segments j).length (d.segments j).rank_pos).representation :=
    fun j => (hsoc j).2.choose
  have hι : ∀ j, Function.Injective (ι j) := fun j => (hsoc j).2.choose_spec.1
  let J : d.induced ⟶ (T.normalizedProductInductionFunctor d.shape).obj
      (fun j => T.segmentInduced (A j).obj (d.segments j).length (d.segments j).rank_pos) :=
    SmoothRep.ofHom (T.normalizedProductInducedMap d.shape ι)
  refine ⟨J ≫ e.inv, ?_⟩
  exact (SmoothRep.hom_hom_injective e.symm).comp
    (normalizedProductInducedMap_injective d.shape ι hι)

/-- An irreducible representation with such an embedding has the multiset as a
supercuspidal support. -/
theorem EmbedsCuspidal.isSupercuspidalSupport {n : ℕ}
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {S : Multiset (CuspidalDatum.{uV, uF} T)} (hX : EmbedsCuspidal T X S)
    (hirr : letI := T.topology; X.IsIrreducible) : T.IsSupercuspidalSupport X S := by
  let := T.topology
  obtain ⟨k, ρ, h, A, hA, hρ, f, hf⟩ := hX
  exact ⟨k, ρ, hρ, IsCuspidalSubrepresentation.isCuspidalConstituent
    ⟨h, A, hA, hirr, SmoothRep.hom f, hf⟩⟩

/-- A nonzero representation of positive rank with such an embedding has an
irreducible subrepresentation, which inherits the embedding. -/
theorem EmbedsCuspidal.exists_irreducible {n : ℕ} (hn : 0 < n)
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {S : Multiset (CuspidalDatum.{uV, uF} T)} (hX : EmbedsCuspidal T X S) [Nontrivial X] :
    letI := T.topology
    ∃ σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      IsIrreducibleSubrepresentation X.representation σ.representation ∧
        EmbedsCuspidal T σ S := by
  let := T.topology
  obtain ⟨k, ρ, h, A, hA, hρ, f, hf⟩ := hX
  have hfin := irreducibleProductFiniteLength.{uF, uV} F T n hn (T.cuspidalShape ρ h)
    (fun i => (A i).obj) (fun i => (A i).property.1)
  have hXfin : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      X.representation.asModule :=
    hfin.of_injective
      (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom f)) hf
  have : IsArtinian (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) X.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hXfin).2
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := X.representation)
  have : IsAtomic (Subrepresentation X.representation) := e.isAtomic_iff.mpr inferInstance
  have hbt : (⊥ : Subrepresentation X.representation) ≠ ⊤ := by
    obtain ⟨v, hv⟩ := exists_ne (0 : X)
    intro hb
    apply hv
    have hmem : v ∈ (⊤ : Subrepresentation X.representation).toSubmodule := Submodule.mem_top
    rw [← hb] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  obtain ⟨U, hU, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation X.representation)).resolve_left
    hbt.symm
  have hirr : (SmoothRep.subrepresentation X U).IsIrreducible :=
    FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom U hU
  refine ⟨SmoothRep.subrepresentation X U,
    ⟨hirr, SmoothRep.hom (SmoothRep.subtype X U), SmoothRep.subtype_injective X U⟩, ?_⟩
  exact EmbedsCuspidal.of_injective (T := T) (S := S) ⟨k, ρ, h, A, hA, hρ, f, hf⟩ _
    (SmoothRep.subtype_injective X U)

end Langlands.Classification.SegmentProductCuspidalEmbedding
