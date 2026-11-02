import Langlands.Representation.Classification.LinkedSegmentOverlapAssembly
import Langlands.Representation.Classification.LinkedSegmentJuxtaposedCase
import Langlands.Representation.Geometric.IdentityCellQuotientStatement

/-!
# The overlapping case of Zelevinsky's Proposition 4.6, step (2)

For `Δ' = init ∪ term` overlapping `Δ`, with `init` juxtaposed with `Δ` and
preceding it, the identity-cell quotient (Ze80 1.3), the two-block Jacquet module
of the socle of `Δ'` (Ze80 3.4) and the juxtaposed case (step (1)) give a nonzero
intertwiner `⟨Δ⟩ × ⟨Δ'⟩ → ⟨Δ ∪ init⟩ × ⟨term⟩`.
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.Classification.QuotientHom

open GeneralLinear Geometric CategoryTheory PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A segment socle is irreducible. -/
theorem isIrreducible_of_isSegmentSocle {Δ : Segment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentSocle Δ π) :
    letI := T.topology
    Representation.IsIrreducible π.representation := by
  obtain ⟨_, _, h⟩ := h
  exact h.1

/-- Two segment socles of the same segment are equivalent. -/
theorem nonempty_socleEquiv {Δ : Segment.{uV, uF} T}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentSocle Δ π) (h' : T.IsSegmentSocle Δ π') :
    letI := T.topology
    Nonempty (π.representation.Equiv π'.representation) := by
  let := T.topology
  exact ⟨SmoothRep.equivOfIso
    (h.nonempty_iso_segmentSocle.some ≪≫ h'.nonempty_iso_segmentSocle.some.symm)⟩

/-- Precomposing a nonzero intertwiner with a surjective one keeps it nonzero. -/
theorem comp_ne_zero_of_surjective {G U V W : Type*} [Monoid G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G U} {σ : Representation ℂ G V} {τ : Representation ℂ G W}
    {f : σ.IntertwiningMap τ} (hf : f ≠ 0) (g : ρ.IntertwiningMap σ)
    (hg : Function.Surjective g) : f.comp g ≠ 0 := by
  intro h
  apply hf
  ext v
  obtain ⟨u, rfl⟩ := hg v
  have := congrArg (fun k : ρ.IntertwiningMap τ => k u) h
  simpa using this

/-- Step (1), as a surjection: for juxtaposed `Δ' ≺ Δ` with union `U`, the product
of socles of `Δ` and `Δ'` maps onto the product of any socle datum of `U`. -/
theorem exists_surjective_of_juxtaposed
    (h1 : JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T)
    {m : ℕ} (d : T.SegmentProductDatum.{uV, uF} m) (h₂ : d.length = 2)
    (hd : d.HasSegmentSocles)
    (hp : (d.segments ⟨1, by omega⟩).Precedes (d.segments ⟨0, by omega⟩))
    (hjux : (d.segments ⟨1, by omega⟩).IsJuxtaposed (d.segments ⟨0, by omega⟩))
    (U : T.Segment.{uV, uF}) (e : T.SegmentProductDatum.{uV, uF} m)
    (hs : (d.segments ⟨0, by omega⟩).IsUnionIntersectionReplacement
      (d.segments ⟨1, by omega⟩) U none)
    (he : List.ofFn e.segments = [U]) (he' : e.HasSegmentSocles) :
    letI := T.topology
    ∃ f : d.induced.representation.IntertwiningMap e.induced.representation,
      Function.Surjective f := by
  let := T.topology
  obtain ⟨U₀, I₀, e₀, hs₀, he₀, he₀', -, s, -, ⟨φ⟩, -, -⟩ := h1 m d h₂ hd hp hjux
  obtain ⟨rfl, rfl⟩ :=
    replacement_eq_of_inter_empty (cuspidalIntegralTwistFreeness F T) hs₀ hs
  obtain ⟨ι⟩ := nonempty_induced_iso_of_segments_eq e₀ e (he₀.trans he.symm) he₀' he'
  let g : d.induced.representation.IntertwiningMap (s.gradedRepresentation 1).ρ :=
    (s.gradedProjection 1).hom.comp (toTopStep s)
  have hg : Function.Surjective g :=
    (s.gradedProjection_surjective 1).comp (toTopStep_surjective s)
  exact ⟨((SmoothRep.equivOfIso ι).toIntertwiningMap.comp φ.toIntertwiningMap).comp g,
    comp_surjective _ _ (comp_surjective _ _ (equiv_surjective _) (equiv_surjective φ)) hg⟩

/-- The datum with the single segment `U` and the single block `E₀`. -/
def singleDatum (U : T.Segment.{uV, uF})
    (E₀ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear U.degree F.Carrier)) :
    T.SegmentProductDatum.{uV, uF} U.degree :=
  ⟨1, fun _ => U, by simp, fun _ => E₀⟩

theorem singleDatum_segments (U : T.Segment.{uV, uF})
    (E₀ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear U.degree F.Carrier)) :
    List.ofFn (singleDatum U E₀).segments = [U] := by
  simp [singleDatum, List.ofFn_succ]

/-- The product of a single block is that block. -/
theorem nonempty_singleDatumEquiv (U : T.Segment.{uV, uF})
    (E₀ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear U.degree F.Carrier)) :
    letI := T.topology
    Nonempty ((singleDatum U E₀).induced.representation.Equiv E₀.representation) := by
  let := T.topology
  let g₁ := T.singleBlockNormalizedProductEquiv (singleDatum U E₀).shape rfl
    (fun _ => E₀.representation) (fun _ => E₀.isSmooth) ⟨0, Nat.one_pos⟩
  exact ⟨g₁.trans (equivOfApplyEq _ E₀.representation fun g =>
    congrArg E₀.representation (reindex_finCongr_symm_self rfl g))⟩

/-- Normalized induction from a shape equal to `B`, of a factor equal to the external
tensor product of `τ`, is the normalized product induced from `τ`. -/
theorem nonempty_parabolicInducedEquivOfEq {m : ℕ} (B B' : BlockShape m) (hB : B' = B)
    (τ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (B'.Levi F.Carrier))
    (hσ : letI := T.topology
      HEq σ (FiniteTensor.externalSmoothObject τ :
        SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier))) :
    letI := T.topology
    Nonempty (Representation.Equiv (T.normalizedParabolicInduced B' σ.representation)
      ((T.normalizedProductInductionFunctor B).obj τ).representation) := by
  let := T.topology
  subst hB
  obtain rfl := eq_of_heq hσ
  exact ⟨Representation.Equiv.refl _⟩

variable {n : ℕ}

namespace OverlapConfig

variable (O : OverlapConfig.{uF, uV} T n)

set_option maxHeartbeats 1000000 in
/-- The two-block Jacquet module of the socle of `Δ'` given by Ze80 3.4, as an
equivalence onto the tensor product of the two factors pulled back to the
coordinate projections. -/
theorem nonempty_splitEquiv
    (A₁ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (O.B.size ⟨1, Nat.one_lt_two⟩) F.Carrier))
    (π₁ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear O.init.degree F.Carrier))
    (π₂ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear O.term.degree F.Carrier))
    (ι : letI := T.topology
      (T.normalizedJacquetFunctor (O.Δ'.socleSplitShape O.q O.hq O.hqm)).obj A₁ ≅
        FiniteTensor.externalFunctor.obj (O.Δ'.socleSplitFactors O.q O.hq O.hqm π₁ π₂)) :
    letI := T.topology
    Nonempty ((T.normalizedJacquet (O.S ⟨1, Nat.one_lt_two⟩) A₁.obj.ρ).Equiv
      (Representation.tprod
        (π₁.representation.comp (Pi.evalMonoidHom
          (fun j => GeneralLinear ((O.S ⟨1, Nat.one_lt_two⟩).size j) F.Carrier)
            ⟨0, Nat.zero_lt_two⟩))
        (π₂.representation.comp (Pi.evalMonoidHom
          (fun j => GeneralLinear ((O.S ⟨1, Nat.one_lt_two⟩).size j) F.Carrier)
            ⟨1, Nat.one_lt_two⟩)))) := by
  let := T.topology
  let S' := O.Δ'.socleSplitShape O.q O.hq O.hqm
  let X := O.Δ'.socleSplitFactors O.q O.hq O.hqm π₁ π₂
  let e₀ : Representation.Equiv (T.normalizedJacquet S' A₁.obj.ρ)
      (FiniteTensor.external fun j => (X j).representation) :=
    SmoothRep.equivOfIso ι
  let e₁ := externalTwoEquiv (H := fun j : Fin 2 => GeneralLinear (S'.size j) F.Carrier)
    (fun j => (X j).representation)
  exact ⟨e₀.trans e₁⟩

set_option maxHeartbeats 1000000 in
/-- The union block of the target identity piece is the product of the union
blocks `A₀ × π₁`. -/
theorem nonempty_unionBlockEquiv
    (A₀ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear O.Δ.degree F.Carrier))
    (π₁ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear O.init.degree F.Carrier))
    (π₂ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear O.term.degree F.Carrier)) :
    letI := T.topology
    Nonempty (Representation.Equiv
      (Parabolic.RefinedInductionTensor.blockRepresentations F T O.C O.R
        (O.targetFactors A₀ π₁ π₂) (0 : Fin 2))
      ((T.normalizedProductInductionFunctor O.unionShape).obj
        (O.unionBlocks A₀ π₁)).representation) :=
  nonempty_parabolicInducedEquivOfEq (T := T) O.unionShape (O.R (0 : Fin 2))
    rfl (O.unionBlocks A₀ π₁) (O.targetFactors A₀ π₁ π₂ (0 : Fin 2)) HEq.rfl

/-- Step (1) on `(Δ, init)`: the product of the union blocks `A₀ × π₁` maps onto
the product of the single block `E₀`. -/
theorem exists_unionProductSurjection
    (h1 : JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T)
    (hpre : O.init.Precedes O.Δ) (hjux : O.init.IsJuxtaposed O.Δ)
    (hrep : O.Δ.IsUnionIntersectionReplacement O.init O.U none)
    (A₀ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear O.Δ.degree F.Carrier))
    (π₁ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear O.init.degree F.Carrier))
    (hA₀ : T.IsSegmentSocle O.Δ A₀) (hπ₁ : T.IsSegmentSocle O.init π₁)
    (E₀ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear O.U.degree F.Carrier))
    (hE₀ : T.IsSegmentSocle O.U E₀) :
    letI := T.topology
    ∃ f : ((T.normalizedProductInductionFunctor O.unionShape).obj
        (O.unionBlocks A₀ π₁)).representation.IntertwiningMap
        (singleDatum O.U E₀).induced.representation,
      Function.Surjective f := by
  let := T.topology
  let d' : T.SegmentProductDatum.{uV, uF} O.U.degree :=
    ⟨2, ![O.Δ, O.init], O.hU, O.unionBlocks A₀ π₁⟩
  have hd' : d'.HasSegmentSocles := Fin.forall_fin_two.mpr ⟨hA₀, hπ₁⟩
  exact exists_surjective_of_juxtaposed h1 d' rfl hd' hpre hjux O.U
    (singleDatum O.U E₀) hrep (singleDatum_segments O.U E₀) (fun _ => hE₀)

set_option maxHeartbeats 1000000 in
/-- Step (1) on `(Δ, init)`: the product of the union blocks `A₀ × π₁` maps onto
any socle of `U`. -/
theorem exists_unionSurjection
    (h1 : JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T)
    (hpre : O.init.Precedes O.Δ) (hjux : O.init.IsJuxtaposed O.Δ)
    (hrep : O.Δ.IsUnionIntersectionReplacement O.init O.U none)
    (A₀ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear O.Δ.degree F.Carrier))
    (π₁ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear O.init.degree F.Carrier))
    (π₂ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear O.term.degree F.Carrier))
    (hA₀ : T.IsSegmentSocle O.Δ A₀) (hπ₁ : T.IsSegmentSocle O.init π₁)
    (E₀ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear O.U.degree F.Carrier))
    (hE₀ : T.IsSegmentSocle O.U E₀) :
    letI := T.topology
    ∃ f : (Parabolic.RefinedInductionTensor.blockRepresentations F T O.C O.R
        (O.targetFactors A₀ π₁ π₂) (0 : Fin 2)).IntertwiningMap E₀.representation,
      Function.Surjective f := by
  let := T.topology
  obtain ⟨k⟩ := O.nonempty_unionBlockEquiv A₀ π₁ π₂
  obtain ⟨f, hf⟩ := O.exists_unionProductSurjection h1 hpre hjux hrep A₀ π₁ hA₀ hπ₁ E₀ hE₀
  obtain ⟨g⟩ := nonempty_singleDatumEquiv O.U E₀
  exact ⟨(g.toIntertwiningMap.comp f).comp k.toIntertwiningMap,
    comp_surjective _ _ (comp_surjective _ _ (equiv_surjective g) hf) (equiv_surjective k)⟩

theorem n_pos (O : OverlapConfig.{uF, uV} T n) : 0 < n := by
  have := O.degree_n
  have := O.Δ.degree_pos
  omega

/-- The overlapping case for the configuration `O`, from the identity-cell quotient,
Ze80 3.4 and step (1): a nonzero intertwiner from the product of socles of `Δ`
and `Δ'` to the product of socles of `U` and `term`. -/
theorem exists_ne_zero
    (h1 : JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T)
    (h34 : SegmentSocleJacquetFormula.{uF, uV} F T)
    (h13 : Geometric.PadicIdentityCellQuotientTheorem.{uF, max uF uV})
    (hpre : O.init.Precedes O.Δ) (hjux : O.init.IsJuxtaposed O.Δ)
    (hrep : O.Δ.IsUnionIntersectionReplacement O.init O.U none)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (O.B.size i) F.Carrier))
    (hA₀ : T.IsSegmentSocle O.Δ (A ⟨0, Nat.zero_lt_two⟩))
    (hA₁ : T.IsSegmentSocle O.Δ' (A ⟨1, Nat.one_lt_two⟩))
    (E : letI := T.topology
      ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (O.C.size j) F.Carrier))
    (hE₀ : T.IsSegmentSocle O.U (E (0 : Fin 2)))
    (hE₁ : T.IsSegmentSocle O.term (E (1 : Fin 2))) :
    letI := T.topology
    ∃ f : ((T.normalizedProductInductionFunctor O.B).obj A).representation.IntertwiningMap
        ((T.normalizedProductInductionFunctor O.C).obj E).representation, f ≠ 0 := by
  let := T.topology
  obtain ⟨-, h34'⟩ := h34 O.Δ' (A ⟨1, Nat.one_lt_two⟩) hA₁
  obtain ⟨π₁, π₂, hπ₁, hπ₂, ⟨ι⟩⟩ := h34' O.q O.hq O.hqm
  obtain ⟨E₁⟩ := O.nonempty_splitEquiv (A ⟨1, Nat.one_lt_two⟩) π₁ π₂ ι
  obtain ⟨η, hη⟩ := h13 p F T n O.n_pos O.B O.C O.S O.R O.hS O.hR
  obtain ⟨f₀, hf₀⟩ := O.exists_unionSurjection h1 hpre hjux hrep (A ⟨0, Nat.zero_lt_two⟩)
    π₁ π₂ hA₀ hπ₁ (E (0 : Fin 2)) hE₀
  obtain ⟨f₁⟩ := nonempty_socleEquiv hπ₂ hE₁
  exact O.exists_ne_zero_of_identityPiece A π₁ π₂ E₁ E η (hη _) f₀ hf₀ f₁.toIntertwiningMap
    (equiv_surjective f₁) (isIrreducible_of_isSegmentSocle hE₀)
    (isIrreducible_of_isSegmentSocle hE₁)

end OverlapConfig

/-- The overlapping case of Ze80 4.6 step (2), for a split `Δ' = init ∪ term` with
`term = J`, `init` juxtaposed with `Δ` and preceding it, and `U = Δ ∪ init`. -/
theorem exists_ne_zero_of_overlap
    (h1 : JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T)
    (h34 : SegmentSocleJacquetFormula.{uF, uV} F T)
    (h13 : Geometric.PadicIdentityCellQuotientTheorem.{uF, max uF uV})
    (d : T.SegmentProductDatum.{uV, uF} n) (h₂ : d.length = 2)
    (hd : d.HasSegmentSocles) (U J : Segment.{uV, uF} T)
    (e : T.SegmentProductDatum.{uV, uF} n)
    (q : ℕ) (hq : 0 < q) (hqm : q < (d.segments ⟨1, by omega⟩).length)
    (hJ : (d.segments ⟨1, by omega⟩).terminal q hqm = J)
    (hpre : ((d.segments ⟨1, by omega⟩).initial q hq).Precedes (d.segments ⟨0, by omega⟩))
    (hjux : ((d.segments ⟨1, by omega⟩).initial q hq).IsJuxtaposed
      (d.segments ⟨0, by omega⟩))
    (hrep : (d.segments ⟨0, by omega⟩).IsUnionIntersectionReplacement
      ((d.segments ⟨1, by omega⟩).initial q hq) U none)
    (hdeg : U.degree = (d.segments ⟨0, by omega⟩).degree +
      ((d.segments ⟨1, by omega⟩).initial q hq).degree)
    (he : List.ofFn e.segments = [U, J]) (he' : e.HasSegmentSocles) :
    letI := T.topology
    ∃ f : d.induced.representation.IntertwiningMap e.induced.representation, f ≠ 0 := by
  let := T.topology
  obtain ⟨l, segs, hsum, blocks⟩ := d
  obtain rfl : l = 2 := h₂
  obtain ⟨l', segs', hsum', E⟩ := e
  have hl' : l' = 2 := by simpa using congrArg List.length he
  subst hl'
  have hsegs' : segs' = ![U, J] := List.ofFn_injective (he.trans (by simp))
  subst hsegs'
  subst hJ
  let O : OverlapConfig.{uF, uV} T n :=
    { Δ := segs ⟨0, Nat.zero_lt_two⟩
      Δ' := segs ⟨1, Nat.one_lt_two⟩
      U := U
      q := q
      hq := hq
      hqm := hqm
      hn := by
        rw [Fin.sum_univ_two] at hsum ⊢
        exact hsum
      hU := by
        rw [Fin.sum_univ_two]
        exact hdeg.symm }
  let A : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (O.B.size i) F.Carrier) :=
    Fin.cons (α := fun i : Fin 2 =>
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (O.B.size i) F.Carrier))
      (blocks ⟨0, Nat.zero_lt_two⟩)
      (Fin.cons (α := fun i : Fin 1 =>
          SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (O.B.size i.succ) F.Carrier))
        (blocks ⟨1, Nat.one_lt_two⟩) finZeroElim)
  let d₂ : T.SegmentProductDatum.{uV, uF} n := ⟨2, ![O.Δ, O.Δ'], O.hn, A⟩
  have hd₂ : d₂.HasSegmentSocles := Fin.forall_fin_two.mpr ⟨hd 0, hd 1⟩
  obtain ⟨ι⟩ := nonempty_induced_iso_of_segments_eq ⟨2, segs, hsum, blocks⟩ d₂
    (congrArg List.ofFn (funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩))) hd hd₂
  obtain ⟨f, hf⟩ := O.exists_ne_zero h1 h34 h13 hpre hjux hrep A (hd 0) (hd 1) E
    (he' 0) (he' 1)
  exact ⟨f.comp (SmoothRep.equivOfIso ι).toIntertwiningMap,
    comp_ne_zero_of_surjective hf _ (equiv_surjective (SmoothRep.equivOfIso ι))⟩

end Langlands.Classification.QuotientHom
