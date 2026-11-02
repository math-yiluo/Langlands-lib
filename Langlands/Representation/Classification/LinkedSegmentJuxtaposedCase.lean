import Langlands.Representation.Classification.LinkedSegmentSocleReverseProductStepsStatement
import Langlands.Representation.Classification.LanglandsQuotients
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof

/-!
# The juxtaposed case of Zelevinsky's Proposition 4.6, step (2)

If `Δ'` precedes `Δ` with empty intersection, step (1) gives a filtration of
`⟨Δ⟩ × ⟨Δ'⟩` whose top quotient is a socle product of the union, hence a nonzero
intertwiner onto any socle product of the union.
-/

noncomputable section

namespace Langlands.Classification.QuotientHom

open CategoryTheory PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Data with the same segment list and segment-socle blocks have isomorphic
products. -/
theorem nonempty_induced_iso_of_segments_eq {n : ℕ}
    (d e : T.SegmentProductDatum.{uV, uF} n)
    (hs : List.ofFn d.segments = List.ofFn e.segments)
    (hd : d.HasSegmentSocles) (he : e.HasSegmentSocles) :
    letI := T.topology
    Nonempty (d.induced ≅ e.induced) := by
  let := T.topology
  obtain ⟨l, Δ, h, A⟩ := d
  obtain ⟨l', Δ', h', A'⟩ := e
  have hl : l = l' := by simpa using congrArg List.length hs
  subst hl
  have hΔ : Δ = Δ' := List.ofFn_injective hs
  subst hΔ
  have hi : ∀ i, Nonempty (A i ≅ A' i) := fun i =>
    ⟨(hd i).nonempty_iso_segmentSocle.some ≪≫ (he i).nonempty_iso_segmentSocle.some.symm⟩
  exact ⟨(T.normalizedProductInductionFunctor _).mapIso (Pi.isoMk fun i => (hi i).some)⟩

/-- If a pair admits a replacement with empty intersection, then under integral
twist freeness every replacement of the pair has the same union and no
intersection segment. -/
theorem replacement_eq_of_inter_empty
    (hfree : CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ U₀ U : T.Segment.{uV, uF}} {I₀ : Option T.Segment.{uV, uF}}
    (h₀ : Δ.IsUnionIntersectionReplacement Γ U₀ I₀)
    (h : Δ.IsUnionIntersectionReplacement Γ U none) :
    U₀ = U ∧ I₀ = none := by
  refine ⟨Segment.eq_of_support_eq hfree (h₀.1.trans h.1.symm), ?_⟩
  cases I₀ with
  | none => rfl
  | some J =>
    have hJ : J.support = Δ.support ∩ Γ.support := h₀.2
    have hE : Δ.support ∩ Γ.support = ∅ := h.2
    have hbase := J.base_mem_support
    rw [hJ, hE] at hbase
    simp at hbase

/-- A surjective intertwiner onto an irreducible representation is nonzero. -/
theorem IntertwiningMap.ne_zero_of_surjective {G V W : Type*} [Monoid G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hσ : Representation.IsIrreducible σ) (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) : f ≠ 0 := by
  intro h0
  apply hσ.bot_ne_top
  refine le_antisymm bot_le fun w _ => ?_
  obtain ⟨v, rfl⟩ := hf w
  rw [h0]
  change (0 : W) ∈ (⊥ : Submodule ℂ W)
  exact zero_mem _

/-- Composing with an injective intertwiner preserves nonvanishing. -/
theorem IntertwiningMap.comp_ne_zero {G U V W : Type*} [Monoid G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G U} {σ : Representation ℂ G V} {τ : Representation ℂ G W}
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f)
    {g : ρ.IntertwiningMap σ} (hg : g ≠ 0) : f.comp g ≠ 0 := by
  intro h
  apply hg
  ext v
  apply hf
  have := congrArg (fun k : ρ.IntertwiningMap τ => k v) h
  simpa using this

/-- The identity of a representation onto the top step of a filtration. -/
def toTopStep {G : Type*} [Monoid G] {A : Rep.{uV} ℂ G} {m : ℕ}
    (s : ObjectRepFiltration A m) :
    A.ρ.IntertwiningMap (s.subrepresentation (Fin.last m)).toRepresentation :=
  (LinearMap.codRestrict (s.subrepresentation (Fin.last m)).toSubmodule LinearMap.id
      fun v => by
        change v ∈ s.subrepresentation (Fin.last m)
        rw [s.subrepresentation_last]
        trivial).intertwiningMap_of_isIntertwiningMap _ _ fun _ _ => rfl

theorem toTopStep_surjective {G : Type*} [Monoid G] {A : Rep.{uV} ℂ G} {m : ℕ}
    (s : ObjectRepFiltration A m) : Function.Surjective (toTopStep s) :=
  fun w => ⟨w.1, rfl⟩

/-- Juxtaposed case, conditional on step (1): the quotient `π/ω₀` of the
filtration supplied by step (1) is equivalent to the union socle, and any
other socle datum of the same union is isomorphic to it. -/
theorem exists_ne_zero_of_juxtaposed
    (h1 : JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T)
    {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n) (h₂ : d.length = 2)
    (hd : d.HasSegmentSocles)
    (hp : (d.segments ⟨1, by omega⟩).Precedes (d.segments ⟨0, by omega⟩))
    (U : T.Segment.{uV, uF}) (e : T.SegmentProductDatum.{uV, uF} n)
    (hs : (d.segments ⟨0, by omega⟩).IsUnionIntersectionReplacement
      (d.segments ⟨1, by omega⟩) U none)
    (he : List.ofFn e.segments = [U]) (he' : e.HasSegmentSocles) :
    letI := T.topology
    ∃ f : d.induced.representation.IntertwiningMap e.induced.representation, f ≠ 0 := by
  let := T.topology
  have hjux : (d.segments ⟨1, by omega⟩).IsJuxtaposed (d.segments ⟨0, by omega⟩) :=
    ⟨hp.isLinked, Set.disjoint_iff_inter_eq_empty.mpr ((Set.inter_comm _ _).trans hs.2)⟩
  obtain ⟨U₀, I₀, e₀, hs₀, he₀, he₀', -, s, hsimple, ⟨φ⟩, -, -⟩ :=
    h1 n d h₂ hd hp hjux
  obtain ⟨rfl, rfl⟩ :=
    replacement_eq_of_inter_empty (cuspidalIntegralTwistFreeness F T) hs₀ hs
  obtain ⟨ι⟩ := nonempty_induced_iso_of_segments_eq e₀ e (he₀.trans he.symm) he₀' he'
  let g : d.induced.representation.IntertwiningMap (s.gradedRepresentation 1).ρ :=
    (s.gradedProjection 1).hom.comp (toTopStep s)
  have hg : Function.Surjective g :=
    (s.gradedProjection_surjective 1).comp (toTopStep_surjective s)
  let E := (SmoothRep.equivOfIso ι).toIntertwiningMap.comp φ.toIntertwiningMap
  have hE : Function.Injective E :=
    (SmoothRep.equivOfIso ι).toLinearEquiv.injective.comp φ.toLinearEquiv.injective
  exact ⟨E.comp g, IntertwiningMap.comp_ne_zero E hE
    (IntertwiningMap.ne_zero_of_surjective (hsimple 1) g hg)⟩

end Langlands.Classification.QuotientHom
