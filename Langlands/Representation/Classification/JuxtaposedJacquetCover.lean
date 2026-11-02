import Langlands.Representation.Classification.JuxtaposedInitialEmbedding
import Langlands.Representation.Classification.JuxtaposedJacquetImage
import Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation
import Langlands.Representation.CuspidalSupport.InducedJacquetCount
import Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionProof
import Langlands.Representation.Filtration.ConstituentSupportDefinitions

/-!
# Every non-identity shuffle factor occurs in every nonzero subrepresentation

Let `π = ⟨Δ₀⟩ × ⟨Δ₁⟩` with `Δ₀` beginning at `ν^l ρ` of length `q` and `Δ₁`
beginning at `ρ` of length `l`, and let `J` be the normalized Jacquet functor along
the uniform shape `(r, …, r)`. For every shuffle `S` other than the identity one,
`π` embeds into `i(τ_{S₀}) ≅ i(τ_S)`, so Frobenius evaluation gives a nonzero map
`J(X) → τ_S` for every nonzero subrepresentation `X` of `π`. Together with the shuffle
count of `J(π)`, which enters as a hypothesis, every composition factor of `J(π)` not
equivalent to the identity shuffle tensor is a composition factor of the image of
`J(X)` in `J(π)`.
-/

noncomputable section

open Representation CategoryTheory

namespace Langlands.Classification.JuxtaposedShuffle

open GeneralLinear PadicField.TopologicalData CuspidalSupport.JacquetLength

universe uF uV uW uT uK uG

/-- A composition factor in the support is irreducible. -/
theorem isIrreducible_of_mem_jordanHolderSupport {k : Type uK} [Field k] {G : Type uG}
    [Monoid G] {B : Rep.{uV} k G} {τ : Rep.{uT} k G}
    (h : τ ∈ (jordanHolderSupport B : Set (Rep.{uT} k G))) : IsIrreducible τ.ρ := by
  obtain ⟨m, ⟨n, s, hs, hm⟩, hpos⟩ := h
  unfold ObjectRepFiltration.factorMultiplicity at hm
  rw [← hm] at hpos
  obtain ⟨⟨i, ⟨e⟩⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  exact isIrreducible_of_equiv e (hs i)

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Frobenius evaluation through an embedding: if `π` embeds into `i_C(σ)` and
`i_C(σ) ≅ i_C(σ')`, every nonzero subrepresentation of `π` has a nonzero map from
its normalized Jacquet module to `⊗ᵢ σ'ᵢ`. -/
theorem exists_ne_zero_jacquet_hom_of_injective {n : ℕ} (C : BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GeneralLinear n F.Carrier) V}
    (σ σ' : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (C.size i) F.Carrier))
    (i : letI := T.topology
      π.IntertwiningMap ((T.normalizedProductInductionFunctor.{uF, uW} C).obj σ).representation)
    (hi : Function.Injective i)
    (e : letI := T.topology
      (T.normalizedProductInductionFunctor.{uF, uW} C).obj σ ≅
        (T.normalizedProductInductionFunctor.{uF, uW} C).obj σ')
    (X : Subrepresentation π) (hX : X ≠ ⊥) :
    letI := T.topology
    ∃ g : (T.normalizedJacquet C X.toRepresentation).IntertwiningMap
        (FiniteTensor.externalSmoothObject σ').representation, g ≠ 0 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let φ := SmoothRep.equivOfIso e
  let f : X.toRepresentation.IntertwiningMap
      (T.normalizedParabolicInduced C (FiniteTensor.externalSmoothObject σ').representation) :=
    φ.toIntertwiningMap.comp (i.comp (subtypeMap X))
  have hf : f ≠ 0 := by
    intro h
    apply hX
    apply Subrepresentation.toSubmodule_injective
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    have h1 : φ (i x) = 0 := DFunLike.congr_fun h ⟨x, hx⟩
    have h2 : i x = 0 := φ.injective (h1.trans (map_zero φ).symm)
    exact hi (h2.trans (map_zero i).symm)
  exact CuspidalSupport.exists_ne_zero_normalizedJacquet_hom
    (σ := (FiniteTensor.externalSmoothObject σ').representation) T C f hf

/-- If `g : J(X) → τ` is nonzero for an irreducible factor `τ` of `J(π)`, then `τ`
is a composition factor of the image of `J(X)` in `J(π)`. -/
theorem mem_jordanHolderSupport_jacquetImage {n : ℕ} (C : BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GeneralLinear n F.Carrier) V}
    (hπ : letI := T.topology; IsSmooth π) (τ : Rep.{uT} ℂ (C.Levi F.Carrier))
    (hτ : τ ∈ (jordanHolderSupport (Rep.of (T.normalizedJacquet C π)) :
      Set (Rep.{uT} ℂ (C.Levi F.Carrier))))
    (X : Subrepresentation π) (g : (T.normalizedJacquet C X.toRepresentation).IntertwiningMap τ.ρ)
    (hg : g ≠ 0) :
    τ ∈ (jordanHolderSupport (Rep.of (jacquetImage T C X).toRepresentation) :
      Set (Rep.{uT} ℂ (C.Levi F.Carrier))) := by
  have hirr := isIrreducible_of_mem_jordanHolderSupport hτ
  obtain ⟨M, hM, -⟩ := hτ
  let ψ := jacquetImageEquiv T C hπ X
  let g' : (jacquetImage T C X).toRepresentation.IntertwiningMap τ.ρ :=
    g.comp ψ.symm.toIntertwiningMap
  have hg' : g' ≠ 0 := by
    intro h
    apply hg
    refine DFunLike.ext _ _ fun x => ?_
    have := DFunLike.congr_fun h (ψ x)
    change g (ψ.symm (ψ x)) = 0 at this
    rw [ψ.symm_apply_apply] at this
    exact this
  let j : (jacquetImage T C X).toRepresentation.IntertwiningMap (T.normalizedJacquet C π) :=
    { toLinearMap := (jacquetImage T C X).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  obtain ⟨m, hm, hpos, -⟩ := jordanHolderSubobjectSimpleMapDetection ℂ (C.Levi F.Carrier)
    (Rep.of (T.normalizedJacquet C π)) (Rep.of (jacquetImage T C X).toRepresentation) τ hirr
    j (Submodule.injective_subtype _) M hM (Or.inr ⟨g', hg'⟩)
  exact ⟨m, hm, hpos⟩

/-- For a shuffle `S` other than the identity one, every nonzero subrepresentation
`X` of `⟨Δ₀⟩ × ⟨Δ₁⟩` has a nonzero map `J(X) → τ_S`, provided the two orders of
`ν^a A × ν^b A` are isomorphic whenever `b + 1 < a`. -/
theorem exists_ne_zero_jacquet_hom_shuffle (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (q l : ℕ)
    (d : T.SegmentProductDatum.{uV, uF} ((q + l) * ρ.rank)) (h₂ : d.length = 2)
    (hd : d.HasSegmentSocles)
    (hb₀ : (d.segments ⟨0, by omega⟩).base = ρ.twist l)
    (hl₀ : (d.segments ⟨0, by omega⟩).length = q)
    (hb₁ : (d.segments ⟨1, by omega⟩).base = ρ.twist 0)
    (hl₁ : (d.segments ⟨1, by omega⟩).length = l)
    (hswap : ∀ a b : ℕ, b + 1 < a → letI := T.topology
      Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 ρ.rank ρ.rank_pos)).obj
            ![T.segmentFactor A.obj (a : ℝ), T.segmentFactor A.obj (b : ℝ)] ≅
        (T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 ρ.rank ρ.rank_pos)).obj
            ![T.segmentFactor A.obj (b : ℝ), T.segmentFactor A.obj (a : ℝ)]))
    (S : Finset (Fin (q + l))) (hS : S.card = q) (hid : S ≠ idShuffle q l)
    (X : letI := T.topology; Subrepresentation d.induced.representation) (hX : X ≠ ⊥) :
    letI := T.topology
    ∃ g : (T.normalizedJacquet (BlockShape.uniform (q + l) ρ.rank ρ.rank_pos)
        X.toRepresentation).IntertwiningMap
          (FiniteTensor.externalSmoothObject
            (shuffleFactors F T A.obj (q + l) ρ.rank_pos S l 0)).representation, g ≠ 0 := by
  let := T.topology
  obtain ⟨i, hi⟩ := exists_injective_initShuffle T ρ A hA q l d h₂ hd hb₀ hl₀ hb₁ hl₁
  obtain ⟨e⟩ := shuffle_induced_iso ρ.rank_pos A.obj hswap S hS hid
  exact exists_ne_zero_jacquet_hom_of_injective T _ _ _ i hi e.symm X hX

/-- **Cover.** Assume the shuffle count of `TwoSegmentSocleShuffleJacquet`. Every
composition factor of `J(⟨Δ₀⟩ × ⟨Δ₁⟩)` that is not equivalent to the identity
shuffle tensor `τ_{S_id}` is a composition factor of the image of `J(X)`, for every
nonzero subrepresentation `X`. -/
theorem mem_jordanHolderSupport_jacquetImage_of_ne_id
    (hS1 : TwoSegmentSocleShuffleJacquet.{uF, uV, max uF uV} F T)
    (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (q l : ℕ)
    (d : T.SegmentProductDatum.{uV, uF} ((q + l) * ρ.rank)) (h₂ : d.length = 2)
    (hd : d.HasSegmentSocles)
    (hb₀ : (d.segments ⟨0, by omega⟩).base = ρ.twist l)
    (hl₀ : (d.segments ⟨0, by omega⟩).length = q)
    (hb₁ : (d.segments ⟨1, by omega⟩).base = ρ.twist 0)
    (hl₁ : (d.segments ⟨1, by omega⟩).length = l)
    (hswap : ∀ a b : ℕ, b + 1 < a → letI := T.topology
      Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 ρ.rank ρ.rank_pos)).obj
            ![T.segmentFactor A.obj (a : ℝ), T.segmentFactor A.obj (b : ℝ)] ≅
        (T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 ρ.rank ρ.rank_pos)).obj
            ![T.segmentFactor A.obj (b : ℝ), T.segmentFactor A.obj (a : ℝ)]))
    (τ : Rep.{max uF uV} ℂ ((BlockShape.uniform (q + l) ρ.rank ρ.rank_pos).Levi F.Carrier))
    (hτ : τ ∈ (jordanHolderSupport (CuspidalJacquetMultiplicity.upperJacquet T
      (BlockShape.uniform (q + l) ρ.rank ρ.rank_pos) d.induced.obj) :
        Set (Rep.{max uF uV} ℂ ((BlockShape.uniform (q + l) ρ.rank ρ.rank_pos).Levi F.Carrier))))
    (hbad : letI := T.topology
      ¬ Nonempty ((FiniteTensor.externalSmoothObject
        (shuffleFactors F T A.obj (q + l) ρ.rank_pos (idShuffle q l) l 0)).representation.Equiv
          τ.ρ))
    (X : letI := T.topology; Subrepresentation d.induced.representation) (hX : X ≠ ⊥) :
    τ ∈ (jordanHolderSupport (Rep.of (jacquetImage T
      (BlockShape.uniform (q + l) ρ.rank ρ.rank_pos) X).toRepresentation) :
        Set (Rep.{max uF uV} ℂ ((BlockShape.uniform (q + l) ρ.rank ρ.rank_pos).Levi F.Carrier))) := by
  let := T.topology
  have hirr := isIrreducible_of_mem_jordanHolderSupport hτ
  obtain ⟨M, hM, hMpos⟩ := hτ
  have hcount := ((hS1 ρ A (l : ℝ) 0 q l d h₂ hA hd hb₀ hl₀ hb₁ hl₁).2 τ.V τ.ρ hirr M).1 hM
  have hpos : 0 < Nat.card {S : Finset (Fin (q + l)) // S.card = q ∧
      Nonempty ((FiniteTensor.externalSmoothObject
        (shuffleFactors F T A.obj (q + l) ρ.rank_pos S l 0)).representation.Equiv τ.ρ)} :=
    hcount ▸ hMpos
  obtain ⟨⟨S, hS, ⟨eS⟩⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  have hid : S ≠ idShuffle q l := by
    rintro rfl
    exact hbad ⟨eS⟩
  obtain ⟨g, hg⟩ := exists_ne_zero_jacquet_hom_shuffle T ρ A hA q l d h₂ hd hb₀ hl₀ hb₁ hl₁
    hswap S hS hid X hX
  refine mem_jordanHolderSupport_jacquetImage T _ d.induced.property τ ⟨M, hM, hMpos⟩ X
    (eS.toIntertwiningMap.comp g) fun h => hg ?_
  refine DFunLike.ext _ _ fun x => ?_
  exact eS.injective ((DFunLike.congr_fun h x).trans (map_zero eS).symm)

end Langlands.Classification.JuxtaposedShuffle
