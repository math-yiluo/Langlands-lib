import Langlands.Representation.Classification.MoeglinWaldspurgerDerivativeToolkit
import Langlands.Representation.Classification.MoeglinWaldspurgerRealizedLinkage
import Langlands.Representation.Classification.SegmentProductOrderedAssembly
import Langlands.Representation.Derivative.ProductVanishing

/-!
# Prepending point segments to a segment-product datum

The iterated product `B × (B × ⋯ × Y)` with an arbitrary representation `B`, the point segment
`[y, y]` realized as the singleton segment of `ν^{x+y} ρ` with block the chosen supercuspidal
representative, and the datum obtained by prepending `j` such blocks.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification
open Langlands.Classification.LeftCuspidalDerivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-! ### Iterated products with a fixed representation -/

variable (T) in
/-- `B × (B × ⋯ × Y)`, with `j` factors `B`. -/
def iterProd {r : ℕ}
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)) :
    (j : ℕ) → {m : ℕ} →
      (letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) →
      (letI := T.topology;
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (powerRank r j m) F.Carrier))
  | 0, _, Y => Y
  | j + 1, m, Y =>
    letI := T.topology
    (T.binaryNormalizedProductFunctor r (powerRank r j m)).obj (B, iterProd B j Y)

theorem powerProduct_eq_iterProd {d : ℕ}
    (A : letI := T.topology; GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)) :
    ∀ (j : ℕ) {m : ℕ}
      (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      powerProduct F T A j Y = iterProd T A.obj j Y
  | 0, _, _ => rfl
  | j + 1, m, Y => by
    let := T.topology
    show (T.binaryNormalizedProductFunctor d (powerRank d j m)).obj (A.obj, powerProduct F T A j Y) =
      (T.binaryNormalizedProductFunctor d (powerRank d j m)).obj (A.obj, iterProd T A.obj j Y)
    rw [powerProduct_eq_iterProd A j Y]

theorem iterProd_castRank {r d : ℕ} (e : r = d)
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d F.Carrier))
    (j : ℕ) {m : ℕ}
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) :
    iterProd T (T.castRank e.symm B) j Y = T.castRank (by rw [e]) (iterProd T B j Y) := by
  subst e
  rfl

theorem iterProd_mono {r : ℕ}
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)) :
    ∀ (j : ℕ) {m : ℕ}
      {Y Y' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)},
      (letI := T.topology; SmoothRep.IsSubrepresentation Y Y') →
        (letI := T.topology;
          SmoothRep.IsSubrepresentation (iterProd T B j Y) (iterProd T B j Y'))
  | 0, _, _, _, h => h
  | j + 1, m, Y, Y', h => by
    let := T.topology
    obtain ⟨f, hf⟩ := iterProd_mono B j h
    let g : (B, iterProd T B j Y) ⟶ (B, iterProd T B j Y') := (𝟙 _, f)
    exact ⟨(T.binaryNormalizedProductFunctor r (powerRank r j m)).map g,
      T.binaryProductMap_injective g (fun _ _ h => h) hf⟩

/-- `B × -` iterated carries isomorphisms to isomorphisms. -/
def iterProdIso {r : ℕ}
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)) :
    (j : ℕ) → {m : ℕ} →
      {Y Y' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)} →
      (Y ≅ Y') → (iterProd T B j Y ≅ iterProd T B j Y')
  | 0, _, _, _, e => e
  | j + 1, m, _, _, e =>
    letI := T.topology
    (T.binaryNormalizedProductFunctor r (powerRank r j m)).mapIso
      (Iso.prod (Iso.refl _) (iterProdIso B j e))

theorem iterProd_nontrivial {r : ℕ}
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
    [Nontrivial B] :
    ∀ (j : ℕ) {m : ℕ}
      (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      Nontrivial Y → Nontrivial (iterProd T B j Y)
  | 0, _, _, hY => hY
  | j + 1, m, Y, hY => by
    let := T.topology
    have := iterProd_nontrivial B j Y hY
    exact Derivative.ProductVanishing.nontrivial_binary T (B, iterProd T B j Y)

theorem iterProd_hasFiniteLength {r : ℕ}
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
    (hB : letI := T.topology; B.HasFiniteLength) :
    ∀ (j : ℕ) {m : ℕ}
      {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)},
      (letI := T.topology; Y.HasFiniteLength) →
        (letI := T.topology; (iterProd T B j Y).HasFiniteLength)
  | 0, _, _, hY => hY
  | j + 1, m, Y, hY => by
    let := T.topology
    exact Aubert.binaryProduct_preservesFiniteLength F T r (powerRank r j m) B
      (iterProd T B j Y) hB (iterProd_hasFiniteLength B hB j hY)

/-! ### Point segments -/

variable (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ)

/-- The point `[y, y]` as the singleton segment of `ν^{x+y} ρ`. -/
def pointSegment (y : ℤ) : T.Segment.{max uF uV, uF} :=
  T.singletonSegment (ρ.twist (x + (y : ℝ)))

theorem pointSegment_eq (y : ℤ) : pointSegment ρ x y = (point y).realize ρ x := by
  unfold pointSegment singletonSegment Interval.realize Segment.twist
  have hl : (point y).length = 1 := by simp [point, Interval.length]
  congr 1
  exact hl.symm

theorem pointSegment_degree (y : ℤ) : (pointSegment ρ x y).degree = ρ.rank :=
  T.singletonSegment_degree _

variable (F) in
/-- The block of the point segment: the chosen supercuspidal representative. -/
def pointBlock (y : ℤ) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (pointSegment ρ x y).degree F.Carrier) :=
  T.castRank (pointSegment_degree ρ x y).symm (cuspRep F T ρ x y).obj

theorem pointBlock_isSegmentSocle (y : ℤ) :
    T.IsSegmentSocle (pointSegment ρ x y) (pointBlock F ρ x y) :=
  T.singletonSegment_isSegmentSocle _ _ (cuspRep_represents F T ρ x y)

theorem pointBlock_isIrreducible (y : ℤ) :
    letI := T.topology; (pointBlock F ρ x y).IsIrreducible :=
  T.isIrreducible_castRank _ _ (cuspRep F T ρ x y).property.1

/-! ### Prepending point segments -/

variable (F) in
/-- The datum with `j` point segments `[y, y]` followed by `d₀`. -/
def iterCons (y : ℤ) :
    (j : ℕ) → {m : ℕ} → T.SegmentProductDatum.{max uF uV, uF} m →
      T.SegmentProductDatum.{max uF uV, uF} (powerRank (pointSegment ρ x y).degree j m)
  | 0, _, d₀ => d₀
  | j + 1, _, d₀ =>
    SegmentProductOrderedAssembly.cons (pointSegment ρ x y) (pointBlock F ρ x y)
      (iterCons y j d₀)

theorem iterCons_induced (y : ℤ) :
    ∀ (j : ℕ) {m : ℕ} (d₀ : T.SegmentProductDatum.{max uF uV, uF} m),
      letI := T.topology
      Nonempty ((iterCons F ρ x y j d₀).induced ≅
        iterProd T (pointBlock F ρ x y) j d₀.induced)
  | 0, _, _ => ⟨Iso.refl _⟩
  | j + 1, m, d₀ => by
    let := T.topology
    obtain ⟨e₀⟩ := SegmentProductOrderedAssembly.nonempty_cons_iso_binary
      (pointSegment ρ x y) (pointBlock F ρ x y) (iterCons F ρ x y j d₀)
    obtain ⟨e₁⟩ := iterCons_induced y j d₀
    exact ⟨e₀ ≪≫ (T.binaryNormalizedProductFunctor _ _).mapIso (Iso.prod (Iso.refl _) e₁)⟩

theorem iterCons_segments (y : ℤ) :
    ∀ (j : ℕ) {m : ℕ} (d₀ : T.SegmentProductDatum.{max uF uV, uF} m),
      List.ofFn (iterCons F ρ x y j d₀).segments =
        List.replicate j (pointSegment ρ x y) ++ List.ofFn d₀.segments
  | 0, _, _ => rfl
  | j + 1, _, d₀ => by
    show List.ofFn (SegmentProductOrderedAssembly.cons (pointSegment ρ x y)
      (pointBlock F ρ x y) (iterCons F ρ x y j d₀)).segments = _
    rw [SegmentProductOrderedAssembly.cons_segments, iterCons_segments y j d₀]
    rfl

theorem iterCons_hasSegmentSocles (y : ℤ) :
    ∀ (j : ℕ) {m : ℕ} (d₀ : T.SegmentProductDatum.{max uF uV, uF} m),
      d₀.HasSegmentSocles → (iterCons F ρ x y j d₀).HasSegmentSocles
  | 0, _, _, h => h
  | j + 1, _, d₀, h =>
    SegmentProductOrderedAssembly.cons_hasSegmentSocles _ _ _
      (pointBlock_isSegmentSocle ρ x y) (iterCons_hasSegmentSocles y j d₀ h)

end Langlands.MoeglinWaldspurger.Derivation
