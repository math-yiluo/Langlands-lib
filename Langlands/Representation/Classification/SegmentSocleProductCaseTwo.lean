import Langlands.Representation.Derivative.RestrictedProductLevel
import Langlands.Representation.Derivative.RestrictionBridge
import Langlands.Representation.Classification.SegmentProductCuspidalEmbedding
import Langlands.Representation.Classification.SegmentContentShift
import Langlands.Representation.Classification.SegmentSocleProductHomogeneityInduction
import Langlands.Representation.Classification.SegmentSocleDerivativesStatement
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof

/-!
# The second case of Zelevinsky's 6.3

Let `π = ⟨Δ_1⟩ × π°` with `π°|P` homogeneous, and let `W ≠ 0` inject both into
`π|P` and into the quotient `τ = ⟨Δ_1⟩ × (π°|P)` of BZ77 4.13(a). By Ze80 5.3,
`τ` is homogeneous of the level `λ°` of `π°|P`, so `W` has level `λ°`, and
`W^(λ°)` injects into `τ^(λ°) ≅ ⟨Δ_1⟩ × π°^(λ°)` (BZ77 4.14(a)), which is a
product of segment socles `⟨Δ_1⟩ × ⟨Δ_2⁻⟩ × ⋯ × ⟨Δ_r⁻⟩` (highest derivative of
a segment-socle product). An irreducible subrepresentation of `W^(λ°)` then has
support `Δ_1 + Δ_2⁻ + ⋯ + Δ_r⁻`, and the support shift for cuspidal products
(BZ77 4.7(b)) bounds its `ν`-twist by `Δ_1 + ⋯ + Δ_r`. Integral twist freeness
and the endpoint condition make this impossible.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Classification.SegmentSocleProductCaseTwo

open GeneralLinear PadicField.TopologicalData Derivative HarmonicAnalysis
open LevelCalculus RightMixedLevel RestrictedProductLevel MirabolicProductRestriction
open SegmentProductCuspidalEmbedding SegmentProductSplit SegmentSocleProductHomogeneityInduction
open SegmentContentShift

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## Rank casts -/

section Casts

variable {T : F.TopologicalData}

theorem embedsCuspidal_of_rankCast {a b : ℕ} (hab : a = b)
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    {S : Multiset (CuspidalDatum.{uV, uF} T)}
    (hX : EmbedsCuspidal T ((generalLinearRankCast T hab).obj X) S) : EmbedsCuspidal T X S := by
  subst hab
  exact hX

variable (T) in
/-- The binary product of rank casts is the rank cast of the binary product. -/
theorem binary_rankCast_obj {a a' b b' : ℕ} (ha : a = a') (hb : b = b') (h : a + b = a' + b') :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      (T.binaryNormalizedProductFunctor a' b').obj
          ((generalLinearRankCast T ha).obj A, (generalLinearRankCast T hb).obj B) =
        (generalLinearRankCast T h).obj ((T.binaryNormalizedProductFunctor a b).obj (A, B)) := by
  subst ha hb
  intro A B
  rfl

variable (T) in
theorem mirabolicDerivativeOfOrder_rankCast_obj
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {a b k : ℕ} (h : a = b)
    (hka : 0 < k ∧ k ≤ a + 1) (hkb : 0 < k ∧ k ≤ b + 1) (c : a + 1 - k = b + 1 - k) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier),
      (mirabolicDerivativeOfOrder T ψ b k hkb).obj ((mirabolicRankCast T h).obj X) =
        (generalLinearRankCast T c).obj ((mirabolicDerivativeOfOrder T ψ a k hka).obj X) := by
  subst h
  intro X
  rfl

/-- An irreducible representation is nonzero. -/
theorem nontrivial_of_isSegmentSocle {Δ : T.Segment.{uV, uF}}
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentSocle Δ π) : Nontrivial π := by
  let _ := T.topology
  obtain ⟨_, _, hirr, _⟩ := h
  have := (Representation.irreducible_iff_isSimpleModule_asModule π.representation).mp hirr
  exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear Δ.degree F.Carrier))
    π.representation.asModule

end Casts

/-! ## Binary products with a segment socle in front -/

section Cons

variable {T : F.TopologicalData}

/-- The datum with first segment `Δ` and first block `D`, followed by `d'`. -/
def consDatum (Δ : T.Segment.{uV, uF})
    (D : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    {c : ℕ} (d' : SegmentProductDatum.{uV, uF} T c) :
    SegmentProductDatum.{uV, uF} T (Δ.degree + c) where
  length := d'.length + 1
  segments := Fin.cons Δ d'.segments
  degree_sum := by
    rw [Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [d'.degree_sum]
  blocks i := Fin.cases (motive := fun i : Fin (d'.length + 1) => letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear
        ((Fin.cons Δ d'.segments : Fin (d'.length + 1) → T.Segment.{uV, uF}) i).degree
          F.Carrier))
    D (fun j => d'.blocks j) i

theorem consDatum_hasSegmentSocles (Δ : T.Segment.{uV, uF})
    (D : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hD : T.IsSegmentSocle Δ D) {c : ℕ} (d' : SegmentProductDatum.{uV, uF} T c)
    (hd' : d'.HasSegmentSocles) : (consDatum Δ D d').HasSegmentSocles := by
  intro i
  change Fin (d'.length + 1) at i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hD
  · exact hd' j

theorem consDatum_cuspidalContent (Δ : T.Segment.{uV, uF})
    (D : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    {c : ℕ} (d' : SegmentProductDatum.{uV, uF} T c) :
    (consDatum Δ D d').multisegment.cuspidalContent =
      Δ.cuspidalContent + d'.multisegment.cuspidalContent := by
  rw [cuspidalContent_eq, cuspidalContent_eq]
  change ((List.ofFn (Fin.cons Δ d'.segments : Fin (d'.length + 1) → T.Segment.{uV, uF})).map
    Segment.cuspidalContent).sum = _
  rw [List.ofFn_succ]
  simp

/-- A segment socle embeds in the cuspidal product of the members of its segment. -/
theorem embedsCuspidal_socle (Δ : T.Segment.{uV, uF})
    (D : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hD : T.IsSegmentSocle Δ D) : EmbedsCuspidal T D Δ.cuspidalContent := by
  let e : SegmentProductDatum.{uV, uF} T Δ.degree := ⟨1, fun _ => Δ, by simp, fun _ => D⟩
  have h1 := embedsCuspidal_induced e (fun _ => hD)
  obtain ⟨iso⟩ := nonempty_iso_single e rfl rfl
  have h2 := embedsCuspidal_of_rankCast _ (h1.of_iso iso.symm)
  have hc : e.multisegment.cuspidalContent = Δ.cuspidalContent := by
    rw [cuspidalContent_eq]
    simp [e]
  rw [hc] at h2
  exact h2

variable (T) in
/-- If the second factor has rank zero and dimension one, the binary product
injects into the first factor. -/
theorem exists_injective_rightZero {a c : ℕ} (ha : 0 < a) (hc : c = 0) (hac : a = a + c) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (Y : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier)),
      Module.finrank ℂ Y = 1 →
      ∃ φ : (T.binaryNormalizedProductFunctor a c).obj (A, Y) ⟶
          (generalLinearRankCast T hac).obj A,
        Function.Injective (SmoothRep.hom φ) := by
  let _ := T.topology
  subst hc
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  intro A Y hY
  have : Module.Finite ℂ Y := Module.finite_of_finrank_pos (by omega)
  let eY : Y ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq Y ℂ (by simp [hY])
  let e : (A ⊗[ℂ] Y) ≃ₗ[ℂ] A :=
    (TensorProduct.congr (LinearEquiv.refl ℂ A) eY).trans (TensorProduct.rid ℂ A)
  have key : ∀ g : GeneralLinear (a + 1) F.Carrier,
      e.toLinearMap ∘ₗ LinearMap.rTensor Y (A.representation g) =
        A.representation g ∘ₗ e.toLinearMap := by
    intro g
    apply TensorProduct.ext'
    intro v y
    simp [e]
  have hg : ∀ g : GeneralLinear (a + 1 + 0) F.Carrier,
      GeneralLinear.reindex (R := F.Carrier) (finCongr (show a + 1 + 0 = a + 1 by omega)) g = g := by
    intro g
    apply Units.ext
    ext i j
    rfl
  let φ : ((T.binaryRightZeroTensorFunctor (a := a + 1) (b := 0) rfl).obj (A, Y)).representation.IntertwiningMap
      ((generalLinearRankCast T hac).obj A).representation :=
    { toLinearMap := e.toLinearMap ∘ₗ (ULift.moduleEquiv (R := ℂ) (M := A ⊗[ℂ] Y)).toLinearMap
      isIntertwining' := fun g => LinearMap.ext fun x => by
        change e (LinearMap.rTensor Y (A.representation
            (GeneralLinear.reindex (R := F.Carrier) (finCongr (show a + 1 + 0 = a + 1 by omega)) g))
            x.down) = A.representation g (e x.down)
        rw [hg g]
        exact LinearMap.congr_fun (key g) x.down }
  refine ⟨SmoothRep.ofHom φ, ?_⟩
  intro x y hxy
  exact ULift.ext _ _ (e.injective hxy)

/-- `⟨Δ⟩ × ⟨Δ'_1⟩ × ⋯ × ⟨Δ'_s⟩` embeds in the cuspidal product of all members,
written as the binary product of `⟨Δ⟩` with the product of the others. -/
theorem embedsCuspidal_binary_cons (Δ : T.Segment.{uV, uF})
    (D : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hD : T.IsSegmentSocle Δ D) {c k : ℕ} (d' : SegmentProductDatum.{uV, uF} T c)
    (hd' : d'.HasSegmentSocles) (hl : d'.length = k + 1) :
    EmbedsCuspidal T ((T.binaryNormalizedProductFunctor Δ.degree c).obj (D, d'.induced))
      (Δ.cuspidalContent + d'.multisegment.cuspidalContent) := by
  have hemb := embedsCuspidal_induced _ (consDatum_hasSegmentSocles Δ D hD d' hd')
  rw [consDatum_cuspidalContent] at hemb
  obtain ⟨l, s, hs, bl⟩ := d'
  change l = k + 1 at hl
  subst hl hs
  obtain ⟨iso⟩ := nonempty_iso_binary (k := k) (consDatum Δ D ⟨k + 1, s, rfl, bl⟩) rfl
  exact embedsCuspidal_of_rankCast _ (hemb.of_iso iso.symm)

/-- The same when no segment follows: the second factor has rank zero and
dimension one. -/
theorem embedsCuspidal_binary_nil (Δ : T.Segment.{uV, uF})
    (D : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hD : T.IsSegmentSocle Δ D) {c : ℕ} (d' : SegmentProductDatum.{uV, uF} T c)
    (hl : d'.length = 0)
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier))
    (hY : Module.finrank ℂ Y = 1) :
    EmbedsCuspidal T ((T.binaryNormalizedProductFunctor Δ.degree c).obj (D, Y))
      (Δ.cuspidalContent + d'.multisegment.cuspidalContent) := by
  obtain ⟨l, s, hs, bl⟩ := d'
  change l = 0 at hl
  subst hl
  have hc : c = 0 := by
    rw [← hs]
    simp
  have h0 : (⟨0, s, hs, bl⟩ : SegmentProductDatum.{uV, uF} T c).multisegment.cuspidalContent = 0 := by
    rw [cuspidalContent_eq]
    simp
  rw [h0, add_zero]
  obtain ⟨φ, hφ⟩ := exists_injective_rightZero T Δ.degree_pos hc (by omega) D Y hY
  exact ((embedsCuspidal_socle Δ D hD).rankCast _).of_injective φ hφ

end Cons

/-! ## The support bound -/

section Core

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
  (hE : Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T)
  (hLD : LeftMixedProductDerivative.{uF, max uF uV} F T)
  (hH : letI := T.topology
    ∀ (k r : ℕ) (ρ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
      (τ : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic r F.Carrier)),
      IsHomogeneous T ψ τ → IsHomogeneous T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)))
  (hC : letI := T.topology
    ∀ (N r : ℕ) (ρ : Fin r → CuspidalDatum.{uV, uF} T) (h : ∑ i, (ρ i).rank = N + 1)
      (A : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)),
      (∀ i, (ρ i).IsRepresentedBy (A i)) →
      ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic N F.Carrier))
        (f : W ⟶ (generalLinearRestriction T N).obj (T.cuspidalProductInduced ρ h A)),
        Function.Injective (SmoothRep.hom f) →
      ∀ (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1), level T ψ W = k →
      ∀ σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (N + 1 - k) F.Carrier),
        IsIrreducibleSubrepresentation
          ((mirabolicDerivativeOfOrder T ψ N k hk).obj W).representation σ.representation →
        ∀ s : Multiset (CuspidalDatum.{uV, uF} T), T.IsSupercuspidalSupport σ s →
          s.map (CuspidalDatum.twist 1) ≤ (List.ofFn ρ : Multiset (CuspidalDatum.{uV, uF} T)))
include hE hLD hH hC

/-- Let `D × P` embed in a cuspidal product with multiset `S`, let `P|P` be
homogeneous of level `l`, and let `D × (P|P)^(l)` embed in a cuspidal product
with multiset `S'`. If a nonzero `W` injects both into `(D × P)|P` and into
`D × (P|P)`, then `ν · S' ≤ S`. -/
theorem support_shift_le {m n l : ℕ} (hl : 0 < l ∧ l ≤ n + 1) :
    letI := T.topology
    ∀ (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + 1) F.Carrier))
      (P : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)),
      Nontrivial D →
      IsHomogeneous T ψ ((generalLinearRestriction T n).obj P) →
      level T ψ ((generalLinearRestriction T n).obj P) = l →
      ∀ S S' : Multiset (CuspidalDatum.{uV, uF} T),
      EmbedsCuspidal T ((generalLinearRankCast T
          (show (m + 1) + (n + 1) = (m + n + 1) + 1 by omega)).obj
          ((T.binaryNormalizedProductFunctor (m + 1) (n + 1)).obj (D, P))) S →
      EmbedsCuspidal T ((T.binaryNormalizedProductFunctor (m + 1) (n + 1 - l)).obj
          (D, (mirabolicDerivativeOfOrder T ψ n l hl).obj
            ((generalLinearRestriction T n).obj P))) S' →
      ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier))
        (f : W ⟶ (restrictedProduct T m n).obj (D, P))
        (g : W ⟶ (restrictionQuotient T m n).obj (D, P)),
        Function.Injective (SmoothRep.hom f) → Function.Injective (SmoothRep.hom g) →
        Nontrivial W → S'.map (CuspidalDatum.twist 1) ≤ S := by
  let _ := T.topology
  intro D P hD hP hlev S S' hS hS' W f g hf hg hW
  let R := (generalLinearRestriction T n).obj P
  let X := (T.leftMixedProductFunctor (m + 1) n).obj (D, R)
  have hcast : (m + 1) + n = m + n + 1 := by omega
  have hτh : IsHomogeneous T ψ ((restrictionQuotient T m n).obj (D, P)) :=
    isHomogeneous_mirabolicRankCast T ψ hcast X (hH (m + 1) n D R hP)
  have hWl : level T ψ W = l := by
    rw [level_eq_of_isHomogeneous T ψ hτh g hg hW]
    change level T ψ ((mirabolicRankCast T hcast).obj X) = l
    rw [level_mirabolicRankCast]
    have h1 : level T ψ X ≤ level T ψ ((generalLinearRestriction T n).obj P) :=
      level_leftMixed_le T ψ hLD D R
    have h2 : level T ψ ((generalLinearRestriction T n).obj P) ≤ level T ψ X :=
      le_level_leftMixed T ψ hLD D R hD
    omega
  have hk : 0 < l ∧ l ≤ m + n + 1 + 1 := ⟨hl.1, by omega⟩
  have hHND : HasNonzeroDerivative T ψ W l := by
    have := hasNonzeroDerivative_level T ψ W (by omega)
    rwa [hWl] at this
  obtain ⟨_, hWnt⟩ := hHND
  let J := mirabolicDerivativeOfOrder T ψ (m + n + 1) l hk
  have hgJ : Function.Injective (SmoothRep.hom (J.map g)) :=
    map_injective_of_exact (mapsShortExact_mirabolicDerivativeOfOrder T ψ hE _ _ hk) g hg
  have hl' : 0 < l ∧ l ≤ (m + 1) + n + 1 := ⟨hl.1, by omega⟩
  have hτ : J.obj ((restrictionQuotient T m n).obj (D, P)) =
      (generalLinearRankCast T (show (m + 1) + n + 1 - l = m + n + 1 + 1 - l by omega)).obj
        ((mirabolicDerivativeOfOrder T ψ ((m + 1) + n) l hl').obj X) :=
    mirabolicDerivativeOfOrder_rankCast_obj T ψ hcast hl' hk _ X
  obtain ⟨E⟩ := hLD.1 ψ (m + 1) n l hl
  have hE1 : EmbedsCuspidal T ((generalLinearRankCast T
      (show (m + 1) + n + 1 - l = (m + 1) + (n + 1 - l) by omega)).obj
      ((mirabolicDerivativeOfOrder T ψ ((m + 1) + n) l hl').obj X)) S' :=
    hS'.of_iso (E.app (D, R))
  have hE2 : EmbedsCuspidal T (J.obj ((restrictionQuotient T m n).obj (D, P))) S' := by
    rw [hτ]
    exact (embedsCuspidal_of_rankCast _ hE1).rankCast _
  have hE3 : EmbedsCuspidal T (J.obj W) S' := hE2.of_injective (J.map g) hgJ
  obtain ⟨σ, hσ, hσS⟩ := hE3.exists_irreducible (by omega)
  have hsupp := hσS.isSupercuspidalSupport hσ.1
  obtain ⟨r, ρ, hρ, A, hA, hρS, f0, hf0⟩ := hS
  have := hC (m + n + 1) r ρ hρ A hA W
    (f ≫ (generalLinearRestriction T (m + n + 1)).map f0) (hf0.comp hf) l hk hWl σ hσ S' hsupp
  rwa [hρS] at this

end Core

/-! ## The exclusion -/

section Exclusion

variable (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
  (hE : Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T)
  (hLD : LeftMixedProductDerivative.{uF, max uF uV} F T)
  (hH : letI := T.topology
    ∀ (k r : ℕ) (ρ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
      (τ : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic r F.Carrier)),
      IsHomogeneous T ψ τ → IsHomogeneous T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ)))
  (hC : letI := T.topology
    ∀ (N r : ℕ) (ρ : Fin r → CuspidalDatum.{uV, uF} T) (h : ∑ i, (ρ i).rank = N + 1)
      (A : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)),
      (∀ i, (ρ i).IsRepresentedBy (A i)) →
      ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic N F.Carrier))
        (f : W ⟶ (generalLinearRestriction T N).obj (T.cuspidalProductInduced ρ h A)),
        Function.Injective (SmoothRep.hom f) →
      ∀ (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1), level T ψ W = k →
      ∀ σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (N + 1 - k) F.Carrier),
        IsIrreducibleSubrepresentation
          ((mirabolicDerivativeOfOrder T ψ N k hk).obj W).representation σ.representation →
        ∀ s : Multiset (CuspidalDatum.{uV, uF} T), T.IsSupercuspidalSupport σ s →
          s.map (CuspidalDatum.twist 1) ≤ (List.ofFn ρ : Multiset (CuspidalDatum.{uV, uF} T)))
  (hF : SegmentSocleProductHighestDerivative.{uF, uV} F T)
include hE hLD hH hC hF

/-- The exclusion for a head segment socle `D₀` of `Δ` and a tail datum `td`
whose members do not start right after the end of `Δ`. -/
theorem exclusion_of_head_tail {m n k c : ℕ} (Δ : T.Segment.{uV, uF})
    (D₀ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hD₀ : T.IsSegmentSocle Δ D₀) (td : SegmentProductDatum.{uV, uF} T c)
    (htl : td.length = k + 1) (htd : td.HasSegmentSocles) (ha : Δ.degree = m + 1)
    (hb : c = n + 1) (hsep : ∀ Δ' ∈ List.ofFn td.segments, Δ'.base ≠ Δ.last.twist 1)
    (hP : IsGeneralLinearHomogeneous T ψ ((generalLinearRankCast T hb).obj td.induced))
    (hS : letI := T.topology
      EmbedsCuspidal T ((generalLinearRankCast T
        (show (m + 1) + (n + 1) = (m + n + 1) + 1 by omega)).obj
        ((T.binaryNormalizedProductFunctor (m + 1) (n + 1)).obj
          ((generalLinearRankCast T ha).obj D₀, (generalLinearRankCast T hb).obj td.induced)))
        (Δ.cuspidalContent + td.multisegment.cuspidalContent)) :
    letI := T.topology
    ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier))
      (f : W ⟶ (restrictedProduct T m n).obj
        ((generalLinearRankCast T ha).obj D₀, (generalLinearRankCast T hb).obj td.induced))
      (g : W ⟶ (restrictionQuotient T m n).obj
        ((generalLinearRankCast T ha).obj D₀, (generalLinearRankCast T hb).obj td.induced)),
      Function.Injective (SmoothRep.hom f) → Function.Injective (SmoothRep.hom g) →
        Nontrivial W → False := by
  let _ := T.topology
  intro W f g hf hg hW
  obtain ⟨l, hl_def⟩ : ∃ l, l = ∑ i, (td.segments i).rank := ⟨_, rfl⟩
  have hlb : l ≤ c := by
    rw [hl_def]
    calc ∑ i, (td.segments i).rank ≤ ∑ i, (td.segments i).degree :=
          Finset.sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (td.segments i).length_pos
      _ = c := td.degree_sum
  have hlpos : 0 < l := by
    have : Nonempty (Fin td.length) := ⟨⟨0, by omega⟩⟩
    rw [hl_def]
    exact Finset.sum_pos (fun i _ => (td.segments i).rank_pos) Finset.univ_nonempty
  have hl : 0 < l ∧ l ≤ n + 1 := ⟨hlpos, by omega⟩
  obtain ⟨hvan, ⟨d', hd'seg, hd'soc, ⟨eY⟩⟩, hone⟩ := hF ψ _ td htd l hlb hl_def
  have hsingle : d'.length = 0 → ∀ i, (td.segments i).length = 1 := by
    intro h0 i
    have hnil := hd'seg.symm.trans (List.ofFn_eq_nil_iff.mpr h0)
    have hi := List.filterMap_eq_nil_iff.mp hnil (td.segments i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    have := (td.segments i).length_pos
    by_cases h2 : 2 ≤ (td.segments i).length
    · simp [h2] at hi
    · omega
  have hY : Nontrivial ((generalLinearDerivative T ψ c l hlb).obj td.induced) := by
    rcases Nat.eq_zero_or_pos d'.length with h0 | h0
    · exact Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [hone (hsingle h0)]; exact one_pos)
    · have hblocks : ∀ i, Nontrivial (d'.blocks i) := fun i =>
        nontrivial_of_isSegmentSocle (hd'soc i)
      exact (nontrivial_iff_of_iso eY).mpr
        (ProductVanishing.nontrivial_normalizedProduct T d'.shape d'.blocks hblocks ⟨0, h0⟩)
  have hlev : level T ψ ((generalLinearRestriction T n).obj
      ((generalLinearRankCast T hb).obj td.induced)) = l := by
    rw [level_eq_iff T ψ hlpos]
    refine ⟨by omega,
      (RestrictionBridge.nontrivial_generalLinearDerivative_iff T ψ hb hlb hlpos _).mp hY, ?_⟩
    intro j hj hjn hnd
    have hj' : j ≤ c := by omega
    have := (RestrictionBridge.nontrivial_generalLinearDerivative_iff T ψ hb hj' (by omega)
      _).mpr hnd
    exact not_subsingleton _ (hvan j hj' hj)
  have hDnt : Nontrivial ((generalLinearRankCast T ha).obj D₀) :=
    (RestrictionBridge.nontrivial_generalLinearRankCast_iff T ha D₀).mpr
      (nontrivial_of_isSegmentSocle hD₀)
  have hc : c - l = n + 1 - l := by omega
  have hS'0 : EmbedsCuspidal T ((T.binaryNormalizedProductFunctor Δ.degree (c - l)).obj
      (D₀, (generalLinearDerivative T ψ c l hlb).obj td.induced))
      (Δ.cuspidalContent + d'.multisegment.cuspidalContent) := by
    rcases Nat.eq_zero_or_pos d'.length with h0 | h0
    · exact embedsCuspidal_binary_nil Δ D₀ hD₀ d' h0 _ (hone (hsingle h0))
    · obtain ⟨k', hk'⟩ : ∃ k', d'.length = k' + 1 := ⟨d'.length - 1, by omega⟩
      exact (embedsCuspidal_binary_cons Δ D₀ hD₀ d' hd'soc hk').of_iso
        ((T.binaryNormalizedProductFunctor _ _).mapIso (Iso.prod (Iso.refl D₀) eY))
  have hS' : EmbedsCuspidal T ((T.binaryNormalizedProductFunctor (m + 1) (n + 1 - l)).obj
      ((generalLinearRankCast T ha).obj D₀, (mirabolicDerivativeOfOrder T ψ n l hl).obj
        ((generalLinearRestriction T n).obj ((generalLinearRankCast T hb).obj td.induced))))
      (Δ.cuspidalContent + d'.multisegment.cuspidalContent) := by
    rw [← RestrictionBridge.generalLinearDerivative_obj_eq_cast T ψ hb hlb hl hc td.induced,
      binary_rankCast_obj T ha hc (by omega) D₀ _]
    exact hS'0.rankCast _
  have hP' : IsHomogeneous T ψ ((generalLinearRestriction T n).obj
      ((generalLinearRankCast T hb).obj td.induced)) :=
    (isGeneralLinearHomogeneous_iff T ψ _).mp hP
  have key := support_shift_le T ψ hE hLD hH hC hl _ _ hDnt hP' hlev _ _ hS hS' W f g hf hg hW
  rw [cuspidalContent_eq td, cuspidalContent_eq d', hd'seg] at key
  exact not_map_twist_le (cuspidalIntegralTwistFreeness F T) Δ (List.ofFn td.segments) hsep key

/-- `exclusion_of_head_tail` with the head block on a general linear group of
an arbitrary rank `a` equal to the degree of `Δ`. -/
theorem exclusion_of_head_tail_of_eq {a m n k c : ℕ} (Δ : T.Segment.{uV, uF})
    (hΔa : Δ.degree = a)
    (D₀ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hD₀ : T.IsSegmentSocle Δ ((generalLinearRankCast T hΔa.symm).obj D₀))
    (td : SegmentProductDatum.{uV, uF} T c)
    (htl : td.length = k + 1) (htd : td.HasSegmentSocles) (ha : a = m + 1)
    (hb : c = n + 1) (hsep : ∀ Δ' ∈ List.ofFn td.segments, Δ'.base ≠ Δ.last.twist 1)
    (hP : IsGeneralLinearHomogeneous T ψ ((generalLinearRankCast T hb).obj td.induced))
    (hS : letI := T.topology
      EmbedsCuspidal T ((generalLinearRankCast T
        (show (m + 1) + (n + 1) = (m + n + 1) + 1 by omega)).obj
        ((T.binaryNormalizedProductFunctor (m + 1) (n + 1)).obj
          ((generalLinearRankCast T ha).obj D₀, (generalLinearRankCast T hb).obj td.induced)))
        (Δ.cuspidalContent + td.multisegment.cuspidalContent)) :
    letI := T.topology
    ∀ (W : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (m + n + 1) F.Carrier))
      (f : W ⟶ (restrictedProduct T m n).obj
        ((generalLinearRankCast T ha).obj D₀, (generalLinearRankCast T hb).obj td.induced))
      (g : W ⟶ (restrictionQuotient T m n).obj
        ((generalLinearRankCast T ha).obj D₀, (generalLinearRankCast T hb).obj td.induced)),
      Function.Injective (SmoothRep.hom f) → Function.Injective (SmoothRep.hom g) →
        Nontrivial W → False := by
  subst hΔa
  exact exclusion_of_head_tail T ψ hE hLD hH hC hF Δ D₀ hD₀ td htl htd ha hb hsep hP hS

/-- The second case of Ze80 6.3 does not occur: for an endpoint-separated
product of segment socles whose tail has homogeneous restriction, no nonzero
representation injects both into the restricted product and into its quotient
`⟨Δ_1⟩ × (π°|P)`. -/
theorem caseTwoExclusion {M k : ℕ} (d : SegmentProductDatum.{uV, uF} T M)
    (h : d.length = k + 2) (m n : ℕ) (ha : d.shape.headRank h = m + 1)
    (hb : d.shape.tailRank h = n + 1) (hd : d.HasSegmentSocles)
    (hsep : ∀ i j : Fin d.length, i < j →
      (d.segments j).base ≠ ((d.segments i).last).twist 1)
    (hP : IsGeneralLinearHomogeneous T ψ
      ((generalLinearRankCast T hb).obj (tail d h).induced)) :
    CaseTwoExclusion T d h m n ha hb := by
  let _ := T.topology
  have hS : EmbedsCuspidal T ((generalLinearRankCast T
      (show (m + 1) + (n + 1) = (m + n + 1) + 1 by omega)).obj
      ((T.binaryNormalizedProductFunctor (m + 1) (n + 1)).obj
        ((generalLinearRankCast T ha).obj (d.blocks (d.shape.headIndex h)),
          (generalLinearRankCast T hb).obj (tail d h).induced)))
      ((d.segments (d.shape.headIndex h)).cuspidalContent +
        (tail d h).multisegment.cuspidalContent) := by
    obtain ⟨e⟩ := nonempty_iso_binary d h
    have h1 := embedsCuspidal_of_rankCast _ ((embedsCuspidal_induced d hd).of_iso e.symm)
    have hSeq : d.multisegment.cuspidalContent = (d.segments (d.shape.headIndex h)).cuspidalContent +
        (tail d h).multisegment.cuspidalContent := by
      rw [cuspidalContent_eq d, ofFn_segments_eq_cons d h, List.map_cons, List.sum_cons,
        cuspidalContent_eq (tail d h)]
    rw [binary_rankCast_obj T ha hb (by omega) _ _, ← hSeq]
    exact (h1.rankCast _).rankCast _
  exact exclusion_of_head_tail_of_eq T ψ hE hLD hH hC hF (a := d.shape.headRank h)
    (d.segments (d.shape.headIndex h)) rfl (d.blocks (d.shape.headIndex h)) (hd _) (tail d h) rfl
    (tail_hasSegmentSocles d h hd) ha hb (head_endpoint d h hsep) hP hS

end Exclusion

end Langlands.Classification.SegmentSocleProductCaseTwo
