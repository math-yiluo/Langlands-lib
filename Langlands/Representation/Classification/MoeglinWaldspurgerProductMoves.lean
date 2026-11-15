import Langlands.Representation.Classification.MoeglinWaldspurgerUnlinkedSwap
import Langlands.Representation.Classification.BernsteinBinaryRankZero
import Langlands.Representation.Classification.SegmentProductOrderedAssembly

/-!
# Moves in iterated products

Rank-zero units, associativity allowing an irreducible rank-zero last factor, iterated
products up to rank transport, and commuting a factor past the iterated cuspidal factors.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification GeneralLinear
open Langlands.Classification.LeftCuspidalDerivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

theorem castIso_generalLinearRankCast {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)) :
    CastIso T X (letI := T.topology; (Derivative.generalLinearRankCast T h).obj X) := by
  subst h
  exact CastIso.refl X

/-- A rank-zero irreducible right factor is a unit, up to rank transport. -/
theorem castIso_rankZero_right {a w : ℕ} (hw : w = 0)
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (W : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear w F.Carrier))
    (hW : letI := T.topology; W.IsIrreducible) :
    letI := T.topology
    CastIso T ((T.binaryNormalizedProductFunctor a w).obj (X, W)) X := by
  let := T.topology
  subst hw
  have e₁ := (T.binaryNormalizedProductFunctor a 0).mapIso
    (Iso.prod (Iso.refl X) (rankZeroIrreducibleUnitIso F T W hW))
  have e₂ := SegmentProductOrderedAssembly.rightUnitIso T X
  exact (castIso_of_iso (e₁ ≪≫ e₂)).trans (castIso_generalLinearRankCast _ X).symm

/-- Associativity, allowing the last factor to be an irreducible representation of rank
zero. -/
theorem castIso_assoc' {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (C : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier))
    (hC : 0 < c ∨ (c = 0 ∧ (letI := T.topology; C.IsIrreducible))) :
    letI := T.topology
    CastIso T ((T.binaryNormalizedProductFunctor (a + b) c).obj
        ((T.binaryNormalizedProductFunctor a b).obj (A, B), C))
      ((T.binaryNormalizedProductFunctor a (b + c)).obj
        (A, (T.binaryNormalizedProductFunctor b c).obj (B, C))) := by
  let := T.topology
  rcases hC with hc | ⟨hc, hCi⟩
  · exact castIso_assoc ha hb hc A B C
  · have h1 := castIso_rankZero_right hc ((T.binaryNormalizedProductFunctor a b).obj (A, B)) C hCi
    have h2 := castIso_rankZero_right hc B C hCi
    have h3 := (CastIso.refl A).binary h2
    exact h1.trans h3.symm

/-! ### Iterated products -/

theorem CastIso.iterProd {r : ℕ}
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
    (K : ℕ) {m m' : ℕ}
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    {Y' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m' F.Carrier)}
    (h : CastIso T Y Y') : CastIso T (iterProd T B K Y) (iterProd T B K Y') := by
  obtain ⟨rfl, ⟨e⟩⟩ := h
  exact ⟨rfl, ⟨iterProdIso B K e⟩⟩

theorem Embeds.iterProd {r : ℕ}
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
    (K : ℕ) {m m' : ℕ}
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    {Y' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m' F.Carrier)}
    (h : Embeds T Y Y') : Embeds T (iterProd T B K Y) (iterProd T B K Y') := by
  obtain ⟨rfl, f⟩ := h
  exact ⟨rfl, iterProd_mono B K f⟩

/-- `B^K × (B × Y)` is `B^(K+1) × Y`. -/
theorem castIso_iterProd_shift {r : ℕ}
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)) :
    ∀ (K : ℕ) {m : ℕ}
      (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      CastIso T (iterProd T B K (letI := T.topology;
          (T.binaryNormalizedProductFunctor r m).obj (B, Y)))
        (iterProd T B (K + 1) Y)
  | 0, _, _ => CastIso.refl _
  | K + 1, m, Y => by
    let := T.topology
    exact (CastIso.refl B).binary (castIso_iterProd_shift B K Y)

theorem iterProd_rank_pos_or {r : ℕ} (hr : 0 < r)
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
    (K : ℕ) {m : ℕ}
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hY : 0 < m ∨ (m = 0 ∧ (letI := T.topology; Y.IsIrreducible))) :
    0 < powerRank r K m ∨
      (powerRank r K m = 0 ∧ (letI := T.topology; (iterProd T B K Y).IsIrreducible)) := by
  rcases K with _ | K
  · exact hY
  · left
    show 0 < r + powerRank r K m
    omega

/-- **Commuting past the cuspidal factors.** If `Z × B ≅ B × Z`, then
`Z × (B^K × Y) ≅ B^K × (Z × Y)`, up to rank transport. -/
theorem castIso_commute {r z : ℕ} (hr : 0 < r) (hz : 0 < z)
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
    (Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear z F.Carrier))
    (hswap : letI := T.topology;
      CastIso T ((T.binaryNormalizedProductFunctor z r).obj (Z, B))
        ((T.binaryNormalizedProductFunctor r z).obj (B, Z))) :
    ∀ (K : ℕ) {m : ℕ}
      (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      (0 < m ∨ (m = 0 ∧ (letI := T.topology; Y.IsIrreducible))) →
      CastIso T (letI := T.topology;
          (T.binaryNormalizedProductFunctor z (powerRank r K m)).obj (Z, iterProd T B K Y))
        (iterProd T B K (letI := T.topology;
          (T.binaryNormalizedProductFunctor z m).obj (Z, Y)))
  | 0, _, _, _ => CastIso.refl _
  | K + 1, m, Y, hY => by
    let := T.topology
    have hW := iterProd_rank_pos_or hr B K Y hY
    -- `Z × (B × W) ≅ (Z × B) × W ≅ (B × Z) × W ≅ B × (Z × W) ≅ B × B^K (Z × Y)`
    have h1 := (castIso_assoc' hz hr Z B (iterProd T B K Y) hW).symm
    have h2 := hswap.binary (CastIso.refl (iterProd T B K Y))
    have h3 := castIso_assoc' hr hz B Z (iterProd T B K Y) hW
    have h4 := (CastIso.refl B).binary (castIso_commute hr hz B Z hswap K Y hY)
    exact h1.trans (h2.trans (h3.trans h4))

end Langlands.MoeglinWaldspurger.Derivation
