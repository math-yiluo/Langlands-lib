import Langlands.Representation.Classification.SegmentHeadSupportLeftExact
import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
import Langlands.Representation.Classification.SupercuspidalDerivativesProof

/-!
# Leibniz pieces of a derivative of `L × X` for a supercuspidal first factor

Let `L` be a smooth representation of `GL_r` with `r > 0` whose derivatives of
order strictly between `0` and `r` vanish and whose top derivative is
one-dimensional (by BZ77 §4.4 every irreducible supercuspidal representation
has this pattern). By the BZ77 4.14(c) Leibniz filtration, every irreducible
actual subquotient of the order-`d` derivative of `L × X` is an actual
subquotient of `L × X^(d)` or of the rank cast of `X^(d-r)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Langlands.Classification.SegmentHeadSupport

open GeneralLinear BinaryTensor Derivative

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

section RankZero

/-- A zero smooth representation has a subsingleton carrier. -/
theorem subsingleton_of_isZero {n : ℕ}
    {A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
    (hA : letI := T.topology; IsZero A) : Subsingleton A := by
  let _ := T.topology
  refine ⟨fun v w => ?_⟩
  have h0 : ∀ u : A, u = 0 := fun u =>
    congrArg (fun φ => SmoothRep.hom φ u) (hA.eq_of_src (𝟙 A) 0)
  rw [h0 v, h0 w]

/-- A smooth representation with a subsingleton carrier is zero. -/
theorem isZero_of_subsingleton {n : ℕ}
    {A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
    (hA : Subsingleton A) : letI := T.topology; IsZero A := by
  let _ := T.topology
  rw [IsZero.iff_id_eq_zero]
  ext v
  exact Subsingleton.elim _ _

/-- Rank casts preserve subsingleton carriers. -/
theorem subsingleton_rankCast {a b : ℕ} (h : a = b)
    {A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
    (hA : Subsingleton A) : Subsingleton ((generalLinearRankCast T h).obj A) := by
  subst h
  exact hA

/-- A rank-cast product with a subsingleton factor has a subsingleton carrier. -/
theorem subsingleton_rankCast_product {a b m : ℕ} (h : a + b = m)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hAB : Subsingleton A ∨ Subsingleton B) :
    Subsingleton ((generalLinearRankCast T h).obj ((T.binaryNormalizedProductFunctor a b).obj
      (A, B))) := by
  let _ := T.topology
  apply subsingleton_rankCast
  apply subsingleton_of_isZero
  apply T.isZero_binaryNormalizedProductFunctor_obj
  rcases hAB with hA | hB
  · exact Or.inl (isZero_of_subsingleton T hA)
  · exact Or.inr (isZero_of_subsingleton T hB)

/-- A one-dimensional representation of `GL_0` is isomorphic to the unit. -/
theorem nonempty_iso_unit
    (Z : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier))
    (hZ : Module.finrank ℂ Z = 1) :
    letI := T.topology; Nonempty (Z ≅ T.binaryProductUnit) := by
  let _ := T.topology
  have : Module.Finite ℂ Z := Module.finite_of_finrank_eq_succ hZ
  have : Module.Finite ℂ (T.binaryProductUnit.{uF, uV}) :=
    Module.finite_of_finrank_eq_succ (T.finrank_binaryProductUnit)
  let e : Z ≃ₗ[ℂ] T.binaryProductUnit.{uF, uV} :=
    LinearEquiv.ofFinrankEq _ _ (hZ.trans T.finrank_binaryProductUnit.symm)
  refine ⟨SmoothRep.mkIso (Representation.Equiv.mk e fun g => ?_)⟩
  rw [representation_apply_of_rank_eq_zero rfl Z.representation g,
    representation_apply_of_rank_eq_zero rfl (T.binaryProductUnit.{uF, uV}).representation g]
  rfl

/-- The rank cast of `B` is `B` composed with the entry-preserving reindex. -/
def rankCastEquiv {b c : ℕ} (h : b = c)
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    Representation.Equiv
      (B.representation.comp (reindex (R := F.Carrier) (finCongr h.symm)).toMonoidHom)
      ((generalLinearRankCast T h).obj B).representation := by
  let _ := T.topology
  subst h
  exact Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => by
    change B.representation (reindex (R := F.Carrier) (finCongr rfl) g) = B.representation g
    rw [reindex_finCongr_rfl]
    rfl

/-- A product `Z × B` with a one-dimensional factor `Z` on a rank-zero group is
equivalent, after rank casts, to `B`. -/
theorem nonempty_equiv_rankCast_product_left {a b m : ℕ} (ha : a = 0) (h : a + b = m)
    (h' : b = m)
    (Z : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hZ : Module.finrank ℂ Z = 1) :
    letI := T.topology
    Nonempty (((generalLinearRankCast T h').obj B).representation.Equiv
      ((generalLinearRankCast T h).obj
        ((T.binaryNormalizedProductFunctor a b).obj (Z, B))).representation) := by
  let _ := T.topology
  subst ha h
  obtain ⟨eZ⟩ := nonempty_iso_unit T Z hZ
  let e1 := SmoothRep.equivOfIso
    ((T.binaryNormalizedProductFunctor 0 b).mapIso (Iso.prod eZ (Iso.refl B)))
  let e2 := T.binaryProductLeftUnitEquiv B
  let e3 := rankCastEquiv T h' B
  exact ⟨((e3.symm.trans (liftEquiv _)).trans e2.symm).trans e1.symm⟩

end RankZero

section Pieces

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The derivative pattern of an irreducible supercuspidal representation:
vanishing derivatives of intermediate order and a one-dimensional top
derivative. -/
def DerivativePattern {a : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) : Prop :=
  letI := T.topology
  (∀ (i : ℕ) (hi : i ≤ a), 0 < i → i < a →
    Subsingleton ((generalLinearDerivative T ψ a i hi).obj A)) ∧
  Module.finrank ℂ ((generalLinearDerivative T ψ a a le_rfl).obj A) = 1

/-- BZ77 §4.4: every irreducible supercuspidal representation of positive rank has
the derivative pattern. -/
theorem derivativePattern_of_supercuspidal {a : ℕ} (ha : 0 < a)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (hA : letI := T.topology; A.IsIrreducible)
    (hsc : letI := T.topology; GeneralLinear.IsSupercuspidal A.representation) :
    DerivativePattern T ψ A := by
  let _ := T.topology
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  obtain ⟨h1, h2⟩ := supercuspidalDerivatives.{uF, uV} F T ψ n A hA hsc
  exact ⟨fun i hi h0 hlt => h1 i hi h0 hlt, h2⟩

/-- BZ77 4.14(c) with BZ77 §4.4: an irreducible actual subquotient of the
order-`d` derivative of `L × X`, for `L` of positive rank `r` with the
derivative pattern, is an actual subquotient of `L × X^(d)` (when `d ≤ b`) or of
the rank cast of `X^(d-r)` (when `r ≤ d`). -/
theorem leibniz_cases {r b d : ℕ} (hr : 0 < r) (hd : d ≤ r + b)
    (L : letI := T.topology; SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear r F.Carrier))
    (hL : DerivativePattern T ψ L)
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear b F.Carrier))
    (σ : letI := T.topology;
      SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear (r + b - d) F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (h : letI := T.topology
      SmoothRep.IsSubquotient σ ((generalLinearDerivative T ψ (r + b) d hd).obj
        ((T.binaryNormalizedProductFunctor r b).obj (L, X)))) :
    letI := T.topology
    (∃ (hdb : d ≤ b) (h' : r + (b - d) = r + b - d),
      SmoothRep.IsSubquotient σ ((generalLinearRankCast T h').obj
        ((T.binaryNormalizedProductFunctor r (b - d)).obj
          (L, (generalLinearDerivative T ψ b d hdb).obj X)))) ∨
    (∃ (_ : r ≤ d) (hdb : d - r ≤ b) (h' : b - (d - r) = r + b - d),
      SmoothRep.IsSubquotient σ ((generalLinearRankCast T h').obj
        ((generalLinearDerivative T ψ b (d - r) hdb).obj X))) := by
  let _ := T.topology
  let : σ.representation.IsIrreducible := hσ
  obtain ⟨e, hglue⟩ : ∃ e : LeibnizIndex r b d ≃ Fin (leibnizIndices r b d).card,
      IsGluedFrom (leibnizSource.{uF, max uF uW} T ψ r b d hd)
        (fun i => leibnizPiece T ψ r b d (e.symm i)) :=
    generalLinearDerivativeLeibnizFiltration.{uF, max uF uW} F T ψ r b d hd
  have h1 := SmoothRep.isSubquotient_iff_representation.mp h
  obtain ⟨i0, hi0⟩ := WeylBranchPieces.IsGluedFrom.exists_isSubquotient_piece hglue (L, X)
    (X := σ.representation) h1
  generalize e.symm i0 = x at hi0
  obtain ⟨⟨i, j⟩, hx⟩ := x
  obtain ⟨hir, hjb, hij⟩ := mem_leibnizIndices.1 hx
  dsimp only at hir hjb hij
  have hsq : SmoothRep.IsSubquotient σ ((generalLinearRankCast T (leibnizIndices_rank hx)).obj
      ((T.binaryNormalizedProductFunctor (r - i) (b - j)).obj
        ((generalLinearDerivative T ψ r i hir).obj L,
          (generalLinearDerivative T ψ b j hjb).obj X))) :=
    SmoothRep.isSubquotient_iff_representation.mpr hi0
  by_cases hi0' : i = 0
  · subst hi0'
    have hjd : j = d := by omega
    subst hjd
    exact Or.inl ⟨hjb, leibnizIndices_rank hx, hsq⟩
  by_cases hir' : i = r
  · subst hir'
    have hjd : j = d - i := by omega
    subst hjd
    obtain ⟨f⟩ := nonempty_equiv_rankCast_product_left T (Nat.sub_self i)
      (leibnizIndices_rank hx) (by omega) ((generalLinearDerivative T ψ i i hir).obj L)
      ((generalLinearDerivative T ψ b (d - i) hjb).obj X) hL.2
    refine Or.inr ⟨by omega, hjb, by omega, ?_⟩
    exact SmoothRep.isSubquotient_iff_representation.mpr
      (WeylBranchPieces.IsSubquotient.of_equiv_left f
        (SmoothRep.isSubquotient_iff_representation.mp hsq))
  exfalso
  have hsub := subsingleton_rankCast_product T (leibnizIndices_rank hx) _
    ((generalLinearDerivative T ψ b j hjb).obj X)
    (Or.inl (hL.1 i hir (Nat.pos_of_ne_zero hi0') (lt_of_le_of_ne hir hir')))
  have hσs := subsingleton_of_isSubquotient hsq hsub
  obtain ⟨u, v, huv⟩ := (nontrivial_of_isIrreducible hσ).exists_pair_ne
  exact huv (Subsingleton.elim u v)

end Pieces

end Langlands.Classification.SegmentHeadSupport
