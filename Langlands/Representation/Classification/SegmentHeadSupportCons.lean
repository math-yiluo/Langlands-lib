import Langlands.Representation.Classification.SegmentHeadSupportLeibniz
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Parabolic.HeadTailProductInduction
import Langlands.Representation.Induction.SingleBlock
import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Supercuspidal supports of subquotients of `L × τ`

If `L` is (the universe lift of) a supercuspidal representative of a cuspidal
datum `ρ₀` and `τ` has a supercuspidal support `s`, then every irreducible
actual subquotient of the binary normalized product `L × τ` has the
supercuspidal support `ρ₀ ::ₘ s`. The module also records that exact functors
preserve actual subquotients, the behaviour of subquotients, irreducibility and
supports under rank casts, and that irreducible representations of `GL_0` are
one-dimensional.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Classification.SegmentHeadSupport

open GeneralLinear BinaryTensor PadicField.TopologicalData Derivative

universe uG uH uV uW uF

section Transfer

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- An exact functor preserves actual subquotients. -/
theorem PreservesShortExact.isSubquotient_map
    {Φ : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uW} ℂ H}
    (hΦ : PreservesShortExact Φ) {X Y : SmoothRep.{0, uG, uV} ℂ G}
    (h : SmoothRep.IsSubquotient X Y) : SmoothRep.IsSubquotient (Φ.obj X) (Φ.obj Y) := by
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp h
  exact SmoothRep.isSubquotient_iff_exists.mpr
    ⟨Φ.obj C, Φ.map i, Φ.map q, hΦ.map_injective i hi, hΦ.map_surjective q hq⟩

end Transfer

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

section ProductShapes

/-- Normalized product induction on a rank-cast shape is the rank cast of the
product on the original shape. (Copied from `SegmentProductSplit`.) -/
theorem normalizedProductInductionFunctor_rankCast_obj {m n : ℕ} (C : BlockShape m)
    (h : m = n)
    (X : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (C.size i) F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor (C.rankCast h)).obj X =
      (generalLinearRankCast T h).obj ((T.normalizedProductInductionFunctor C).obj X) := by
  subst h
  rfl

/-- The binary product of positive ranks, written as a product on the binary
shape. (Copied from `SegmentProductSplit`.) -/
theorem binaryNormalizedProductFunctor_obj_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (X : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.binary a b ha hb).size i)
        F.Carrier))
    (h0 : X (0 : Fin 2) = A) (h1 : X (1 : Fin 2) = B) :
    letI := T.topology
    (T.binaryNormalizedProductFunctor a b).obj (A, B) =
      (T.normalizedProductInductionFunctor (BlockShape.binary a b ha hb)).obj X := by
  let _ := T.topology
  rw [T.binaryNormalizedProductFunctor_of_pos ha hb]
  change (T.normalizedProductInductionFunctor (BlockShape.binary a b ha hb)).obj
      ((T.binaryPairFamilyFunctor ha hb).obj (A, B)) = _
  congr 1
  funext i
  fin_cases i
  · exact h0.symm
  · exact h1.symm

end ProductShapes

section RankCast

/-- A rank cast and its inverse cancel. -/
theorem rankCast_symm_obj {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    (generalLinearRankCast T h).obj ((generalLinearRankCast T h.symm).obj X) = X := by
  subst h
  rfl

/-- Subquotients of a rank cast are rank casts of subquotients. -/
theorem isSubquotient_rankCast_iff {a b : ℕ} (h : a = b)
    (σ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    SmoothRep.IsSubquotient σ ((generalLinearRankCast T h).obj X) ↔
      SmoothRep.IsSubquotient ((generalLinearRankCast T h.symm).obj σ) X := by
  subst h
  exact Iff.rfl

/-- Rank casts preserve irreducibility. -/
theorem isIrreducible_rankCast {a b : ℕ} (h : a = b)
    (σ : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible) :
    letI := T.topology; ((generalLinearRankCast T h).obj σ).IsIrreducible := by
  subst h
  exact hσ

/-- Rank casts preserve supercuspidal supports. -/
theorem isSupercuspidalSupport_rankCast_iff {a b : ℕ} (h : a = b)
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (s : Multiset (CuspidalDatum.{uV, uF} T)) :
    T.IsSupercuspidalSupport ((generalLinearRankCast T h).obj σ) s ↔
      T.IsSupercuspidalSupport σ s := by
  subst h
  exact Iff.rfl

end RankCast

section RankZero

/-- An irreducible representation of the trivial group `GL_0` is one-dimensional. -/
theorem finrank_eq_one_of_isIrreducible {n : ℕ} (hn : n = 0)
    (Z : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (hZ : letI := T.topology; Z.IsIrreducible) : Module.finrank ℂ Z = 1 := by
  let _ := T.topology
  let _ : IsSimpleOrder (Subrepresentation Z.representation) := hZ
  rw [← isSimpleModule_iff_finrank_eq_one, isSimpleModule_iff]
  let e : Subrepresentation Z.representation ≃o Submodule ℂ Z :=
    { toFun := fun S => S.toSubmodule
      invFun := fun S => ⟨S, fun g v hv => by
        rw [representation_apply_of_rank_eq_zero hn Z.representation g]
        exact hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.symm.isSimpleOrder

/-- A product `A × Z` with a one-dimensional factor `Z` on a rank-zero group is
equivalent, after rank casts, to `A`. -/
theorem nonempty_equiv_rankCast_product_right {a b m : ℕ} (hb : b = 0) (h : a + b = m)
    (h' : a = m)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (Z : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hZ : Module.finrank ℂ Z = 1) :
    letI := T.topology
    Nonempty (((generalLinearRankCast T h').obj A).representation.Equiv
      ((generalLinearRankCast T h).obj
        ((T.binaryNormalizedProductFunctor a b).obj (A, Z))).representation) := by
  let _ := T.topology
  subst hb h
  obtain ⟨eZ⟩ := nonempty_iso_unit T Z hZ
  let e1 := SmoothRep.equivOfIso
    ((T.binaryNormalizedProductFunctor a 0).mapIso (Iso.prod (Iso.refl A) eZ))
  let e2 := T.binaryProductRightUnitEquiv A
  let e3 := rankCastEquiv T (Nat.add_zero a).symm A
  exact ⟨((e3.symm.trans (liftEquiv _)).trans e2.symm).trans e1.symm⟩

end RankZero

section Cons

/-- An irreducible actual subquotient of the universe lift of a supercuspidal
representative of `ρ₀` has the supercuspidal support `{ρ₀}`. -/
theorem isSupercuspidalSupport_singleton (ρ0 : CuspidalDatum.{uV, uF} T)
    (A0 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ0.rank))
    (hA0 : ρ0.IsRepresentedBy A0)
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ρ0.rank F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (h : letI := T.topology; SmoothRep.IsSubquotient σ (SmoothRep.universeLift.{uF} A0.obj)) :
    T.IsSupercuspidalSupport σ {ρ0} := by
  let := T.topology
  let ρ1 : Fin 1 → CuspidalDatum.{uV, uF} T := fun _ => ρ0
  have hsum : ∑ i, (ρ1 i).rank = ρ0.rank := by simp [ρ1]
  let AA : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ1 i).rank) := fun _ => A0
  let B := T.cuspidalShape ρ1 hsum
  let L := SmoothRep.universeLift.{uF} A0.obj
  let e₀ := T.singleBlockNormalizedProductEquiv B rfl
    (fun i => (AA i).obj.representation) (fun i => (AA i).obj.isSmooth) (0 : Fin 1)
  let e₁ : ((T.cuspidalProductInduced ρ1 hsum AA).representation).Equiv L.representation :=
    e₀.trans (Representation.Equiv.mk (SmoothRep.universeLiftEquiv.{uF} A0.obj).toLinearEquiv
      (fun g => by
        have hg : (GeneralLinear.reindex (R := F.Carrier)
            (finCongr (show ρ0.rank = ρ0.rank from B.singleBlock_size rfl (0 : Fin 1)))).symm g =
              g := by
          ext i j
          rfl
        ext v
        exact congrArg (fun x => ULift.up.{uF} (A0.obj.representation x v)) hg))
  have hsub : SmoothRep.IsSubquotient σ (T.cuspidalProductInduced ρ1 hsum AA) :=
    SmoothRep.IsSubquotient.of_iso_right h (SmoothRep.mkIso e₁).symm
  exact ⟨1, ρ1, by simp [ρ1], hsum, AA, fun _ => hA0, hσ, hsub⟩

/-- Let `A₀` be a supercuspidal representative of `ρ₀` and let `τ` be an
irreducible representation with supercuspidal support `s`. Every irreducible
actual subquotient of `A₀ × τ` has the supercuspidal support `ρ₀ ::ₘ s`. -/
theorem isSupercuspidalSupport_cons {n : ℕ} (ρ0 : CuspidalDatum.{uV, uF} T)
    (A0 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ0.rank))
    (hA0 : ρ0.IsRepresentedBy A0)
    (τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (s : Multiset (CuspidalDatum.{uV, uF} T)) (hτ : T.IsSupercuspidalSupport τ s)
    (σ : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (ρ0.rank + n) F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (h : letI := T.topology
      SmoothRep.IsSubquotient σ ((T.binaryNormalizedProductFunctor ρ0.rank n).obj
        (SmoothRep.universeLift.{uF} A0.obj, τ))) :
    T.IsSupercuspidalSupport σ (ρ0 ::ₘ s) := by
  let := T.topology
  obtain ⟨k, ρs, rfl, hsum, As, hAs, hτirr, hτsq⟩ := hτ
  let L := SmoothRep.universeLift.{uF} A0.obj
  cases k with
  | zero =>
    have hn : n = 0 := by simpa using hsum.symm
    have h' : ρ0.rank = ρ0.rank + n := by omega
    obtain ⟨e⟩ := nonempty_equiv_rankCast_product_right T hn rfl h' L τ
      (finrank_eq_one_of_isIrreducible T hn τ hτirr)
    have h1 : SmoothRep.IsSubquotient σ ((generalLinearRankCast T h').obj L) :=
      SmoothRep.IsSubquotient.of_iso_right h (SmoothRep.mkIso e).symm
    have h2 := (isSubquotient_rankCast_iff T h' σ L).mp h1
    have h3 := isSupercuspidalSupport_singleton T ρ0 A0 hA0 _
      (isIrreducible_rankCast T h'.symm σ hσ) h2
    rw [← isSupercuspidalSupport_rankCast_iff T h', rankCast_symm_obj] at h3
    have hs : (List.ofFn ρs : Multiset (CuspidalDatum.{uV, uF} T)) = 0 := by simp
    rw [hs, Multiset.cons_zero]
    exact h3
  | succ k =>
    subst hsum
    let ρ : Fin (k + 2) → CuspidalDatum.{uV, uF} T := Fin.cons ρ0 ρs
    let A : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank) :=
      Fin.cons (α := fun i => SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
        A0 As
    have hsum' : ∑ i, (ρ i).rank = ρ0.rank + ∑ i, (ρs i).rank := Fin.sum_univ_succ _
    let B := T.cuspidalShape ρ hsum'
    let σf : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
      fun i => (A i).obj
    have hB : B.length = k + 2 := rfl
    let e1 := T.headTailProductInductionIso B hB σf
    let P := T.cuspidalProductInduced ρs rfl As
    have hX : (T.normalizedProductInductionFunctor (B.headTailShape hB)).obj
        (T.headTailProductFactors B hB σf) =
        (generalLinearRankCast T (B.headRank_add_tailRank hB)).obj
          ((T.binaryNormalizedProductFunctor (B.headRank hB) (B.tailRank hB)).obj
            (SmoothRep.universeLift.{uF} (σf (B.headIndex hB)),
              (T.normalizedProductInductionFunctor (B.tailShape hB)).obj
                (fun j => σf (B.tailIndex hB j)))) := by
      rw [binaryNormalizedProductFunctor_obj_eq T (B.headRank_pos hB)
        (B.tailRank_pos hB) (SmoothRep.universeLift.{uF} (σf (B.headIndex hB)))
        ((T.normalizedProductInductionFunctor (B.tailShape hB)).obj
          (fun j => σf (B.tailIndex hB j)))
        (T.headTailProductFactors B hB σf) rfl rfl]
      exact normalizedProductInductionFunctor_rankCast_obj T _ _ _
    have hLP : SmoothRep.IsSubquotient
        ((T.binaryNormalizedProductFunctor ρ0.rank (∑ i, (ρs i).rank)).obj (L, τ))
        ((T.binaryNormalizedProductFunctor ρ0.rank (∑ i, (ρs i).rank)).obj (L, P)) :=
      (preservesShortExact_binaryNormalized_sectR T ρ0.rank_pos L).isSubquotient_map hτsq
    have hsq' : SmoothRep.IsSubquotient σ
        ((generalLinearRankCast T (B.headRank_add_tailRank hB)).obj
          ((T.binaryNormalizedProductFunctor (B.headRank hB) (B.tailRank hB)).obj
            (SmoothRep.universeLift.{uF} (σf (B.headIndex hB)),
              (T.normalizedProductInductionFunctor (B.tailShape hB)).obj
                (fun j => σf (B.tailIndex hB j))))) :=
      isSubquotient_trans h hLP
    have hsq : SmoothRep.IsSubquotient σ (T.cuspidalProductInduced ρ hsum' A) :=
      SmoothRep.IsSubquotient.of_iso_right hsq' (e1 ≪≫ eqToIso hX).symm
    have hrep : ∀ i, (ρ i).IsRepresentedBy (A i) := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hA0
      · exact hAs j
    refine ⟨k + 2, ρ, ?_, hsum', A, hrep, hσ, hsq⟩
    rw [List.ofFn_succ, ← Multiset.cons_coe]
    rfl

end Cons

end Langlands.Classification.SegmentHeadSupport
