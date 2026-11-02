import Langlands.Representation.Classification.SegmentProductSplit
import Langlands.Representation.Induction.EmptyProductUnit
import Mathlib.LinearAlgebra.Dimension.Free

/-! Ordered datum constructors and the actual rank-zero product boundary. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.SegmentProductOrderedAssembly

open GeneralLinear PadicField.TopologicalData Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Equality transport of a smooth object is the usual matrix rank reindexing. -/
def rankCastEquiv {a b : ℕ} (h : a = b)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    Representation.Equiv (A.representation.comp
      (GeneralLinear.reindex (R := F.Carrier) (finCongr h)).symm.toMonoidHom)
      ((generalLinearRankCast T h).obj A).representation := by
  letI := T.topology
  subst b
  rw [GeneralLinear.reindex_finCongr_rfl]
  exact Representation.Equiv.mk (LinearEquiv.refl ℂ A) (fun _ => rfl)

/-- The inverse rank presentation uses the forward matrix reindexing. -/
def rankCastSymmEquiv {a b : ℕ} (h : a = b)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    Representation.Equiv (A.representation.comp
      (GeneralLinear.reindex (R := F.Carrier) (finCongr h)).toMonoidHom)
      ((generalLinearRankCast T h.symm).obj A).representation := by
  letI := T.topology
  subst b
  rw [GeneralLinear.reindex_finCongr_rfl]
  exact Representation.Equiv.mk (LinearEquiv.refl ℂ A) (fun _ => rfl)

/-- Every one-dimensional representation of `GL_0` is the actual binary unit. -/
theorem nonempty_iso_unit
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier))
    (hA : letI := T.topology; Module.finrank ℂ A = 1) :
    letI := T.topology
    Nonempty (A ≅ T.binaryProductUnit.{uF, uV}) := by
  let _ := T.topology
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hA
  refine ⟨SmoothRep.mkIso (Representation.Equiv.mk
    (e.symm.trans (ULift.moduleEquiv (R := ℂ) (M := ℂ)).symm) ?_)⟩
  intro g
  rw [GeneralLinear.representation_apply_of_rank_eq_zero rfl A.representation g,
    GeneralLinear.representation_apply_of_rank_eq_zero rfl
      (T.binaryProductUnit.{uF, uV}).representation g]
  rfl

/-- The left binary unit can be removed without retaining a carrier lift. -/
def leftUnitIso {b : ℕ}
    (B : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    (T.binaryNormalizedProductFunctor 0 b).obj (T.binaryProductUnit, B) ≅
      (generalLinearRankCast T (Nat.zero_add b).symm).obj B := by
  letI := T.topology
  exact SmoothRep.mkIso (((T.binaryProductLeftUnitEquiv B).trans
    (BinaryTensor.liftEquiv _).symm).trans (rankCastSymmEquiv T (Nat.zero_add b) B))

/-- The right binary unit can be removed without retaining a carrier lift. -/
def rightUnitIso {a : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    (T.binaryNormalizedProductFunctor a 0).obj (A, T.binaryProductUnit) ≅
      (generalLinearRankCast T (Nat.add_zero a).symm).obj A := by
  letI := T.topology
  exact SmoothRep.mkIso (((T.binaryProductRightUnitEquiv A).trans
    (BinaryTensor.liftEquiv _).symm).trans (rankCastSymmEquiv T (Nat.add_zero a) A))

/-- A supplied rank-zero line can be omitted on the left of a binary product. -/
theorem nonempty_iso_omit_left_line {b : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
    (B : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hA : letI := T.topology; Module.finrank ℂ A = 1) :
    letI := T.topology
    Nonempty ((T.binaryNormalizedProductFunctor 0 b).obj (A, B) ≅
      (generalLinearRankCast T (Nat.zero_add b).symm).obj B) := by
  let _ := T.topology
  obtain ⟨e⟩ := nonempty_iso_unit T A hA
  exact ⟨(T.binaryNormalizedProductFunctor 0 b).mapIso (Iso.prod e (Iso.refl B)) ≪≫
    leftUnitIso T B⟩

variable {T}

/-- Change only the numerical ambient rank of a datum. -/
def rankCast {a b : ℕ} (h : a = b) (d : SegmentProductDatum.{uV, uF} T a) :
    SegmentProductDatum.{uV, uF} T b where
  length := d.length
  segments := d.segments
  degree_sum := d.degree_sum.trans h
  blocks := d.blocks

@[simp] theorem rankCast_segments {a b : ℕ} (h : a = b)
    (d : SegmentProductDatum.{uV, uF} T a) :
    (rankCast h d).segments = d.segments := rfl

theorem rankCast_hasSegmentSocles {a b : ℕ} (h : a = b)
    (d : SegmentProductDatum.{uV, uF} T a) (hd : d.HasSegmentSocles) :
    (rankCast h d).HasSegmentSocles := hd

theorem rankCast_induced {a b : ℕ} (h : a = b)
    (d : SegmentProductDatum.{uV, uF} T a) :
    letI := T.topology
    (rankCast h d).induced = (generalLinearRankCast T h).obj d.induced := by
  subst b
  rfl

/-- The empty ordered datum. -/
def empty : SegmentProductDatum.{uV, uF} T 0 where
  length := 0
  segments := Fin.elim0
  degree_sum := by simp
  blocks i := i.elim0

@[simp] theorem empty_segments :
    List.ofFn (empty : SegmentProductDatum.{uV, uF} T 0).segments = [] := rfl

theorem empty_hasSegmentSocles : (empty : SegmentProductDatum.{uV, uF} T 0).HasSegmentSocles :=
  fun i => i.elim0

/-- Every datum on `GL_0` induces the actual one-dimensional unit. -/
def zeroDatumUnitIso (d : SegmentProductDatum.{uV, uF} T 0) :
    letI := T.topology
    d.induced ≅ T.binaryProductUnit.{uF, max uF uV} :=
  T.emptyProductUnitIso d.shape d.blocks

theorem finrank_zeroDatum (d : SegmentProductDatum.{uV, uF} T 0) :
    letI := T.topology
    Module.finrank ℂ d.induced = 1 := by
  let _ := T.topology
  exact (SmoothRep.equivOfIso (zeroDatumUnitIso d)).toLinearEquiv.finrank_eq.trans
    (T.finrank_binaryProductUnit)

/-- Prepend one supplied segment and its actual block, preserving the tail order. -/
def cons {n : ℕ} (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (d : SegmentProductDatum.{uV, uF} T n) :
    SegmentProductDatum.{uV, uF} T (Δ.degree + n) where
  length := d.length + 1
  segments := Fin.cons Δ d.segments
  degree_sum := by
    rw [Fin.sum_univ_succ]
    simpa using congrArg (Δ.degree + ·) d.degree_sum
  blocks := Fin.cases A d.blocks

@[simp] theorem cons_segments {n : ℕ} (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (d : SegmentProductDatum.{uV, uF} T n) :
    List.ofFn (cons Δ A d).segments = Δ :: List.ofFn d.segments :=
  List.ofFn_cons _ _

theorem cons_hasSegmentSocles {n : ℕ} (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (d : SegmentProductDatum.{uV, uF} T n)
    (hA : T.IsSegmentSocle Δ A) (hd : d.HasSegmentSocles) :
    (cons Δ A d).HasSegmentSocles := Fin.cases hA hd

/-- A one-entry datum is its actual block, along the exact degree equality. -/
def singletonIso {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n)
    (h : d.length = 1) (i : Fin d.length) :
    letI := T.topology
    d.induced ≅ (generalLinearRankCast T (d.shape.singleBlock_size h i)).obj (d.blocks i) := by
  letI := T.topology
  exact SmoothRep.mkIso ((T.singleBlockNormalizedProductEquiv d.shape h
    (fun j => (d.blocks j).representation) (fun j => (d.blocks j).isSmooth) i).trans
      (rankCastEquiv T (d.shape.singleBlock_size h i) (d.blocks i)))

/-- Prepending a block realizes the binary product, including an empty tail. -/
theorem nonempty_cons_iso_binary {n : ℕ} (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (d : SegmentProductDatum.{uV, uF} T n) :
    letI := T.topology
    Nonempty ((cons Δ A d).induced ≅
      (T.binaryNormalizedProductFunctor Δ.degree n).obj (A, d.induced)) := by
  let _ := T.topology
  rcases d with ⟨r, segments, hsum, blocks⟩
  cases r with
  | zero =>
    have hn : n = 0 := by simpa using hsum.symm
    subst n
    let d : SegmentProductDatum.{uV, uF} T 0 := ⟨0, segments, by simp, blocks⟩
    have eS : (cons Δ A d).induced ≅ A :=
      singletonIso (cons Δ A d) rfl (0 : Fin 1)
    have eB : (T.binaryNormalizedProductFunctor Δ.degree 0).obj (A, d.induced) ≅ A :=
      (T.binaryNormalizedProductFunctor Δ.degree 0).mapIso
        (Iso.prod (Iso.refl A) (zeroDatumUnitIso d)) ≪≫ rightUnitIso T A
    exact ⟨eS ≪≫ eB.symm⟩
  | succ r =>
    subst n
    exact SegmentProductSplit.nonempty_iso_binary
      (cons Δ A ⟨r + 1, segments, rfl, blocks⟩) rfl

/-- The original ordered list is exactly the first segment followed by the tail. -/
theorem segments_eq_head_cons_tail {n k : ℕ} (d : SegmentProductDatum.{uV, uF} T n)
    (h : d.length = k + 2) :
    List.ofFn d.segments = d.segments (d.shape.headIndex h) ::
      List.ofFn (SegmentProductSplit.tail d h).segments := by
  rcases d with ⟨r, segments, hsum, blocks⟩
  dsimp at h
  subst r
  exact List.ofFn_succ

/-- The sum of base ranks splits without changing the order or multiplicities. -/
theorem rank_sum_eq_head_add_tail {n k : ℕ} (d : SegmentProductDatum.{uV, uF} T n)
    (h : d.length = k + 2) :
    (∑ i, (d.segments i).rank) =
      (d.segments (d.shape.headIndex h)).rank +
        ∑ i, ((SegmentProductSplit.tail d h).segments i).rank := by
  rcases d with ⟨r, segments, hsum, blocks⟩
  dsimp at h
  subst r
  exact Fin.sum_univ_succ _

end Langlands.Classification.SegmentProductOrderedAssembly
