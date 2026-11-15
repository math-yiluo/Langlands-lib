import Langlands.Representation.Classification.LeftCuspidalDerivative.Transitivity
import Langlands.Representation.Classification.LeftCuspidalDerivative.Product
import Langlands.Representation.Aubert.SupportGrading
import Langlands.Representation.CuspidalSupport.BinaryProductSupport
import Langlands.Representation.Classification.UnlinkedSegmentSocleProductIrreducibleProof
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Classification.SupercuspidalEmbeddingProof
import Langlands.Representation.Classification.SegmentHeadSupportCons
import Langlands.Representation.Parabolic.HeadTailProductInduction

/-!
# Powers of a supercuspidal representation and `A`-pure supports

* `cuspidalDatumOf hd A`: the cuspidal datum of an actual supercuspidal `A` of `GL_d`.
* `IsPure`: an irreducible representation is `A`-pure if its supercuspidal support is a
  multiple of the datum of `A`.
* `cuspidalPower`: the cuspidal product `A × ⋯ × A` of `K` copies; it is irreducible
  (`isIrreducible_cuspidalPower`) and `A`-pure (`isSupercuspidalSupport_cuspidalPower`).
* `isPure_right_of_isSubquotient_binaryProduct`: if an `A`-pure irreducible representation is a
  subquotient of `ρ₁ × ρ₂` with `ρ₁, ρ₂` irreducible, then `ρ₂` is `A`-pure.
* `exists_isSubrepresentation_cuspidalPower`: an `A`-pure irreducible representation of positive
  rank embeds into some `A^K`.
* `nonempty_cuspidalPowerSuccIso`: `A^(K+2) ≅ A × A^(K+1)` (after rank transport).
* `isFirstBlockConstituent_of_isPure`: `A` is a first-block Jacquet constituent of every
  `A`-pure irreducible representation of positive rank.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.LeftCuspidalDerivative

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

section Datum

/-- The cuspidal datum of an actual supercuspidal representation `A` of `GL_d`, `d > 0`. -/
def cuspidalDatumOf {d : ℕ} (hd : 0 < d)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)) :
    T.CuspidalDatum.{max uF uV, uF} :=
  letI := T.topology
  ⟨d, hd, A.isoClass⟩

theorem cuspidalDatumOf_rank {d : ℕ} (hd : 0 < d)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)) :
    (cuspidalDatumOf T hd A).rank = d := rfl

theorem cuspidalDatumOf_isRepresentedBy {d : ℕ} (hd : 0 < d)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d)) :
    (cuspidalDatumOf T hd A).IsRepresentedBy A := rfl

/-- An irreducible representation is `A`-pure: some multiple of the cuspidal datum of `A` is a
supercuspidal support of it. -/
def IsPure {d : ℕ} (hd : 0 < d)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {b : ℕ} (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)) :
    Prop :=
  ∃ j : ℕ, T.IsSupercuspidalSupport ρ (Multiset.replicate j (cuspidalDatumOf T hd A))

end Datum

section Power

variable {d : ℕ} (hd : 0 < d)
  (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))

/-- The cuspidal product `A × ⋯ × A` of `K` copies of `A`, on `GL_n` for any `n` equal to the
sum of the ranks. -/
def cuspidalPower (K : ℕ) {n : ℕ} (h : ∑ _i : Fin K, (cuspidalDatumOf T hd A).rank = n) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  T.cuspidalProductInduced (fun _ : Fin K => cuspidalDatumOf T hd A) h (fun _ => A)

/-- `A^K` is irreducible for `K > 0`: it is a product of one-term segment socles of the same
segment, whose multisegment is unlinked (Zelevinsky 1980, Theorem 4.2). -/
theorem isIrreducible_cuspidalPower (K : ℕ) (hK : 0 < K) {n : ℕ}
    (h : ∑ _i : Fin K, (cuspidalDatumOf T hd A).rank = n) :
    letI := T.topology
    (cuspidalPower T hd A K h).IsIrreducible := by
  let := T.topology
  have hn : 0 < n := by
    rw [← h]
    exact Finset.sum_pos (fun _ _ => hd) ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by omega⟩
  let D := SegmentProductDatum.ofCuspidals.{uF, uV} T (fun _ : Fin K => cuspidalDatumOf T hd A) h
    (fun _ => A)
  have hD : D.HasSegmentSocles :=
    SegmentProductDatum.ofCuspidals_hasSegmentSocles.{uF, uV} T _ h _
      (fun _ => cuspidalDatumOf_isRepresentedBy T hd A)
  have hU : D.multisegment.IsUnlinked := by
    have hmem : ∀ Δ ∈ D.multisegment, Δ = T.singletonSegment (cuspidalDatumOf T hd A) := by
      intro Δ hΔ
      change Δ ∈ ((List.ofFn D.segments : List _) : Multiset _) at hΔ
      rw [Multiset.mem_coe, List.mem_ofFn] at hΔ
      obtain ⟨i, rfl⟩ := hΔ
      rfl
    intro Δ₁ h₁ Δ₂ h₂ hlink
    rw [hmem Δ₁ h₁, hmem Δ₂ h₂] at hlink
    exact hlink.1 subset_rfl
  have hirr := unlinkedSegmentSocleProductIrreducible.{uF, max uF uV} F T n₀ D hD hU
  exact (Weil.IsomorphismInvariance.irreducible_iff
    (SmoothRep.equivOfIso (SegmentProductDatum.ofCuspidalsInducedIso.{uF, uV} T _ h _))).mp hirr

/-- `A^K` has the supercuspidal support `K · [A]`, for `K > 0`. -/
theorem isSupercuspidalSupport_cuspidalPower (K : ℕ) (hK : 0 < K) {n : ℕ}
    (h : ∑ _i : Fin K, (cuspidalDatumOf T hd A).rank = n) :
    T.IsSupercuspidalSupport (cuspidalPower T hd A K h)
      (Multiset.replicate K (cuspidalDatumOf T hd A)) := by
  let := T.topology
  refine ⟨K, fun _ => cuspidalDatumOf T hd A, ?_, h, fun _ => A,
    fun _ => cuspidalDatumOf_isRepresentedBy T hd A, isIrreducible_cuspidalPower T hd A K hK h,
    SegmentHeadSupport.isSubquotient_refl _⟩
  rw [List.ofFn_const, Multiset.coe_replicate]

theorem isPure_cuspidalPower (K : ℕ) (hK : 0 < K) {n : ℕ}
    (h : ∑ _i : Fin K, (cuspidalDatumOf T hd A).rank = n) :
    IsPure T hd A (cuspidalPower T hd A K h) :=
  ⟨K, isSupercuspidalSupport_cuspidalPower T hd A K hK h⟩

end Power

section PureProduct

variable {d : ℕ} (hd : 0 < d)
  (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))

/-- If an `A`-pure irreducible `D` is a subquotient of `ρ₁ × ρ₂` with `ρ₁, ρ₂` irreducible,
then `ρ₂` is `A`-pure. -/
theorem isPure_right_of_isSubquotient_binaryProduct {a₁ a₂ : ℕ}
    {D : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a₁ + a₂) F.Carrier)}
    (hD : letI := T.topology; D.IsIrreducible) (hDp : IsPure T hd A D)
    {ρ₁ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a₁ F.Carrier)}
    {ρ₂ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a₂ F.Carrier)}
    (hρ₁ : letI := T.topology; ρ₁.IsIrreducible) (hρ₂ : letI := T.topology; ρ₂.IsIrreducible)
    (h : letI := T.topology
      SmoothRep.IsSubquotient D ((T.binaryNormalizedProductFunctor a₁ a₂).obj (ρ₁, ρ₂))) :
    IsPure T hd A ρ₂ := by
  let := T.topology
  obtain ⟨s, hs⟩ := Aubert.SupportGrading.exists_isSupercuspidalSupport ρ₁ hρ₁
  obtain ⟨t, ht⟩ := Aubert.SupportGrading.exists_isSupercuspidalSupport ρ₂ hρ₂
  have hst := binaryProductConstituentSupport hs ht hD h
  obtain ⟨j, hj⟩ := hDp
  have heq := Aubert.SupportGrading.isSupercuspidalSupport_unique hD hst hj
  refine ⟨Multiset.card t, ?_⟩
  have ht' : t = Multiset.replicate (Multiset.card t) (cuspidalDatumOf T hd A) := by
    apply Multiset.eq_replicate_of_mem
    intro b hb
    have hb' : b ∈ s + t := Multiset.mem_add.mpr (Or.inr hb)
    rw [heq] at hb'
    exact Multiset.eq_of_mem_replicate hb'
  rw [← ht']
  exact ht

end PureProduct

section Helpers

/-- Subrepresentations pass along isomorphisms of the ambient representation. -/
theorem isSubrepresentation_of_iso {n : ℕ}
    {Z P Q : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : letI := T.topology; SmoothRep.IsSubrepresentation Z P) (e : P ≅ Q) :
    letI := T.topology; SmoothRep.IsSubrepresentation Z Q := by
  let := T.topology
  obtain ⟨f, hf⟩ := h
  exact ⟨f ≫ e.hom, fun x y hxy => hf (Derivative.LevelCalculus.iso_hom_injective e hxy)⟩

/-- Normalized product induction is congruent in the block shape. -/
theorem normalizedProductInductionFunctor_obj_congr {n : ℕ} {B B' : BlockShape n}
    (h : B = B')
    (X : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (Y : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B'.size i) F.Carrier))
    (hXY : HEq X Y) :
    letI := T.topology
    (T.normalizedProductInductionFunctor B).obj X =
      (T.normalizedProductInductionFunctor B').obj Y := by
  subst h
  cases hXY
  rfl

/-- The rank-cast functor acts on objects as `castRank`. -/
theorem generalLinearRankCast_obj_eq {r s : ℕ} (h : r = s)
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    (Derivative.generalLinearRankCast T h).obj X = T.castRank h X := by
  subst h
  rfl

/-- If an irreducible `Z` embeds into `X × σ` (after the rank transport `a + k = m`) with `X`
irreducible and `a, k > 0`, then `X` is a first-block Jacquet constituent of `Z`
(Frobenius reciprocity). -/
theorem isFirstBlockConstituent_of_isSubrepresentation_binary {a k m : ℕ} (ha : 0 < a)
    (hk : 0 < k) (h : a + k = m)
    {Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hZ : letI := T.topology; Z.IsIrreducible)
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (hX : letI := T.topology; X.representation.IsIrreducible)
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (hsub : letI := T.topology; SmoothRep.IsSubrepresentation Z
      (T.castRank h ((T.binaryNormalizedProductFunctor a k).obj (X, σ)))) :
    BinaryGeometricPieces.IsFirstBlockConstituent.{uF, uV} F T Z X := by
  let := T.topology
  have hZnt : Nontrivial Z := nontrivial_of_isIrreducible hZ
  obtain ⟨g, hg⟩ := exists_jacquet_ne_zero_of_isSubrepresentation F T ha hk h Z X σ hZnt hsub
  exact Or.inr ⟨k, ha, hk, h, isSubquotient_firstBlock_of_ne_zero
    (H := fun i : Fin 2 => GeneralLinear ((BlockShape.ofPair a k ha hk h).size i) F.Carrier)
    _ _ hX g hg⟩

end Helpers

section Embedding

variable {d : ℕ} (hd : 0 < d)
  (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))

/-- An `A`-pure irreducible representation of positive rank embeds into some `A^K`. -/
theorem exists_isSubrepresentation_cuspidalPower {b : ℕ} (hb : 0 < b)
    {ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)}
    (hρ : letI := T.topology; ρ.IsIrreducible) (hp : IsPure T hd A ρ) :
    ∃ (K : ℕ) (h : ∑ _i : Fin K, (cuspidalDatumOf T hd A).rank = b),
      letI := T.topology
      SmoothRep.IsSubrepresentation ρ (cuspidalPower T hd A K h) := by
  let := T.topology
  obtain ⟨K, κs, hsub⟩ := glSupercuspidalEmbedding.{max uF uV, uF} p F T b hb ρ hρ
  obtain ⟨j, hj⟩ := hp
  have hs : T.IsSupercuspidalSupport ρ (List.ofFn κs : Multiset _) :=
    ⟨K, κs, rfl, hsub.isCuspidalConstituent⟩
  have heq := Aubert.SupportGrading.isSupercuspidalSupport_unique hρ hs hj
  have hκ : κs = fun _ => cuspidalDatumOf T hd A := by
    funext i
    have hm : κs i ∈ (List.ofFn κs : Multiset _) :=
      Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)
    rw [heq] at hm
    exact Multiset.eq_of_mem_replicate hm
  subst hκ
  obtain ⟨h, B, hB, hsub'⟩ := hsub
  have hsub'' := (T.isCuspidalSubrepresentation_iff _ ρ h (fun _ => A)
    (fun _ => cuspidalDatumOf_isRepresentedBy T hd A)).mp ⟨h, B, hB, hsub'⟩
  obtain ⟨-, f, hf⟩ := hsub''
  exact ⟨K, h, SmoothRep.ofHom f, hf⟩

/-- `A^(K+2) ≅ A × A^(K+1)`, after the rank transport `d + m = n`. -/
theorem nonempty_cuspidalPowerSuccIso (K : ℕ) {m n : ℕ}
    (hm : ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank = m)
    (h : ∑ _i : Fin (K + 2), (cuspidalDatumOf T hd A).rank = n) (hn : d + m = n) :
    letI := T.topology
    Nonempty (cuspidalPower T hd A (K + 2) h ≅
      T.castRank hn ((T.binaryNormalizedProductFunctor d m).obj
        (A.obj, cuspidalPower T hd A (K + 1) hm))) := by
  let := T.topology
  subst hm
  let κ := cuspidalDatumOf T hd A
  let B := T.cuspidalShape (fun _ : Fin (K + 2) => κ) h
  have hB : B.length = K + 2 := rfl
  let σf : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
    fun _ => A.obj
  let e1 := T.headTailProductInductionIso B hB σf
  have hX : (T.normalizedProductInductionFunctor (B.headTailShape hB)).obj
      (T.headTailProductFactors B hB σf) =
      (Derivative.generalLinearRankCast T (B.headRank_add_tailRank hB)).obj
        ((T.binaryNormalizedProductFunctor (B.headRank hB) (B.tailRank hB)).obj
          (SmoothRep.universeLift.{uF} (σf (B.headIndex hB)),
            (T.normalizedProductInductionFunctor (B.tailShape hB)).obj
              (fun j => σf (B.tailIndex hB j)))) := by
    rw [SegmentHeadSupport.binaryNormalizedProductFunctor_obj_eq T (B.headRank_pos hB)
      (B.tailRank_pos hB) (SmoothRep.universeLift.{uF} (σf (B.headIndex hB)))
      ((T.normalizedProductInductionFunctor (B.tailShape hB)).obj
        (fun j => σf (B.tailIndex hB j)))
      (T.headTailProductFactors B hB σf) rfl rfl]
    exact SegmentHeadSupport.normalizedProductInductionFunctor_rankCast_obj T _ _ _
  let e2 : SmoothRep.universeLift.{uF} A.obj ≅ A.obj :=
    SmoothRep.mkIso (SmoothRep.universeLiftEquiv.{uF} A.obj).symm
  have hshape : B.tailShape hB = T.cuspidalShape (fun _ : Fin (K + 1) => κ) rfl := rfl
  have htail : (T.normalizedProductInductionFunctor (B.tailShape hB)).obj
      (fun j => σf (B.tailIndex hB j)) = cuspidalPower T hd A (K + 1) rfl :=
    normalizedProductInductionFunctor_obj_congr T hshape _ _ HEq.rfl
  let e3 := (Derivative.generalLinearRankCast T (B.headRank_add_tailRank hB)).mapIso
    ((T.binaryNormalizedProductFunctor d (∑ _i : Fin (K + 1), κ.rank)).mapIso
      (Iso.prod e2 (eqToIso htail)))
  refine ⟨e1 ≪≫ eqToIso hX ≪≫ e3 ≪≫ eqToIso ?_⟩
  exact generalLinearRankCast_obj_eq T _ _

/-- `A^1 ≅ A`, after the rank transport `d = n`. -/
def cuspidalPowerOneEquiv {n : ℕ} (h : ∑ _i : Fin 1, (cuspidalDatumOf T hd A).rank = n)
    (hn : d = n) :
    letI := T.topology
    (cuspidalPower T hd A 1 h).representation.Equiv (T.castRank hn A.obj).representation :=
  letI := T.topology
  let B := T.cuspidalShape (fun _ : Fin 1 => cuspidalDatumOf T hd A) h
  (T.singleBlockNormalizedProductEquiv B rfl (fun _ => A.obj.representation)
    (fun _ => A.obj.isSmooth) ⟨0, Nat.one_pos⟩).trans
      (T.castRankEquiv (B.singleBlock_size rfl ⟨0, Nat.one_pos⟩) A.obj)

/-- **`A` is a first-block constituent of every `A`-pure irreducible representation of
positive rank.** -/
theorem isFirstBlockConstituent_of_isPure {b : ℕ} (hb : 0 < b)
    {ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)}
    (hρ : letI := T.topology; ρ.IsIrreducible) (hp : IsPure T hd A ρ) :
    BinaryGeometricPieces.IsFirstBlockConstituent.{uF, uV} F T ρ A.obj := by
  let := T.topology
  obtain ⟨K, h, hsub⟩ := exists_isSubrepresentation_cuspidalPower T hd A hb hρ hp
  match K, h, hsub with
  | 0, h, _ =>
    exfalso
    simp at h
    omega
  | 1, h, hsub =>
    have hn : d = b := by
      rw [← h, Fin.sum_univ_one]
      rfl
    let e := cuspidalPowerOneEquiv T hd A h hn
    have hP : (cuspidalPower T hd A 1 h).representation.IsIrreducible :=
      isIrreducible_cuspidalPower T hd A 1 Nat.one_pos h
    have hsq : WeylBranchPieces.IsSubquotient (cuspidalPower T hd A 1 h).representation
        ρ.representation :=
      SmoothRep.isSubquotient_iff_representation.mp hsub.isSubquotient
    obtain ⟨e'⟩ := CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient hP hρ hsq
    -- `ρ ≃ castRank hn A`
    have e'' : ρ.representation.Equiv (T.castRank hn A.obj).representation := e'.symm.trans e
    refine Or.inl ⟨hn.symm, ?_⟩
    clear_value e
    subst hn
    exact WeylBranchPieces.IsSubquotient.of_equiv e''
  | K + 2, h, hsub =>
    have hm : 0 < ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank :=
      Finset.sum_pos (fun _ _ => hd) ⟨0, Finset.mem_univ _⟩
    have hn : d + ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank = b := by
      rw [← h, Fin.sum_univ_succ (n := K + 1)]
      rfl
    obtain ⟨e⟩ := nonempty_cuspidalPowerSuccIso T hd A K rfl h hn
    exact isFirstBlockConstituent_of_isSubrepresentation_binary T hd hm hn hρ A.property.1 _
      (isSubrepresentation_of_iso T hsub e)

end Embedding

end Langlands.Classification.LeftCuspidalDerivative
