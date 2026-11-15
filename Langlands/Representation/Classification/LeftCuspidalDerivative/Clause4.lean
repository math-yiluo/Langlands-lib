import Langlands.Representation.Classification.LeftCuspidalDerivative.PowerIso

/-!
# Uniqueness: irreducible subrepresentations of `A^K × S`

For a supercuspidal `A` and an irreducible left `A`-reduced `S`, any two irreducible
subrepresentations of `A^K × S = powerProduct F T A K S` are isomorphic (`uniqueness`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.LeftCuspidalDerivative

open GeneralLinear PadicField.TopologicalData

universe uF uV uG uW

section Irreducible

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- An irreducible subrepresentation of an irreducible smooth representation is isomorphic to
it. -/
theorem nonempty_iso_of_isSubrepresentation_of_isIrreducible
    {π X : SmoothRep.{0, uG, uW} ℂ G} (hπ : π.IsIrreducible) (hX : X.IsIrreducible)
    (hs : SmoothRep.IsSubrepresentation π X) : Nonempty (π ≅ X) := by
  obtain ⟨j, hj⟩ := hs
  have hπ' : π.representation.IsIrreducible := hπ
  have hX' : X.representation.IsIrreducible := hX
  have hnt : Nontrivial π := nontrivial_of_isIrreducible hπ
  have hj0 : SmoothRep.hom j ≠ 0 := by
    intro h0
    obtain ⟨x, y, hxy⟩ := exists_pair_ne π
    apply hxy
    apply hj
    rw [h0]
    rfl
  obtain ⟨e⟩ := nonempty_equiv_of_ne_zero (SmoothRep.hom j) hj0
  exact ⟨SmoothRep.mkIso e⟩

end Irreducible

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- `nonempty_iso_of_isSubrepresentation_binaryProduct` after a rank transport. -/
theorem nonempty_iso_of_isSubrepresentation_castRank_binaryProduct {d a m N : ℕ} (hd : 0 < d)
    (ha : 0 < a) (hm : 0 < m)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible) (hp : IsPure T hd A 𝔄)
    {E : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hE : letI := T.topology; E.IsIrreducible) (hr : LeftReduced F T A E) (h : a + m = N)
    {π π' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hπ : letI := T.topology; π.IsIrreducible) (hπ' : letI := T.topology; π'.IsIrreducible)
    (hs : letI := T.topology; SmoothRep.IsSubrepresentation π
      (T.castRank h ((T.binaryNormalizedProductFunctor a m).obj (𝔄, E))))
    (hs' : letI := T.topology; SmoothRep.IsSubrepresentation π'
      (T.castRank h ((T.binaryNormalizedProductFunctor a m).obj (𝔄, E)))) :
    letI := T.topology
    Nonempty (π ≅ π') := by
  subst h
  exact nonempty_iso_of_isSubrepresentation_binaryProduct F T hd ha hm A h𝔄 hp hE hr
    hπ hπ' hs hs'

/-- **Clause 4 (uniqueness).** If `S` is irreducible and left `A`-reduced, any two irreducible
subrepresentations of `A^K × S` are isomorphic. -/
theorem uniqueness {d : ℕ}
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    (K m : ℕ) (S : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (powerRank d K m) F.Carrier))
    (hS : letI := T.topology; S.IsIrreducible) (hSr : LeftReduced F T A S)
    (hπ : letI := T.topology; π.IsIrreducible) (hπ' : letI := T.topology; π'.IsIrreducible)
    (hs : letI := T.topology; SmoothRep.IsSubrepresentation π (powerProduct F T A K S))
    (hs' : letI := T.topology; SmoothRep.IsSubrepresentation π' (powerProduct F T A K S)) :
    letI := T.topology
    Nonempty (π ≅ π') := by
  let := T.topology
  cases K with
  | zero =>
    obtain ⟨e⟩ := nonempty_iso_of_isSubrepresentation_of_isIrreducible hπ hS hs
    obtain ⟨e'⟩ := nonempty_iso_of_isSubrepresentation_of_isIrreducible hπ' hS hs'
    exact ⟨e ≪≫ e'.symm⟩
  | succ K =>
    obtain rfl | hd := Nat.eq_zero_or_pos d
    · exfalso
      have hsub := subsingleton_of_leftReduced_rankZero F T A S
        (SmoothRep.hasFiniteLength_of_isIrreducible hS) hSr
      have hnt : Nontrivial S := nontrivial_of_isIrreducible hS
      exact (not_nontrivial_iff_subsingleton.mpr hsub) hnt
    have ha : 0 < ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank :=
      Finset.sum_pos (fun _ _ => hd) ⟨0, Finset.mem_univ _⟩
    have h𝔄 := isIrreducible_cuspidalPower T hd A (K + 1) K.succ_pos rfl
    obtain rfl | hm := Nat.eq_zero_or_pos m
    · have hP : ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank = powerRank d (K + 1) 0 := by
        rw [sum_cuspidalDatumOf_rank, powerRank_eq]
        ring
      obtain ⟨e⟩ := nonempty_powerProduct_rankZero_iso F T hd A S hS K rfl hP
      have hirr := T.isIrreducible_castRank hP _ h𝔄
      obtain ⟨e1⟩ := nonempty_iso_of_isSubrepresentation_of_isIrreducible hπ hirr
        (isSubrepresentation_of_iso T hs e)
      obtain ⟨e1'⟩ := nonempty_iso_of_isSubrepresentation_of_isIrreducible hπ' hirr
        (isSubrepresentation_of_iso T hs' e)
      exact ⟨e1 ≪≫ e1'.symm⟩
    · have hP : (∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank) + m =
          powerRank d (K + 1) m := by
        rw [sum_cuspidalDatumOf_rank, powerRank_eq]
        ring
      obtain ⟨e⟩ := nonempty_powerProduct_iso F T hd A hm S K rfl hP
      exact nonempty_iso_of_isSubrepresentation_castRank_binaryProduct F T hd ha hm A h𝔄
        (isPure_cuspidalPower T hd A (K + 1) K.succ_pos rfl) hS hSr hP hπ hπ'
        (isSubrepresentation_of_iso T hs e) (isSubrepresentation_of_iso T hs' e)

end Langlands.Classification.LeftCuspidalDerivative
