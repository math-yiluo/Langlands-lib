import Langlands.Representation.Archimedean.RealCharacterInducedWeightZero
import Langlands.Representation.Archimedean.RealCharacterPairFiltration

/-!
# Adjacent filtrations involving an induction block of weight zero

Two character steps can be fused into one step past an induction block of weight zero.
The steps and the conclusion allow arbitrary surrounding lists. Four applications of the
published character-pair filtration therefore treat two induction blocks of weight zero.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealStandardFiltration

namespace RealInducedPairWeightZero

/-- The first character in the expansion of an induction block of weight zero. -/
abbrev first (d : ComplexCharacterData) : RealCharacterData :=
  RealJacquetFrobenius.charData 1 d.exponent

/-- The second character in the expansion of an induction block of weight zero. -/
abbrev second (d : ComplexCharacterData) : RealCharacterData :=
  RealJacquetFrobenius.charData 0 d.exponent

@[simp]
theorem first_exponent (d : ComplexCharacterData) : (first d).exponent = d.exponent := rfl

@[simp]
theorem second_exponent (d : ComplexCharacterData) : (second d).exponent = d.exponent := rfl

/-- Fuse two adjacent steps that move a block past the characters of a zero-weight block
on its right. -/
theorem fuse_right (n : ℕ) (pre post : List RealBlock) (x : RealBlock)
    (d : ComplexCharacterData) (hw : d.weight = 0)
    (h1 : RealAdjacentFiltration n pre (.character (second d) :: post)
      x (.character (first d)))
    (h2 : RealAdjacentFiltration n (pre ++ [.character (first d)]) post
      x (.character (second d))) :
    RealAdjacentFiltration n pre post x (.induced d) := by
  have hexp : realBlockExpand (.induced d) =
      [.character (first d), .character (second d)] := by
    simp [realBlockExpand, hw, first, second]
  have hKF : KF n (pre ++ x :: .character (first d) :: .character (second d) :: post) =
      KF n (pre ++ x :: .induced d :: post) := by
    have h := kf_append_expand n (pre ++ [x]) post (.induced d)
    simpa [hexp, List.append_assoc] using h.symm
  have hKF' : KF n (pre ++ .induced d :: x :: post) =
      KF n (pre ++ .character (first d) :: .character (second d) :: x :: post) := by
    simpa [hexp] using kf_append_expand n pre (x :: post) (.induced d)
  have hsupp : realExponentSupport [x, .induced d] =
      realBlockSupport x ++ [d.exponent, d.exponent] := by
    simp [realExponentSupport, realBlockSupport, hw]
  have hsupp1 : realExponentSupport [x, .character (first d)] =
      realBlockSupport x ++ [d.exponent] := by
    simp [realExponentSupport, realBlockSupport]
  have hsupp2 : realExponentSupport [x, .character (second d)] =
      realBlockSupport x ++ [d.exponent] := by
    simp [realExponentSupport, realBlockSupport]
  have hwD : realWeightSquareSum [x, .induced d] = realBlockWeightSquare x := by
    simp [realWeightSquareSum, realBlockWeightSquare, hw]
  rw [realAdjacentFiltration_iff]
  have F1 := (realAdjacentFiltration_iff _ _ _ _ _).1 h1
  refine (F1.bind fun es hes => ?_).congr hKF
  obtain ⟨ws, rfl, hws⟩ := hes
  rcases hws with rfl | ⟨hperm, hlt⟩
  · have F2 := (realAdjacentFiltration_iff _ _ _ _ _).1 h2
    simp only [List.append_assoc, List.cons_append, List.nil_append] at F2 ⊢
    refine F2.of_eq_pieces fun es hes => ?_
    obtain ⟨ws', rfl, hws'⟩ := hes
    rcases hws' with rfl | ⟨hperm', hlt'⟩
    · exact ⟨pre ++ .induced d :: x :: post,
        ⟨[.induced d, x], by simp, Or.inl rfl⟩, by
          simpa [List.append_assoc] using hKF'⟩
    · refine ⟨_, ⟨.character (first d) :: ws', by simp [List.append_assoc],
          Or.inr ⟨?_, ?_⟩⟩, rfl⟩
      · rw [hsupp2] at hperm'
        rw [hsupp]
        have hcomm : ([d.exponent] ++ (realBlockSupport x ++ [d.exponent])).Perm
            ((realBlockSupport x ++ [d.exponent]) ++ [d.exponent]) :=
          List.perm_append_comm
        have hp := (hperm'.cons d.exponent).trans hcomm
        simpa [realExponentSupport, realBlockSupport, List.append_assoc] using hp
      · rw [hwD]
        simpa [realWeightSquareSum, realBlockWeightSquare] using hlt'
  · refine HasFiltration.self
      ⟨ws ++ [.character (second d)], by simp, Or.inr ⟨?_, ?_⟩⟩
    · rw [hsupp1] at hperm
      rw [hsupp, realExponentSupport_append]
      simpa [realExponentSupport, realBlockSupport, List.append_assoc] using
        hperm.append_right [d.exponent]
    · rw [hwD, realWeightSquareSum_append]
      simpa [realWeightSquareSum, realBlockWeightSquare] using hlt

/-- Fuse two adjacent steps that move the characters of a zero-weight block past a block
on its right. -/
theorem fuse_left (n : ℕ) (pre post : List RealBlock) (d : ComplexCharacterData)
    (y : RealBlock) (hw : d.weight = 0)
    (h1 : RealAdjacentFiltration n (pre ++ [.character (first d)]) post
      (.character (second d)) y)
    (h2 : RealAdjacentFiltration n pre (.character (second d) :: post)
      (.character (first d)) y) :
    RealAdjacentFiltration n pre post (.induced d) y := by
  have hexp : realBlockExpand (.induced d) =
      [.character (first d), .character (second d)] := by
    simp [realBlockExpand, hw, first, second]
  have hKF : KF n ((pre ++ [.character (first d)]) ++ .character (second d) :: y :: post) =
      KF n (pre ++ .induced d :: y :: post) := by
    simpa [hexp, List.append_assoc] using
      (kf_append_expand n pre (y :: post) (.induced d)).symm
  have hKF' : KF n (pre ++ y :: .induced d :: post) =
      KF n (pre ++ y :: .character (first d) :: .character (second d) :: post) := by
    simpa [hexp, List.append_assoc] using
      kf_append_expand n (pre ++ [y]) post (.induced d)
  have hsupp : realExponentSupport [.induced d, y] =
      d.exponent :: d.exponent :: realBlockSupport y := by
    simp [realExponentSupport, realBlockSupport, hw]
  have hsupp1 : realExponentSupport [.character (second d), y] =
      d.exponent :: realBlockSupport y := by
    simp [realExponentSupport, realBlockSupport]
  have hsupp2 : realExponentSupport [.character (first d), y] =
      d.exponent :: realBlockSupport y := by
    simp [realExponentSupport, realBlockSupport]
  have hwD : realWeightSquareSum [.induced d, y] = realBlockWeightSquare y := by
    simp [realWeightSquareSum, realBlockWeightSquare, hw]
  rw [realAdjacentFiltration_iff]
  have F1 := (realAdjacentFiltration_iff _ _ _ _ _).1 h1
  refine (F1.bind fun es hes => ?_).congr hKF
  obtain ⟨ws, rfl, hws⟩ := hes
  rcases hws with rfl | ⟨hperm, hlt⟩
  · have F2 := (realAdjacentFiltration_iff _ _ _ _ _).1 h2
    simp only [List.append_assoc, List.cons_append, List.nil_append] at F2 ⊢
    refine F2.of_eq_pieces fun es hes => ?_
    obtain ⟨ws', rfl, hws'⟩ := hes
    rcases hws' with rfl | ⟨hperm', hlt'⟩
    · exact ⟨pre ++ y :: .induced d :: post,
        ⟨[y, .induced d], by simp, Or.inl rfl⟩, by
          simpa [List.append_assoc] using hKF'⟩
    · refine ⟨_, ⟨ws' ++ [.character (second d)], by simp, Or.inr ⟨?_, ?_⟩⟩, rfl⟩
      · rw [hsupp2] at hperm'
        rw [hsupp, realExponentSupport_append]
        have hp := (hperm'.append_right [d.exponent]).trans
          (List.perm_append_comm.cons d.exponent)
        simpa [realExponentSupport, realBlockSupport] using hp
      · rw [hwD, realWeightSquareSum_append]
        simpa [realWeightSquareSum, realBlockWeightSquare] using hlt'
  · refine HasFiltration.self
      ⟨.character (first d) :: ws, by simp [List.append_assoc], Or.inr ⟨?_, ?_⟩⟩
    · rw [hsupp1] at hperm
      rw [hsupp]
      simpa [realExponentSupport, realBlockSupport] using hperm.cons d.exponent
    · rw [hwD]
      simpa [realWeightSquareSum, realBlockWeightSquare] using hlt

attribute [local irreducible] RealAdjacentFiltration

set_option maxHeartbeats 800000 in
/-- Two induction blocks of weight zero have the adjacent filtration, in arbitrary
surrounding lists. All four character steps are supplied by the published character-pair
filtration theorem. -/
theorem both_zero (n : ℕ) (pre post : List RealBlock) (d e : ComplexCharacterData)
    (hd : d.weight = 0) (he : e.weight = 0)
    (hrank : realRank (pre ++ .induced d :: .induced e :: post) = n)
    (hlt : realBlockExponent (.induced d) < realBlockExponent (.induced e)) :
    RealAdjacentFiltration n pre post (.induced d) (.induced e) := by
  have h11 : RealAdjacentFiltration n (pre ++ [.character (first d)])
      (.character (second e) :: post) (.character (second d)) (.character (first e)) :=
    realCharacterPairFiltration n (pre ++ [.character (first d)])
      (.character (second e) :: post) (second d) (first e) (by
      simp only [realRank, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, RealBlock.rank] at hrank ⊢
      omega) hlt
  have h12 : RealAdjacentFiltration n pre
      (.character (second d) :: .character (second e) :: post)
      (.character (first d)) (.character (first e)) :=
    realCharacterPairFiltration n pre
      (.character (second d) :: .character (second e) :: post) (first d) (first e) (by
      simp only [realRank, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons, RealBlock.rank] at hrank ⊢
      omega) hlt
  have h1 : RealAdjacentFiltration n pre (.character (second e) :: post)
      (.induced d) (.character (first e)) :=
    fuse_left n pre (.character (second e) :: post) d (.character (first e)) hd h11 h12
  have h21 : RealAdjacentFiltration n
      ((pre ++ [.character (first e)]) ++ [.character (first d)]) post
      (.character (second d)) (.character (second e)) :=
    realCharacterPairFiltration n
      ((pre ++ [.character (first e)]) ++ [.character (first d)]) post (second d) (second e) (by
      simp only [realRank, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, RealBlock.rank] at hrank ⊢
      omega) hlt
  have h22 : RealAdjacentFiltration n (pre ++ [.character (first e)])
      (.character (second d) :: post) (.character (first d)) (.character (second e)) :=
    realCharacterPairFiltration n (pre ++ [.character (first e)])
      (.character (second d) :: post) (first d) (second e) (by
      simp only [realRank, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, RealBlock.rank] at hrank ⊢
      omega) hlt
  have h2 : RealAdjacentFiltration n (pre ++ [.character (first e)]) post
      (.induced d) (.character (second e)) :=
    fuse_left n (pre ++ [.character (first e)]) post d (.character (second e)) hd h21 h22
  exact fuse_right n pre post (.induced d) e he h1 h2

end RealInducedPairWeightZero

end Langlands.Archimedean
