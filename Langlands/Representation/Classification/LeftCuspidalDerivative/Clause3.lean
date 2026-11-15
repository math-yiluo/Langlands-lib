import Langlands.Representation.Classification.LeftCuspidalDerivative.Comparison
import Langlands.Representation.Aubert.BinaryProductExactnessProof

/-!
# Comparison: from `A^K × Y` to `A^K × S`

If an irreducible `π` embeds into `A^K × Y`, where `Y` is finite-length, left `A`-reduced and
every irreducible subrepresentation of `Y` is isomorphic to an irreducible `S`, then `π` embeds
into `A^K × S` (`comparison`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.LeftCuspidalDerivative

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

section PowerFunctor

variable {d : ℕ}
  (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))

/-- `Y ↦ A^K × Y` as a functor. -/
def powerFunctor : (K : ℕ) → {m : ℕ} →
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (powerRank d K m) F.Carrier)
  | 0, _ => letI := T.topology; 𝟭 _
  | K + 1, m =>
    letI := T.topology
    powerFunctor K ⋙ (Prod.sectR A.obj _ ⋙
      T.binaryNormalizedProductFunctor.{uF, max uF uV} d (powerRank d K m))

theorem powerFunctor_obj (K : ℕ) {m : ℕ}
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) :
    (powerFunctor F T A K).obj Y = powerProduct F T A K Y := by
  induction K with
  | zero => rfl
  | succ K ih =>
    change (T.binaryNormalizedProductFunctor.{uF, max uF uV} d (powerRank d K m)).obj
      (A.obj, (powerFunctor F T A K).obj Y) = _
    rw [ih]
    rfl

theorem powerFunctor_preservesFiniteLength (K : ℕ) {m : ℕ} :
    letI := T.topology
    SmoothRep.PreservesFiniteLength (powerFunctor F T A K (m := m)) := by
  let := T.topology
  induction K with
  | zero => exact SmoothRep.preservesFiniteLength_id
  | succ K ih =>
    refine SmoothRep.PreservesFiniteLength.comp ih ?_
    intro X hX
    exact Derivative.ProductDerivativesFiniteLength.binaryProduct_hasFiniteLength T (A.obj, X)
      (SmoothRep.hasFiniteLength_of_isIrreducible A.property.1) hX

theorem powerFunctor_preservesFiniteLengthShortExact (K : ℕ) {m : ℕ} :
    letI := T.topology
    SmoothRep.PreservesFiniteLengthShortExact (powerFunctor F T A K (m := m)) := by
  let := T.topology
  induction K with
  | zero => exact SmoothRep.preservesFiniteLengthShortExact_id
  | succ K ih =>
    refine SmoothRep.PreservesFiniteLengthShortExact.comp
      (powerFunctor_preservesFiniteLength F T A K) ih ?_
    intro X Y Z f g hX hY hZ h
    exact (Aubert.binaryProductExactness F T d (powerRank d K m)).2
      ⟨A.obj, SmoothRep.hasFiniteLength_of_isIrreducible A.property.1⟩
      ⟨X, hX⟩ ⟨Y, hY⟩ ⟨Z, hZ⟩ (SmoothRep.hom f) (SmoothRep.hom g) h

end PowerFunctor

/-- `exists_isSubrepresentation_of_isSubrepresentation_binaryProduct` after a rank transport. -/
theorem exists_isSubrepresentation_of_isSubrepresentation_castRank {d a m N : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hm : 0 < m)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible) (hp : IsPure T hd A 𝔄)
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hr : LeftReduced F T A Y) (h : a + m = N)
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hπ : letI := T.topology; π.IsIrreducible)
    (hs : letI := T.topology; SmoothRep.IsSubrepresentation π
      (T.castRank h ((T.binaryNormalizedProductFunctor a m).obj (𝔄, Y)))) :
    letI := T.topology
    ∃ E : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier), E.IsIrreducible ∧
      SmoothRep.IsSubrepresentation E Y ∧ SmoothRep.IsSubrepresentation π
        (T.castRank h ((T.binaryNormalizedProductFunctor a m).obj (𝔄, E))) := by
  subst h
  exact exists_isSubrepresentation_of_isSubrepresentation_binaryProduct F T hd ha hm A h𝔄 hp hr
    hπ hs

/-- An irreducible subquotient of an irreducible smooth representation is isomorphic to it. -/
theorem nonempty_iso_of_isSubquotient_of_isIrreducible {n : ℕ}
    {π P : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hπ : letI := T.topology; π.IsIrreducible) (hP : letI := T.topology; P.IsIrreducible)
    (h : letI := T.topology; SmoothRep.IsSubquotient π P) :
    letI := T.topology; Nonempty (π ≅ P) := by
  let := T.topology
  obtain ⟨e⟩ := CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient hP hπ
    (SmoothRep.isSubquotient_iff_representation.mp h)
  exact ⟨(SmoothRep.mkIso e).symm⟩

/-- An isomorphism is an embedding. -/
theorem isSubrepresentation_of_nonempty_iso {G : Type uF} [Group G] [TopologicalSpace G]
    {π P : SmoothRep.{0, uF, max uF uV} ℂ G} (e : π ≅ P) : SmoothRep.IsSubrepresentation π P :=
  ⟨e.hom, fun _ _ hxy => Derivative.LevelCalculus.iso_hom_injective e hxy⟩

/-- **Clause 3 (comparison).** If an irreducible `π` embeds into `A^K × Y`, where `Y` is
finite-length, left `A`-reduced and every irreducible subrepresentation of `Y` is isomorphic to
the irreducible `S`, then `π` embeds into `A^K × S`. -/
theorem comparison {d : ℕ}
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    (K m : ℕ)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (powerRank d K m) F.Carrier))
    (Y S : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hY : letI := T.topology; Y.HasFiniteLength) (hπ : letI := T.topology; π.IsIrreducible)
    (hS : letI := T.topology; S.IsIrreducible) (hr : LeftReduced F T A Y)
    (hYS : letI := T.topology; ∀ Z : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier),
      Z.IsIrreducible → SmoothRep.IsSubrepresentation Z Y → Nonempty (Z ≅ S))
    (hs : letI := T.topology; SmoothRep.IsSubrepresentation π (powerProduct F T A K Y)) :
    letI := T.topology
    SmoothRep.IsSubrepresentation π (powerProduct F T A K S) := by
  let := T.topology
  have hπnt : Nontrivial π := nontrivial_of_isIrreducible hπ
  cases K with
  | zero =>
    obtain ⟨e⟩ := hYS π hπ hs
    exact isSubrepresentation_of_nonempty_iso e
  | succ K =>
    obtain rfl | hd := Nat.eq_zero_or_pos d
    · exfalso
      have hY0 := subsingleton_of_leftReduced_rankZero F T A Y hY hr
      have hP : Subsingleton ((powerFunctor F T A (K + 1)).obj Y) :=
        subsingleton_map_of_preservesFiniteLengthShortExact
          (powerFunctor_preservesFiniteLengthShortExact F T A (K + 1)) hY hY0
      rw [powerFunctor_obj] at hP
      obtain ⟨j, hj⟩ := hs
      obtain ⟨x, y, hxy⟩ := exists_pair_ne π
      exact hxy (hj (Subsingleton.elim _ _))
    have ha : 0 < ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank :=
      Finset.sum_pos (fun _ _ => hd) ⟨0, Finset.mem_univ _⟩
    have h𝔄 := isIrreducible_cuspidalPower T hd A (K + 1) K.succ_pos rfl
    obtain rfl | hm := Nat.eq_zero_or_pos m
    · -- `m = 0`: every irreducible subquotient of `A^(K+1) × Y` is `A^(K+1) × S`
      have hP : ∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank = powerRank d (K + 1) 0 := by
        rw [sum_cuspidalDatumOf_rank, powerRank_eq]
        ring
      have hsq : SmoothRep.IsSubquotient π ((powerFunctor F T A (K + 1)).obj Y) := by
        rw [powerFunctor_obj]
        exact hs.isSubquotient
      obtain ⟨τ, hτ, -, hπτ⟩ := exists_irreducible_of_isSubquotient_map_of_finiteLength
        (powerFunctor_preservesFiniteLengthShortExact F T A (K + 1)) hY hπ hsq
      let eτ : τ ≅ S := rankZeroIrreducibleUnitIso.{uF, max uF uV} F T τ hτ ≪≫
        (rankZeroIrreducibleUnitIso.{uF, max uF uV} F T S hS).symm
      have hπS : SmoothRep.IsSubquotient π (powerProduct F T A (K + 1) S) := by
        rw [← powerFunctor_obj]
        exact SmoothRep.IsSubquotient.of_iso_right hπτ ((powerFunctor F T A (K + 1)).mapIso eτ)
      obtain ⟨e⟩ := nonempty_powerProduct_rankZero_iso F T hd A S hS K rfl hP
      have hirr : (powerProduct F T A (K + 1) S).IsIrreducible :=
        (isIrreducible_iff_of_equiv (SmoothRep.equivOfIso e)).mpr
          (T.isIrreducible_castRank hP _ h𝔄)
      obtain ⟨e'⟩ := nonempty_iso_of_isSubquotient_of_isIrreducible F T hπ hirr hπS
      exact isSubrepresentation_of_nonempty_iso e'
    · have hP : (∑ _i : Fin (K + 1), (cuspidalDatumOf T hd A).rank) + m =
          powerRank d (K + 1) m := by
        rw [sum_cuspidalDatumOf_rank, powerRank_eq]
        ring
      obtain ⟨eY⟩ := nonempty_powerProduct_iso F T hd A hm Y K rfl hP
      obtain ⟨E, hE, hEY, hsE⟩ := exists_isSubrepresentation_of_isSubrepresentation_castRank F T
        hd ha hm A h𝔄 (isPure_cuspidalPower T hd A (K + 1) K.succ_pos rfl) hr hP hπ
        (isSubrepresentation_of_iso T hs eY)
      obtain ⟨eES⟩ := hYS E hE hEY
      obtain ⟨e1⟩ := nonempty_castRank_iso T hP
        ((T.binaryNormalizedProductFunctor.{uF, max uF uV} _ m).mapIso
          (Iso.prod (Iso.refl (cuspidalPower T hd A (K + 1) rfl)) eES))
      obtain ⟨eS⟩ := nonempty_powerProduct_iso F T hd A hm S K rfl hP
      exact isSubrepresentation_of_iso T hsE (e1 ≪≫ eS.symm)

end Langlands.Classification.LeftCuspidalDerivative
