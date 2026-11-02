import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Parabolic.ProductInductionFiltration
import Langlands.Representation.Filtration.ExactConstituentExtraction

/-! Actual factor filtrations and constituent extraction for all-rank binary
normalized products, with independent field and input carrier universes. -/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands

universe uG uV uW uX uY uF

private def tensorCongr
    {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {τ : Representation ℂ G X} {υ : Representation ℂ G Y}
    (e : ρ.Equiv σ) (f : τ.Equiv υ) :
    (Representation.tprod ρ τ).Equiv (Representation.tprod σ υ) :=
  Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv)
    (fun g => (e.toIntertwiningMap.tensor f.toIntertwiningMap).isIntertwining' g)

/-- Transport a supplied filtration and its supplied quotient comparisons. -/
private def transportFiltrationData
    {G : Type uG} [Group G] [TopologicalSpace G]
    {A : Rep.{uV} ℂ G} {P : SmoothRep.{0, uG, uW} ℂ G} {r : ℕ}
    (s : ObjectRepFiltration A r) (e : A.ρ.Equiv P.representation)
    (Q : Fin r → SmoothRep.{0, uG, uW} ℂ G)
    (f : ∀ j, (s.gradedRepresentation j).ρ.Equiv (Q j).representation) :
    Σ t : ObjectRepFiltration P.obj r,
      ∀ j, (t.gradedRepresentation j).ρ.Equiv (Q j).representation :=
  ⟨LengthTwo.transport e s,
    fun j => (s.equivTransportGradedEquiv e j).symm.trans (f j)⟩

namespace PadicField.TopologicalData

open GeneralLinear BinaryTensor

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {a b : ℕ}

private def leftZeroPullbackEquiv (ha : a = 0)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    (Representation.tprod
      (A.representation.comp (1 : GeneralLinear (a + b) F.Carrier →*
        GeneralLinear a F.Carrier))
      (B.representation.comp
        (GeneralLinear.reindex (R := F.Carrier)
          (finCongr (by omega : a + b = b))).toMonoidHom)).Equiv
      ((T.binaryNormalizedProductFunctor a b).obj (A, B)).representation := by
  letI := T.topology
  refine (Representation.Equiv.mk (LinearEquiv.refl ℂ _) ?_).trans
    (T.binaryLeftZeroTensorEquiv ha (A, B)).symm
  intro g
  apply TensorProduct.ext'
  intro v w
  change A.representation 1 v ⊗ₜ[ℂ] _ = v ⊗ₜ[ℂ] _
  rw [map_one]
  rfl

private def rightZeroPullbackEquiv (hb : b = 0)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    (Representation.tprod
      (A.representation.comp
        (GeneralLinear.reindex (R := F.Carrier)
          (finCongr (by omega : a + b = a))).toMonoidHom)
      (B.representation.comp (1 : GeneralLinear (a + b) F.Carrier →*
        GeneralLinear b F.Carrier))).Equiv
      ((T.binaryNormalizedProductFunctor a b).obj (A, B)).representation := by
  letI := T.topology
  refine (Representation.Equiv.mk (LinearEquiv.refl ℂ _) ?_).trans
    (T.binaryRightZeroTensorEquiv hb (A, B)).symm
  intro g
  apply TensorProduct.ext'
  intro v w
  change _ ⊗ₜ[ℂ] B.representation 1 w = _ ⊗ₜ[ℂ] w
  rw [map_one]
  rfl

/-- Filter the actual all-rank binary product by a supplied left-factor
filtration, with actual equivalences for every successive quotient. -/
def binaryProductLeftFiltrationData
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    {r : ℕ} (s : ObjectRepFiltration A.obj r) :
    letI := T.topology
    Σ t : ObjectRepFiltration ((T.binaryNormalizedProductFunctor a b).obj (A, B)).obj r,
      ∀ j, (t.gradedRepresentation j).ρ.Equiv
        ((T.binaryNormalizedProductFunctor a b).obj (s.smoothGradedObject j, B)).representation := by
  letI := T.topology
  by_cases ha : a = 0
  · let φ : GeneralLinear (a + b) F.Carrier →* GeneralLinear a F.Carrier := 1
    let ψ := (GeneralLinear.reindex (R := F.Carrier)
      (finCongr (by omega : a + b = b))).toMonoidHom
    let t := (s.comp φ).tensorRight (Rep.of (B.representation.comp ψ))
    exact transportFiltrationData t (T.leftZeroPullbackEquiv ha A B) _
      (fun j => ((s.comp φ).tensorRightGradedEquiv _ j).trans
        ((tensorCongr (s.compGradedEquiv φ j) (Representation.Equiv.refl _)).trans
          (T.leftZeroPullbackEquiv ha (s.smoothGradedObject j) B)))
  · by_cases hb : b = 0
    · let φ := (GeneralLinear.reindex (R := F.Carrier)
        (finCongr (by omega : a + b = a))).toMonoidHom
      let ψ : GeneralLinear (a + b) F.Carrier →* GeneralLinear b F.Carrier := 1
      let t := (s.comp φ).tensorRight (Rep.of (B.representation.comp ψ))
      exact transportFiltrationData t (T.rightZeroPullbackEquiv hb A B) _
        (fun j => ((s.comp φ).tensorRightGradedEquiv _ j).trans
          ((tensorCongr (s.compGradedEquiv φ j) (Representation.Equiv.refl _)).trans
            (T.rightZeroPullbackEquiv hb (s.smoothGradedObject j) B)))
    · let ha' := Nat.pos_of_ne_zero ha
      let hb' := Nat.pos_of_ne_zero hb
      let C := BlockShape.binary a b ha' hb'
      let P := (T.binaryPairFamilyFunctor ha' hb').obj (A, B)
      let t := Parabolic.normalizedProductSlotFiltration T C
        (fun h => (P h).representation) (0 : Fin 2) s
      let e := (SmoothRep.equivOfIso ((T.binaryNormalizedProductPositiveIso ha' hb').app
        (A, B))).symm
      refine transportFiltrationData t e _ (fun j => ?_)
      let Q := (T.binaryPairFamilyFunctor ha' hb').obj (s.smoothGradedObject j, B)
      refine (Parabolic.normalizedProductSlotFiltrationGradedEquivOfFamily T C
        (fun h => (P h).representation) (0 : Fin 2) s
        (fun h => (Q h).representation) j ?_ (Representation.Equiv.refl _) (fun h => (P h).property)).trans
          (SmoothRep.equivOfIso ((T.binaryNormalizedProductPositiveIso ha' hb').app
            (s.smoothGradedObject j, B))).symm
      rintro ⟨h, hh⟩
      change h ≠ (0 : Fin 2) at hh
      have heq : h = (1 : Fin 2) := by
        apply Fin.ext
        change h.val = 1
        have hn : h.val ≠ 0 := fun h0 => hh (Fin.ext h0)
        have hv : h.val < 2 := h.isLt
        omega
      subst h
      exact Representation.Equiv.refl _

/-- Filter the actual all-rank binary product by a supplied right-factor
filtration, with actual equivalences for every successive quotient. -/
def binaryProductRightFiltrationData
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    {r : ℕ} (s : ObjectRepFiltration B.obj r) :
    letI := T.topology
    Σ t : ObjectRepFiltration ((T.binaryNormalizedProductFunctor a b).obj (A, B)).obj r,
      ∀ j, (t.gradedRepresentation j).ρ.Equiv
        ((T.binaryNormalizedProductFunctor a b).obj (A, s.smoothGradedObject j)).representation := by
  letI := T.topology
  by_cases ha : a = 0
  · let φ : GeneralLinear (a + b) F.Carrier →* GeneralLinear a F.Carrier := 1
    let ψ := (GeneralLinear.reindex (R := F.Carrier)
      (finCongr (by omega : a + b = b))).toMonoidHom
    let t := (s.comp ψ).tensorLeft (Rep.of (A.representation.comp φ))
    exact transportFiltrationData t (T.leftZeroPullbackEquiv ha A B) _
      (fun j => ((s.comp ψ).tensorLeftGradedEquiv _ j).trans
        ((tensorCongr (Representation.Equiv.refl _) (s.compGradedEquiv ψ j)).trans
          (T.leftZeroPullbackEquiv ha A (s.smoothGradedObject j))))
  · by_cases hb : b = 0
    · let φ := (GeneralLinear.reindex (R := F.Carrier)
        (finCongr (by omega : a + b = a))).toMonoidHom
      let ψ : GeneralLinear (a + b) F.Carrier →* GeneralLinear b F.Carrier := 1
      let t := (s.comp ψ).tensorLeft (Rep.of (A.representation.comp φ))
      exact transportFiltrationData t (T.rightZeroPullbackEquiv hb A B) _
        (fun j => ((s.comp ψ).tensorLeftGradedEquiv _ j).trans
          ((tensorCongr (Representation.Equiv.refl _) (s.compGradedEquiv ψ j)).trans
            (T.rightZeroPullbackEquiv hb A (s.smoothGradedObject j))))
    · let ha' := Nat.pos_of_ne_zero ha
      let hb' := Nat.pos_of_ne_zero hb
      let C := BlockShape.binary a b ha' hb'
      let P := (T.binaryPairFamilyFunctor ha' hb').obj (A, B)
      let t := Parabolic.normalizedProductSlotFiltration T C
        (fun h => (P h).representation) (1 : Fin 2) s
      let e := (SmoothRep.equivOfIso ((T.binaryNormalizedProductPositiveIso ha' hb').app
        (A, B))).symm
      refine transportFiltrationData t e _ (fun j => ?_)
      let Q := (T.binaryPairFamilyFunctor ha' hb').obj (A, s.smoothGradedObject j)
      refine (Parabolic.normalizedProductSlotFiltrationGradedEquivOfFamily T C
        (fun h => (P h).representation) (1 : Fin 2) s
        (fun h => (Q h).representation) j ?_ (Representation.Equiv.refl _) (fun h => (P h).property)).trans
          (SmoothRep.equivOfIso ((T.binaryNormalizedProductPositiveIso ha' hb').app
            (A, s.smoothGradedObject j))).symm
      rintro ⟨h, hh⟩
      change h ≠ (1 : Fin 2) at hh
      have heq : h = (0 : Fin 2) := by
        apply Fin.ext
        change h.val = 0
        have hn : h.val ≠ 1 := fun h1 => hh (Fin.ext h1)
        have hv : h.val < 2 := h.isLt
        omega
      subst h
      exact Representation.Equiv.refl _

/-- A supplied irreducible subquotient of a binary product of finite-length
factors occurs in the literal product of actual irreducible factor subquotients. -/
theorem exists_irreducible_factor_subquotients_of_binaryProduct
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    A.HasFiniteLength → B.HasFiniteLength →
    ∀ D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier),
      D.IsIrreducible →
      SmoothRep.IsSubquotient D ((T.binaryNormalizedProductFunctor a b).obj (A, B)) →
      ∃ (E : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
        (H : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
        E.IsIrreducible ∧ SmoothRep.IsSubquotient E A ∧
        H.IsIrreducible ∧ SmoothRep.IsSubquotient H B ∧
        SmoothRep.IsSubquotient D ((T.binaryNormalizedProductFunctor a b).obj (E, H)) := by
  let := T.topology
  intro hA hB D hD hDP
  obtain ⟨c, hc₀, hc₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hA
  obtain ⟨s, hs⟩ :=
    LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries c hc₀ hc₁
  obtain ⟨t, ht⟩ := T.binaryProductLeftFiltrationData A B s
  obtain ⟨i, hi⟩ := t.exists_smoothGradedObject_subquotient hD hDP
  have hi' := hi.of_iso_right (SmoothRep.mkIso (ht i))
  obtain ⟨c', hc'₀, hc'₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hB
  obtain ⟨s', hs'⟩ :=
    LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries c' hc'₀ hc'₁
  obtain ⟨t', ht'⟩ := T.binaryProductRightFiltrationData (s.smoothGradedObject i) B s'
  obtain ⟨j, hj⟩ := t'.exists_smoothGradedObject_subquotient hD hi'
  exact ⟨s.smoothGradedObject i, s'.smoothGradedObject j,
    hs i, s.smoothGradedObject_isSubquotient i,
    hs' j, s'.smoothGradedObject_isSubquotient j,
    hj.of_iso_right (SmoothRep.mkIso (ht' j))⟩

end PadicField.TopologicalData

end Langlands
