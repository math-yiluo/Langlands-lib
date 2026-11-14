import Langlands.GroupScheme.Rational.CompatiblePinningRestriction
import Langlands.GroupScheme.Rational.MergedRootGaloisData
import Langlands.Geometry.Building.QuasiSplitMultipliableOpposite

/-! # Piece families of `A₂` orbits of simple roots

For Galois-compatible pinning data and a maximal split torus, the Galois orbit of the sum
`m₀ = p₀ + q₀` of two simple roots with equal restriction indexes a piece family over that
restriction, together with exactly Galois-equivariant merged-root maps. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Geometry.Building

namespace Langlands.GroupScheme

namespace GaloisCompatiblePinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : GaloisCompatiblePinningData k K G)

local notation "bK" => algebraBaseMap k K

/-- The ordinary Galois permutation of all root indices of the pinning. -/
def rootIndexAction : (K ≃ₐ[k] K) →* Equiv.Perm D.pinning.rootIndex :=
  IsRootDatumOf.galoisRootIndexAction (T := D.torus) (P := D.transportedRootDatum) k K
    D.inclusion D.transportedRootDatum_isRootDatum

theorem transportedRoot_rootIndexAction (σ : K ≃ₐ[k] K) (r : D.pinning.rootIndex) :
    D.transportedRootDatum.root (D.rootIndexAction σ r) =
      characterLattice.galoisRepresentation k K D.torus σ (D.transportedRootDatum.root r) :=
  IsRootDatumOf.galoisRootIndexEquiv_root k K D.inclusion D.transportedRootDatum_isRootDatum σ r

theorem rootIndexAction_simple (σ : K ≃ₐ[k] K) (a : D.pinning.base.support) :
    D.rootIndexAction σ (a : D.pinning.rootIndex) = (D.action σ a : D.pinning.rootIndex) := by
  apply D.transportedRootDatum.root.injective
  rw [D.transportedRoot_rootIndexAction, D.transportedRootDatum_action_root]

theorem root_rootIndexAction_add (σ : K ≃ₐ[k] K) {m x y : D.pinning.rootIndex}
    (h : D.pinning.rootDatum.root m = D.pinning.rootDatum.root x + D.pinning.rootDatum.root y) :
    D.pinning.rootDatum.root (D.rootIndexAction σ m) =
      D.pinning.rootDatum.root (D.rootIndexAction σ x) +
        D.pinning.rootDatum.root (D.rootIndexAction σ y) := by
  apply (characterLattice.congr D.torusIso).injective
  rw [map_add, ← D.transportedRootDatum_root, ← D.transportedRootDatum_root,
    ← D.transportedRootDatum_root, D.transportedRoot_rootIndexAction,
    D.transportedRoot_rootIndexAction, D.transportedRoot_rootIndexAction, ← map_add,
    D.transportedRootDatum_root, D.transportedRootDatum_root, D.transportedRootDatum_root, h,
    map_add]

/-- The Galois action on root indices, as a multiplicative action. -/
@[reducible] def rootIndexMulAction : MulAction (K ≃ₐ[k] K) D.pinning.rootIndex :=
  MulAction.compHom _ D.rootIndexAction

attribute [local instance] rootIndexMulAction

theorem smul_rootIndex (σ : K ≃ₐ[k] K) (r : D.pinning.rootIndex) :
    σ • r = D.rootIndexAction σ r := rfl

section Pairs

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} (t : S ⟶ D.torus)
  {p₀ q₀ : D.pinning.base.support} {m₀ : D.pinning.rootIndex}
  (hm₀ : D.pinning.rootDatum.root m₀ =
    D.pinning.rootDatum.root (p₀ : D.pinning.rootIndex) +
      D.pinning.rootDatum.root (q₀ : D.pinning.rootIndex))

/-- The Galois orbit of the merged root `m₀`, indexing the pieces. -/
abbrev PairOrbit (m₀ : D.pinning.rootIndex) : Type u :=
  MulAction.orbit (K ≃ₐ[k] K) m₀

/-- A Galois element carrying `m₀` to a given point of its orbit. -/
def pairElement (c : D.PairOrbit m₀) : K ≃ₐ[k] K :=
  (MulAction.mem_orbit_iff.mp c.2).choose

theorem pairElement_smul (c : D.PairOrbit m₀) : D.pairElement c • m₀ = c.1 :=
  (MulAction.mem_orbit_iff.mp c.2).choose_spec

variable (p₀ q₀) in
/-- The first simple root of the piece at `c`. -/
def pairA (c : D.PairOrbit m₀) : D.pinning.base.support := D.action (D.pairElement c) p₀

variable (p₀ q₀) in
/-- The second simple root of the piece at `c`. -/
def pairB (c : D.PairOrbit m₀) : D.pinning.base.support := D.action (D.pairElement c) q₀

include hm₀ in
theorem root_pair (c : D.PairOrbit m₀) :
    D.pinning.rootDatum.root c.1 =
      D.pinning.rootDatum.root (D.pairA p₀ c : D.pinning.rootIndex) +
        D.pinning.rootDatum.root (D.pairB q₀ c : D.pinning.rootIndex) := by
  rw [← D.pairElement_smul c, smul_rootIndex, D.root_rootIndexAction_add _ hm₀,
    D.rootIndexAction_simple, D.rootIndexAction_simple]
  rfl

end Pairs

section Pieces

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} (t : S ⟶ D.torus)
  {p₀ q₀ : D.pinning.base.support} {m₀ : D.pinning.rootIndex}
  (hm₀ : D.pinning.rootDatum.root m₀ =
    D.pinning.rootDatum.root (p₀ : D.pinning.rootIndex) +
      D.pinning.rootDatum.root (q₀ : D.pinning.rootIndex))
  (hS : IsSplitTorus S.toGrp) {a : characterLattice S}
  (hp₀ : D.restrictMap t ≫ D.pinning.rootDatum.root (p₀ : D.pinning.rootIndex) =
    characterLattice.baseChange (algebraBaseMap k K) S a)
  (hq₀ : D.restrictMap t ≫ D.pinning.rootDatum.root (q₀ : D.pinning.rootIndex) =
    characterLattice.baseChange (algebraBaseMap k K) S a)
  (hpq : p₀ ≠ q₀)
  (hline : RestrictsToMultipliableLine (D.restrictMap t) D.pinning.rootDatum
    (characterLattice.baseChange (algebraBaseMap k K) S a))

include hS hp₀ in
theorem restrict_pairA (c : D.PairOrbit m₀) :
    D.restrictMap t ≫ D.pinning.rootDatum.root (D.pairA p₀ c : D.pinning.rootIndex) =
      characterLattice.baseChange (algebraBaseMap k K) S a := by
  rw [pairA, D.restrictMap_comp_root_action t hS, hp₀]

include hS hq₀ in
theorem restrict_pairB (c : D.PairOrbit m₀) :
    D.restrictMap t ≫ D.pinning.rootDatum.root (D.pairB q₀ c : D.pinning.rootIndex) =
      characterLattice.baseChange (algebraBaseMap k K) S a := by
  rw [pairB, D.restrictMap_comp_root_action t hS, hq₀]

include hpq in
theorem pairA_ne_pairB (c : D.PairOrbit m₀) :
    (D.pairA p₀ c : D.pinning.rootIndex) ≠ (D.pairB q₀ c : D.pinning.rootIndex) := by
  intro h
  exact hpq ((D.action (D.pairElement c)).injective (Subtype.ext h))

include hm₀ hS hp₀ hq₀ hpq in
theorem isMultipliablePiece_pair (c : D.PairOrbit m₀) :
    IsMultipliablePiece (D.restrictMap t) D.pinning.rootDatum
      (characterLattice.baseChange (algebraBaseMap k K) S a)
      (D.pairA p₀ c : D.pinning.rootIndex) (D.pairB q₀ c : D.pinning.rootIndex) c.1 :=
  ⟨D.restrict_pairA t hS hp₀ c, D.restrict_pairB t hS hq₀ c, D.pairA_ne_pairB hpq c,
    D.root_pair hm₀ c⟩

include hm₀ hS hp₀ hq₀ hpq hline in
/-- The Galois image of the piece at `c` is the piece at `σ • c`, in one of the two orders. -/
theorem pair_orient (σ : K ≃ₐ[k] K) (c : D.PairOrbit m₀) :
    (D.pairA p₀ (σ • c) = D.action σ (D.pairA p₀ c) ∧
        D.pairB q₀ (σ • c) = D.action σ (D.pairB q₀ c)) ∨
      (D.pairA p₀ (σ • c) = D.action σ (D.pairB q₀ c) ∧
        D.pairB q₀ (σ • c) = D.action σ (D.pairA p₀ c)) := by
  have hpc := D.isMultipliablePiece_pair t hm₀ hS hp₀ hq₀ hpq (σ • c)
  have hσc : ((σ • c : D.PairOrbit m₀) : D.pinning.rootIndex) = D.rootIndexAction σ c.1 := rfl
  have hsum : D.pinning.rootDatum.root (D.action σ (D.pairA p₀ c) : D.pinning.rootIndex) +
      D.pinning.rootDatum.root (D.action σ (D.pairB q₀ c) : D.pinning.rootIndex) =
      D.pinning.rootDatum.root (σ • c : D.PairOrbit m₀).1 := by
    rw [hσc, D.root_rootIndexAction_add σ (D.root_pair hm₀ c), D.rootIndexAction_simple,
      D.rootIndexAction_simple]
  have hA : D.restrictMap t ≫ D.pinning.rootDatum.root
      (D.action σ (D.pairA p₀ c) : D.pinning.rootIndex) =
        characterLattice.baseChange (algebraBaseMap k K) S a := by
    rw [D.restrictMap_comp_root_action t hS, D.restrict_pairA t hS hp₀]
  have hB : D.restrictMap t ≫ D.pinning.rootDatum.root
      (D.action σ (D.pairB q₀ c) : D.pinning.rootIndex) =
        characterLattice.baseChange (algebraBaseMap k K) S a := by
    rw [D.restrictMap_comp_root_action t hS, D.restrict_pairB t hS hq₀]
  rcases piece_decomposition_unique hline hpc hA hB hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨(Subtype.ext h1).symm, (Subtype.ext h2).symm⟩
  · exact Or.inr ⟨(Subtype.ext h2).symm, (Subtype.ext h1).symm⟩

include hm₀ hS hp₀ hq₀ hpq hline in
/-- Two pieces sharing a root are equal. -/
theorem pair_eq_of_mem {c c' : D.PairOrbit m₀} {x : D.pinning.rootIndex}
    (hx : x = D.pairA p₀ c ∨ x = D.pairB q₀ c) (hx' : x = D.pairA p₀ c' ∨ x = D.pairB q₀ c') :
    c = c' := by
  have hpc := D.isMultipliablePiece_pair t hm₀ hS hp₀ hq₀ hpq c
  have hpc' := D.isMultipliablePiece_pair t hm₀ hS hp₀ hq₀ hpq c'
  -- the partner of `x` in both pieces
  have key : ∀ {c c' : D.PairOrbit m₀},
      IsMultipliablePiece (D.restrictMap t) D.pinning.rootDatum
        (characterLattice.baseChange (algebraBaseMap k K) S a) (D.pairA p₀ c : D.pinning.rootIndex)
        (D.pairB q₀ c : D.pinning.rootIndex) c.1 →
      IsMultipliablePiece (D.restrictMap t) D.pinning.rootDatum
        (characterLattice.baseChange (algebraBaseMap k K) S a) (D.pairA p₀ c' : D.pinning.rootIndex)
        (D.pairB q₀ c' : D.pinning.rootIndex) c'.1 →
      ∀ {y z y' z' : D.pinning.rootIndex},
        IsMultipliablePiece (D.restrictMap t) D.pinning.rootDatum
          (characterLattice.baseChange (algebraBaseMap k K) S a) y z c.1 →
        IsMultipliablePiece (D.restrictMap t) D.pinning.rootDatum
          (characterLattice.baseChange (algebraBaseMap k K) S a) y' z' c'.1 → y = y' → c = c' := by
    intro c c' _ _ y z y' z' h h' hyy
    subst hyy
    have hz := partner_unique hline h.1 h.2.1 h'.2.1 h.2.2.1
      (piece_pairing_pq hline h.1 h.2.1 h.2.2.1 h.2.2.2)
      (piece_pairing_pq hline h'.1 h'.2.1 h'.2.2.1 h'.2.2.2)
    subst hz
    apply Subtype.ext
    apply D.pinning.rootDatum.root.injective
    rw [h.2.2.2, h'.2.2.2]
  rcases hx with rfl | rfl <;> rcases hx' with h | h
  · exact key hpc hpc' hpc hpc' h
  · exact key hpc hpc' hpc hpc'.swap h
  · exact key hpc hpc' hpc.swap hpc' h
  · exact key hpc hpc' hpc.swap hpc'.swap h

end Pieces

instance (m₀ : D.pinning.rootIndex) : Finite (D.PairOrbit m₀) := Subtype.finite

section Family

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} (t : S ⟶ D.torus)
  {p₀ q₀ : D.pinning.base.support} {m₀ : D.pinning.rootIndex}
  (hm₀ : D.pinning.rootDatum.root m₀ =
    D.pinning.rootDatum.root (p₀ : D.pinning.rootIndex) +
      D.pinning.rootDatum.root (q₀ : D.pinning.rootIndex))
  (hS : IsSplitTorus S.toGrp) {a : characterLattice S}
  (hp₀ : D.restrictMap t ≫ D.pinning.rootDatum.root (p₀ : D.pinning.rootIndex) =
    characterLattice.baseChange (algebraBaseMap k K) S a)
  (hq₀ : D.restrictMap t ≫ D.pinning.rootDatum.root (q₀ : D.pinning.rootIndex) =
    characterLattice.baseChange (algebraBaseMap k K) S a)
  (hpq : p₀ ≠ q₀)
  (hline : RestrictsToMultipliableLine (D.restrictMap t) D.pinning.rootDatum
    (characterLattice.baseChange (algebraBaseMap k K) S a))

include hm₀ hS hp₀ hq₀ hpq hline in
theorem pair_pairings (c : D.PairOrbit m₀) :
    D.pairA p₀ c ≠ D.pairB q₀ c ∧
      D.pinning.rootDatum.pairing (D.pairA p₀ c : D.pinning.rootIndex)
        (D.pairB q₀ c : D.pinning.rootIndex) = -1 ∧
      D.pinning.rootDatum.pairing (D.pairB q₀ c : D.pinning.rootIndex)
        (D.pairA p₀ c : D.pinning.rootIndex) = -1 := by
  obtain ⟨h1, h2, h3, h4⟩ := D.isMultipliablePiece_pair t hm₀ hS hp₀ hq₀ hpq c
  exact ⟨fun h => h3 (congrArg Subtype.val h), piece_pairing_pq hline h1 h2 h3 h4,
    piece_pairing_qp hline h1 h2 h3 h4⟩

variable [FiniteDimensional k K]

include hm₀ hS hp₀ hq₀ hpq hline in
/-- Galois-compatible merged-root data along the pieces of the orbit. -/
theorem exists_mergedPieces :
    ∃ M : D.PairOrbit m₀ → D.pinning.SteinbergModifiedData,
      (∀ c, (M c).a = D.pairA p₀ c ∧ (M c).b = D.pairB q₀ c ∧ (M c).ca = 1 ∧ (M c).cb = 1) ∧
      (∀ c, (M c).nAlpha.point ∈
        (RelativeRoot.subgroup D.pinning.inclusion
            (D.pinning.rootDatum.root (M c).alpha)).carrier (Over.mk (𝟙 _)) ⊔
          (RelativeRoot.subgroup D.pinning.inclusion
            (-D.pinning.rootDatum.root (M c).alpha)).carrier (Over.mk (𝟙 _))) ∧
      (∀ (σ : K ≃ₐ[k] K) (c : D.PairOrbit m₀) (s : K),
        GaloisPointComparison.rationalConjugate k K G σ ((M c).xAlpha.rationalPoint s) =
          (M (σ • c)).xAlpha.rationalPoint (σ s)) ∧
      (∀ (σ : K ≃ₐ[k] K) (c : D.PairOrbit m₀),
        GaloisPointComparison.rationalConjugate k K G σ (M c).nAlpha.point =
          (M (σ • c)).nAlpha.point) ∧
      (∀ (σ : K ≃ₐ[k] K) (c : D.PairOrbit m₀) (u : Kˣ),
        GaloisPointComparison.rationalConjugate k K G σ
            (SplitPinning.corootRationalPoint D.pinning (M c).alpha u) =
          SplitPinning.corootRationalPoint D.pinning (M (σ • c)).alpha
            (Units.map σ.toMonoidHom u)) :=
  D.exists_mergedRootGaloisData (D.pairA p₀) (D.pairB q₀)
    (D.pair_pairings t hm₀ hS hp₀ hq₀ hpq hline)
    (D.pair_orient t hm₀ hS hp₀ hq₀ hpq hline)

end Family

section PieceFamily

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} (t : S ⟶ D.torus)
  {p₀ q₀ : D.pinning.base.support} {m₀ : D.pinning.rootIndex}
  (hm₀ : D.pinning.rootDatum.root m₀ =
    D.pinning.rootDatum.root (p₀ : D.pinning.rootIndex) +
      D.pinning.rootDatum.root (q₀ : D.pinning.rootIndex))
  (hS : IsSplitTorus S.toGrp) {a : characterLattice S}
  (hp₀ : D.restrictMap t ≫ D.pinning.rootDatum.root (p₀ : D.pinning.rootIndex) =
    characterLattice.baseChange (algebraBaseMap k K) S a)
  (hq₀ : D.restrictMap t ≫ D.pinning.rootDatum.root (q₀ : D.pinning.rootIndex) =
    characterLattice.baseChange (algebraBaseMap k K) S a)
  (hpq : p₀ ≠ q₀)
  (hline : RestrictsToMultipliableLine (D.restrictMap t) D.pinning.rootDatum
    (characterLattice.baseChange (algebraBaseMap k K) S a))
  (M : D.PairOrbit m₀ → D.pinning.SteinbergModifiedData)
  (hM : ∀ c, (M c).a = D.pairA p₀ c ∧ (M c).b = D.pairB q₀ c)

include hm₀ hM in
theorem mergedAlpha_eq (c : D.PairOrbit m₀) : (M c).alpha = c.1 := by
  apply D.pinning.rootDatum.root.injective
  rw [(M c).root_eq, (hM c).1, (hM c).2, D.root_pair hm₀ c]

/-- An enumeration of the pieces. -/
def pieceEquiv (m₀ : D.pinning.rootIndex) : Fin (Nat.card (D.PairOrbit m₀)) ≃ D.PairOrbit m₀ :=
  (Finite.equivFin _).symm

/-- The base piece, at `m₀` itself. -/
def basePair (m₀ : D.pinning.rootIndex) : D.PairOrbit m₀ := ⟨m₀, MulAction.mem_orbit_self m₀⟩

variable [LocallyOfFiniteType G.X.hom] [IsAffineHom D.torus.toGrp.X.hom]
  [LocallyOfFiniteType D.torus.toGrp.X.hom] [FiniteDimensional k K] [IsGalois k K]
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj D.torus).toGrp)
  (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom t ≫ D.inclusion))
  (hjc : IsClosedSubgroup D.inclusion)
  (hcent : (torusCentralizer (CommGroupScheme.groupHom t ≫ D.inclusion)).IsRepresentedBy
      D.inclusion)

/-- **The piece family of an `A₂` orbit.** Pieces are indexed by the Galois orbit of `m₀`; the
piece at `c` has roots `pairA c`, `pairB c` over `a` and the merged root of `M c` over `2a`. -/
def a2PieceFamily : PieceFamily (D.restrictMap t) D.pinning.rootDatum
    (characterLattice.baseChange (algebraBaseMap k K) S a) where
  r := Nat.card (D.PairOrbit m₀)
  lp l := (D.pairA p₀ (D.pieceEquiv m₀ l) : D.pinning.rootIndex)
  lq l := (D.pairB q₀ (D.pieceEquiv m₀ l) : D.pinning.rootIndex)
  lm l := (M (D.pieceEquiv m₀ l)).alpha
  piece l := by
    obtain ⟨h1, h2, h3, h4⟩ := D.isMultipliablePiece_pair t hm₀ hS hp₀ hq₀ hpq
      (D.pieceEquiv m₀ l)
    exact ⟨h1, h2, h3, by rw [D.mergedAlpha_eq hm₀ M hM]; exact h4⟩
  disjoint l l' hll' := by
    have hne : D.pieceEquiv m₀ l ≠ D.pieceEquiv m₀ l' := (D.pieceEquiv m₀).injective.ne hll'
    refine ⟨fun h => hne ?_, fun h => hne ?_, fun h => hne ?_, fun h => hne ?_⟩
    · exact D.pair_eq_of_mem t hm₀ hS hp₀ hq₀ hpq hline (Or.inl rfl) (Or.inl h.symm)
    · exact D.pair_eq_of_mem t hm₀ hS hp₀ hq₀ hpq hline (Or.inr rfl) (Or.inl h.symm)
    · exact D.pair_eq_of_mem t hm₀ hS hp₀ hq₀ hpq hline (Or.inl rfl) (Or.inr h.symm)
    · exact D.pair_eq_of_mem t hm₀ hS hp₀ hq₀ hpq hline (Or.inr rfl) (Or.inr h.symm)
  lm_injective l l' h := by
    simp only at h
    rw [D.mergedAlpha_eq hm₀ M hM, D.mergedAlpha_eq hm₀ M hM] at h
    exact (D.pieceEquiv m₀).injective (Subtype.ext h)
  cover_a i hi := by
    obtain ⟨σ, hσ⟩ := D.exists_action_eq_of_restrict_eq t hS hT hf hjc hcent
      (r := i) (a₀ := p₀) (by rw [hi, hp₀])
    set c : D.PairOrbit m₀ := σ • D.basePair m₀ with hc
    have hroot : D.pinning.rootDatum.root (D.action σ p₀ : D.pinning.rootIndex) +
        D.pinning.rootDatum.root (D.action σ q₀ : D.pinning.rootIndex) =
        D.pinning.rootDatum.root c.1 := by
      change _ = D.pinning.rootDatum.root (D.rootIndexAction σ m₀)
      rw [D.root_rootIndexAction_add σ hm₀, D.rootIndexAction_simple, D.rootIndexAction_simple]
    have hA : D.restrictMap t ≫ D.pinning.rootDatum.root (D.action σ p₀ : D.pinning.rootIndex) =
        characterLattice.baseChange (algebraBaseMap k K) S a := by
      rw [D.restrictMap_comp_root_action t hS, hp₀]
    have hB : D.restrictMap t ≫ D.pinning.rootDatum.root (D.action σ q₀ : D.pinning.rootIndex) =
        characterLattice.baseChange (algebraBaseMap k K) S a := by
      rw [D.restrictMap_comp_root_action t hS, hq₀]
    refine ⟨(D.pieceEquiv m₀).symm c, ?_⟩
    rw [Equiv.apply_symm_apply, hσ]
    rcases piece_decomposition_unique hline (D.isMultipliablePiece_pair t hm₀ hS hp₀ hq₀ hpq c)
      hA hB hroot with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  cover_two i hi := by
    have hm₀res : D.restrictMap t ≫ D.pinning.rootDatum.root m₀ =
        (2 : ℤ) • characterLattice.baseChange (algebraBaseMap k K) S a := by
      rw [hm₀, Preadditive.comp_add, hp₀, hq₀, two_zsmul]
    obtain ⟨σ, hσ⟩ := D.exists_galois_of_restrict_eq t hS hT hf hjc hcent
      (r := i) (r₀ := m₀) (by rw [hi, hm₀res])
    refine ⟨(D.pieceEquiv m₀).symm (σ • D.basePair m₀), ?_⟩
    rw [Equiv.apply_symm_apply, D.mergedAlpha_eq hm₀ M hM]
    apply D.transportedRootDatum.root.injective
    rw [hσ]
    change _ = D.transportedRootDatum.root (D.rootIndexAction σ m₀)
    rw [D.transportedRoot_rootIndexAction]

end PieceFamily

end GaloisCompatiblePinningData

end Langlands.GroupScheme
