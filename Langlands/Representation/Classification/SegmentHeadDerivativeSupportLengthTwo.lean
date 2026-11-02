import Langlands.Representation.Classification.SegmentTruncationObstructionStatement
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
import Langlands.Representation.Derivative.RestrictionBridge
import Langlands.Representation.Classification.SupercuspidalDerivativesProof
import Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftProof
import Langlands.Representation.Classification.SegmentHeadTopDerivative
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.Tensor.SmoothSubquotients
import Langlands.Representation.Filtration.ZeroFactorDeletionProof
import Langlands.Representation.Filtration.SubsingletonProof
import Langlands.Representation.Filtration.FunctorLengthTwoDetection
import Langlands.Representation.Classification.SegmentCuspidalContent
import Langlands.Representation.Derivative.OrderedCuspidalProductHeadShift
import Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof

/-!
# Derivative supports of a special head of length two

For a segment `Δ = [ρ, νρ]` of length two, every irreducible subquotient of every
derivative of a supplied special head of `ρ × νρ` has a supercuspidal support whose
set is an optional terminal truncation of `Δ`. The reducibility of `ρ × νρ` is taken
from the published `twoSupercuspidalAdjacentProductReducible`, under operator ruling
`2b33898bdd0a5ff1b9031be5155a06f0`; nothing else from Ze80 1.11 is used.

The module also exports the generic cases used for segments of every length:
derivative order `0`, top order `deg Δ`, and segments of length one.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Langlands.Classification.SegmentHeadDerivativeSupportLengthTwo

open GeneralLinear HarmonicAnalysis Derivative BinaryTensor

universe uF uV

/-! ## Binary products with zero or rank-zero factors

These comparisons are adapted from `TwoSupercuspidalBinaryProductBridge`; they use
only `Induction.BinaryProduct` and the derivative rank transport. -/

section BinaryProducts

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

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
  · exact Or.inl (isZero_of_subsingleton F T hA)
  · exact Or.inr (isZero_of_subsingleton F T hB)

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
  obtain ⟨eZ⟩ := nonempty_iso_unit F T Z hZ
  let e1 := SmoothRep.equivOfIso
    ((T.binaryNormalizedProductFunctor a 0).mapIso (Iso.prod (Iso.refl A) eZ))
  let e2 := T.binaryProductRightUnitEquiv A
  let e3 := rankCastEquiv F T (Nat.add_zero a).symm A
  exact ⟨((e3.symm.trans (liftEquiv _)).trans e2.symm).trans e1.symm⟩

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
  obtain ⟨eZ⟩ := nonempty_iso_unit F T Z hZ
  let e1 := SmoothRep.equivOfIso
    ((T.binaryNormalizedProductFunctor 0 b).mapIso (Iso.prod eZ (Iso.refl B)))
  let e2 := T.binaryProductLeftUnitEquiv B
  let e3 := rankCastEquiv F T h' B
  exact ⟨((e3.symm.trans (liftEquiv _)).trans e2.symm).trans e1.symm⟩

/-- The product of two one-dimensional representations of rank-zero groups is
one-dimensional, also after a rank cast. -/
theorem finrank_rankCast_product_of_zero_zero {a b m : ℕ} (ha : a = 0) (hb : b = 0)
    (h : a + b = m)
    (Z : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (Z' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hZ : Module.finrank ℂ Z = 1) (hZ' : Module.finrank ℂ Z' = 1) :
    Module.finrank ℂ ((generalLinearRankCast T h).obj
      ((T.binaryNormalizedProductFunctor a b).obj (Z, Z'))) = 1 := by
  let _ := T.topology
  subst h
  change Module.finrank ℂ ((T.binaryNormalizedProductFunctor a b).obj (Z, Z')) = 1
  rw [(T.binaryZeroZeroTensorEquiv ha hb (Z, Z')).toLinearEquiv.finrank_eq]
  change Module.finrank ℂ (Z ⊗[ℂ] Z') = 1
  rw [Module.finrank_tensorProduct, hZ, hZ']

end BinaryProducts

/-! ## Leibniz pieces of a product of two supercuspidal representations

Adapted from `NonadjacentLeibnizPieces`; the Leibniz filtration and the supercuspidal
derivative pattern are supplied by their published proofs. -/

section Leibniz

/-- The only graded piece of a filtration of length one is linearly equivalent to
the whole representation. -/
theorem nonempty_linearEquiv_graded_of_length_one {R G : Type*} [CommRing R] [Monoid G]
    {X : Rep.{uV} R G} {n : ℕ} (s : ObjectRepFiltration X n) (hn : n = 1) (i : Fin n) :
    Nonempty ((s.gradedRepresentation i) ≃ₗ[R] X) := by
  subst hn
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have h0 : s.subrepresentation 0 = ⊥ := s.subrepresentation_zero
  have h1 : s.subrepresentation (Fin.last 1) = ⊤ := s.subrepresentation_last
  let q := ((s.step (0 : Fin 1).castSucc).lowerInUpper (s.step (0 : Fin 1).succ)
    (Discrete.mk PUnit.unit)).toSubmodule
  have hq : q = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hv' : ((s.step (0 : Fin 1).succ).obj (Discrete.mk PUnit.unit)).toSubmodule.subtype v ∈
        (s.subrepresentation 0).toSubmodule := hv
    rw [h0] at hv'
    exact (Submodule.mem_bot R).2 (Subtype.ext hv')
  have htop : (s.subrepresentation (Fin.last 1)).toSubmodule = ⊤ := by rw [h1]; rfl
  exact ⟨(Submodule.quotEquivOfEqBot q hq).trans (LinearEquiv.ofTop _ htop)⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The derivative pattern of a supercuspidal representation: vanishing derivatives
of intermediate order and a one-dimensional top derivative. -/
def SupercuspidalDerivativePattern {a : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) : Prop :=
  letI := T.topology
  (∀ (i : ℕ) (hi : i ≤ a), 0 < i → i < a →
    Subsingleton ((generalLinearDerivative T ψ a i hi).obj A)) ∧
  Module.finrank ℂ ((generalLinearDerivative T ψ a a le_rfl).obj A) = 1

/-- An irreducible representation of positive rank with vanishing proper Jacquet
modules has the derivative pattern (BZ77 4.4, published as
`supercuspidalDerivatives`). -/
theorem supercuspidalDerivativePattern_of_isSupercuspidal {k : ℕ} (hk : 0 < k)
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (hirr : letI := T.topology; X.IsIrreducible)
    (hsc : letI := T.topology; IsSupercuspidal X.representation) :
    SupercuspidalDerivativePattern F T ψ X := by
  let _ := T.topology
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨h1, h2⟩ := supercuspidalDerivatives.{uF, uV} F T ψ n X hirr hsc
  exact ⟨fun i hi h0 hlt => h1 i hi h0 hlt, h2⟩

/-- Every supercuspidal representation of positive rank has the derivative pattern. -/
theorem supercuspidalDerivativePattern {k : ℕ} (hk : 0 < k)
    (ρ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) :
    SupercuspidalDerivativePattern F T ψ ρ.obj :=
  supercuspidalDerivativePattern_of_isSupercuspidal F T ψ hk ρ.obj ρ.property.1 ρ.property.2

/-- At an intermediate order, a Leibniz piece of `A × B` for factors with the
supercuspidal derivative pattern is zero, or has index `(0, b)` and is equivalent to
the rank cast of `A`, or has index `(a, 0)` and is equivalent to the rank cast of `B`. -/
theorem leibnizPiece_cases {a b d : ℕ} (hd0 : 0 < d) (hd1 : d < a + b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hA : SupercuspidalDerivativePattern F T ψ A) (hB : SupercuspidalDerivativePattern F T ψ B)
    (x : LeibnizIndex a b d) :
    letI := T.topology
    Subsingleton ((leibnizPiece T ψ a b d x).obj (A, B)) ∨
      (x.val = (0, b) ∧ ∃ h : a = a + b - d,
        Nonempty (((generalLinearRankCast T h).obj A).representation.Equiv
          ((leibnizPiece T ψ a b d x).obj (A, B)).ρ)) ∨
      (x.val = (a, 0) ∧ ∃ h : b = a + b - d,
        Nonempty (((generalLinearRankCast T h).obj B).representation.Equiv
          ((leibnizPiece T ψ a b d x).obj (A, B)).ρ)) := by
  let _ := T.topology
  obtain ⟨⟨i, j⟩, hx⟩ := x
  obtain ⟨hia, hjb, hij⟩ := mem_leibnizIndices.1 hx
  dsimp only at hij hia hjb
  by_cases hi : 0 < i ∧ i < a
  · exact Or.inl (subsingleton_rankCast_product F T _ _ _ (Or.inl (hA.1 i hia hi.1 hi.2)))
  by_cases hj : 0 < j ∧ j < b
  · exact Or.inl (subsingleton_rankCast_product F T _ _ _ (Or.inr (hB.1 j hjb hj.1 hj.2)))
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    have hjb' : j = b := by omega
    subst hjb'
    exact Or.inr (Or.inl ⟨rfl, by omega, nonempty_equiv_rankCast_product_right F T
      (Nat.sub_self j) (leibnizIndices_rank hx) (by dsimp only; omega) _ _ hB.2⟩)
  · have hia' : i = a := by omega
    have hj0 : j = 0 := by omega
    subst hia' hj0
    exact Or.inr (Or.inr ⟨rfl, by omega, nonempty_equiv_rankCast_product_left F T
      (Nat.sub_self i) (leibnizIndices_rank hx) (by dsimp only; omega) _ _ hA.2⟩)

/-- The unique Leibniz piece at the top order is one-dimensional. -/
theorem finrank_leibnizPiece_top {a b : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hA : SupercuspidalDerivativePattern F T ψ A) (hB : SupercuspidalDerivativePattern F T ψ B)
    (x : LeibnizIndex a b (a + b)) :
    Module.finrank ℂ ((leibnizPiece T ψ a b (a + b) x).obj (A, B)) = 1 := by
  let _ := T.topology
  obtain ⟨⟨i, j⟩, hx⟩ := x
  obtain ⟨hia, hjb, hij⟩ := mem_leibnizIndices.1 hx
  dsimp only at hij hia hjb
  have hi : i = a := by omega
  have hj : j = b := by omega
  subst hi hj
  exact finrank_rankCast_product_of_zero_zero F T (Nat.sub_self i) (Nat.sub_self j)
    (leibnizIndices_rank hx) _ _ hA.2 hB.2

theorem card_leibnizIndices_top (a b : ℕ) : (leibnizIndices a b (a + b)).card = 1 := by
  rw [leibnizIndices_top, Finset.card_singleton]

/-- The top derivative of `A × B` is one-dimensional when both factors have the
supercuspidal derivative pattern. -/
theorem finrank_top_binary {a b d : ℕ} (hd : d ≤ a + b) (hda : d = a + b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hA : SupercuspidalDerivativePattern F T ψ A) (hB : SupercuspidalDerivativePattern F T ψ B) :
    letI := T.topology
    Module.finrank ℂ ((generalLinearDerivative T ψ (a + b) d hd).obj
      ((T.binaryNormalizedProductFunctor a b).obj (A, B))) = 1 := by
  let _ := T.topology
  subst hda
  obtain ⟨e, s, hs⟩ := (generalLinearDerivativeLeibnizFiltration.{uF, uV} F T).filtration
    T ψ a b (a + b) le_rfl
  let i0 : Fin (leibnizIndices a b (a + b)).card := ⟨0, by rw [card_leibnizIndices_top]; omega⟩
  obtain ⟨L⟩ := nonempty_linearEquiv_graded_of_length_one
    (CuspidalSupport.objectFiltrationAt s (A, B)) (card_leibnizIndices_top a b) i0
  obtain ⟨φ⟩ := hs i0
  exact L.finrank_eq.symm.trans
    ((Representation.equivOfIso (φ.app (A, B))).toLinearEquiv.finrank_eq.trans
      (finrank_leibnizPiece_top F T ψ A B hA hB _))

/-- The Leibniz piece of index `(0, b)` is equivalent to the rank cast of `A`. -/
theorem leibnizPiece_zero_top {a b d : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hB : SupercuspidalDerivativePattern F T ψ B) (x : LeibnizIndex a b d)
    (hx : x.val = (0, b)) :
    letI := T.topology
    ∃ h : a = a + b - d,
      Nonempty (((generalLinearRankCast T h).obj A).representation.Equiv
        ((leibnizPiece T ψ a b d x).obj (A, B)).ρ) := by
  let _ := T.topology
  obtain ⟨⟨i, j⟩, hmem⟩ := x
  obtain ⟨hia, hjb, hij⟩ := mem_leibnizIndices.1 hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
  dsimp only at hij hia hjb
  exact ⟨by omega, nonempty_equiv_rankCast_product_right F T (Nat.sub_self _)
    (leibnizIndices_rank hmem) (by dsimp only; omega) _ _ hB.2⟩

/-- The Leibniz piece of index `(a, 0)` is equivalent to the rank cast of `B`. -/
theorem leibnizPiece_top_zero {a b d : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hA : SupercuspidalDerivativePattern F T ψ A) (x : LeibnizIndex a b d)
    (hx : x.val = (a, 0)) :
    letI := T.topology
    ∃ h : b = a + b - d,
      Nonempty (((generalLinearRankCast T h).obj B).representation.Equiv
        ((leibnizPiece T ψ a b d x).obj (A, B)).ρ) := by
  let _ := T.topology
  obtain ⟨⟨i, j⟩, hmem⟩ := x
  obtain ⟨hia, hjb, hij⟩ := mem_leibnizIndices.1 hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
  dsimp only at hij hia hjb
  exact ⟨by omega, nonempty_equiv_rankCast_product_left F T (Nat.sub_self _)
    (leibnizIndices_rank hmem) (by dsimp only; omega) _ _ hA.2⟩

/-- Away from the orders `0`, `a`, `b` and `a + b`, the derivative of `A × B`
vanishes when both factors have the supercuspidal derivative pattern. -/
theorem subsingleton_derivative_binary {a b d : ℕ} (hd : d ≤ a + b) (hd0 : 0 < d)
    (hd1 : d < a + b) (hda : d ≠ a) (hdb : d ≠ b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (hA : SupercuspidalDerivativePattern F T ψ A) (hB : SupercuspidalDerivativePattern F T ψ B) :
    letI := T.topology
    Subsingleton ((generalLinearDerivative T ψ (a + b) d hd).obj
      ((T.binaryNormalizedProductFunctor a b).obj (A, B))) := by
  let _ := T.topology
  obtain ⟨e, s, hs⟩ := (generalLinearDerivativeLeibnizFiltration.{uF, uV} F T).filtration
    T ψ a b d hd
  refine objectRepFiltrationSubsingleton.{0, uF, max uF uV} ℂ
    (GeneralLinear (a + b - d) F.Carrier) _ _ (CuspidalSupport.objectFiltrationAt s (A, B))
    (fun i => ?_)
  obtain ⟨φ⟩ := hs i
  have hp : Subsingleton ((leibnizPiece T ψ a b d (e.symm i)).obj (A, B)) := by
    have hsum := leibnizIndices_sum (e.symm i).property
    rcases leibnizPiece_cases F T ψ hd0 hd1 A B hA hB (e.symm i) with h | ⟨hx, -⟩ | ⟨hx, -⟩
    · exact h
    · rw [hx] at hsum
      exact absurd hsum.symm (by dsimp only; omega)
    · rw [hx] at hsum
      exact absurd hsum.symm (by dsimp only; omega)
  exact (Representation.equivOfIso (φ.app (A, B))).toLinearEquiv.toEquiv.injective.subsingleton

/-- Irreducibility survives rank casts. -/
theorem isIrreducible_rankCast {a b : ℕ} (h : a = b)
    {A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
    (hA : letI := T.topology; A.IsIrreducible) :
    letI := T.topology; ((generalLinearRankCast T h).obj A).IsIrreducible := by
  subst h
  exact hA

/-- At the order `r` the derivative of `A × B`, for two supercuspidal representations
`A`, `B` of `GL_r`, has a filtration of length two with irreducible factors, one of
which is equivalent to the rank cast of `B`. -/
theorem exists_twoStep_filtration_binary {r : ℕ} (hr : 0 < r) (hd : r ≤ r + r)
    (A B : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    ∃ s : ObjectRepFiltration (SmoothRep.toRep.obj ((generalLinearDerivative T ψ (r + r) r hd).obj
        ((T.binaryNormalizedProductFunctor r r).obj (A.obj, B.obj)))) 2,
      s.HasSimpleFactors ∧ ∃ (i : Fin 2) (h : r = r + r - r),
        Nonempty ((s.gradedRepresentation i).ρ.Equiv
          ((generalLinearRankCast T h).obj B.obj).representation) := by
  let _ := T.topology
  have hA := supercuspidalDerivativePattern F T ψ hr A
  have hB := supercuspidalDerivativePattern F T ψ hr B
  obtain ⟨e, s, hs⟩ := (generalLinearDerivativeLeibnizFiltration.{uF, uV} F T).filtration
    T ψ r r r hd
  let s0 := CuspidalSupport.objectFiltrationAt s (A.obj, B.obj)
  let x0 : LeibnizIndex r r r := ⟨(0, r), mem_leibnizIndices.2 ⟨Nat.zero_le _, le_rfl, by omega⟩⟩
  let x1 : LeibnizIndex r r r := ⟨(r, 0), mem_leibnizIndices.2 ⟨le_rfl, Nat.zero_le _, by omega⟩⟩
  let P : Fin (leibnizIndices r r r).card → Prop := fun i =>
    (e.symm i).val = (0, r) ∨ (e.symm i).val = (r, 0)
  have hP : ∀ i, ¬ P i → Subsingleton (s0.gradedRepresentation i) := fun i hi => by
    obtain ⟨φ⟩ := hs i
    have hp : Subsingleton ((leibnizPiece T ψ r r r (e.symm i)).obj (A.obj, B.obj)) := by
      rcases leibnizPiece_cases F T ψ hr (by omega) A.obj B.obj hA hB (e.symm i) with
        h | ⟨hx, -⟩ | ⟨hx, -⟩
      · exact h
      · exact absurd (Or.inl hx) hi
      · exact absurd (Or.inr hx) hi
    exact (Representation.equivOfIso (φ.app (A.obj, B.obj))).toLinearEquiv.toEquiv.injective.subsingleton
  obtain ⟨m, e', t, ht⟩ := ObjectRepFiltration.zeroFactorDeletionTheorem.{0, uF, max uF uV} ℂ
    (GeneralLinear (r + r - r) F.Carrier) _ _ s0 P hP
  have hx01 : x0 ≠ x1 := fun h => by
    have := congrArg (fun x : LeibnizIndex r r r => x.val.1) h
    dsimp only [x0, x1] at this
    omega
  let f : Fin 2 → {i // P i} := ![⟨e x0, Or.inl (by rw [Equiv.symm_apply_apply])⟩, ⟨e x1, Or.inr (by rw [Equiv.symm_apply_apply])⟩]
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd (e.injective (congrArg Subtype.val hab)) hx01
      · exact absurd (e.injective (congrArg Subtype.val hab)).symm hx01
      · rfl
    · rintro ⟨i, hi | hi⟩
      · refine ⟨0, Subtype.ext ?_⟩
        change e x0 = i
        rw [← e.apply_symm_apply i]
        exact congrArg e (Subtype.ext hi.symm)
      · refine ⟨1, Subtype.ext ?_⟩
        change e x1 = i
        rw [← e.apply_symm_apply i]
        exact congrArg e (Subtype.ext hi.symm)
  have hm : m = 2 := Fin.equiv_iff_eq.mp ⟨e'.trans (Equiv.ofBijective f hf).symm⟩
  subst hm
  -- Each selected graded piece is equivalent to a rank cast of `A` or `B`.
  have hpiece : ∀ i, P i → Representation.IsIrreducible (s0.gradedRepresentation i).ρ := by
    intro i hi
    obtain ⟨φ⟩ := hs i
    let eφ := Representation.equivOfIso (φ.app (A.obj, B.obj))
    rcases hi with hx | hx
    · obtain ⟨h, ⟨eA⟩⟩ := leibnizPiece_zero_top F T ψ A.obj B.obj hB (e.symm i) hx
      exact (Weil.IsomorphismInvariance.irreducible_iff (eφ.trans eA.symm)).mpr
        (isIrreducible_rankCast F T h A.property.1)
    · obtain ⟨h, ⟨eB⟩⟩ := leibnizPiece_top_zero F T ψ A.obj B.obj hA (e.symm i) hx
      exact (Weil.IsomorphismInvariance.irreducible_iff (eφ.trans eB.symm)).mpr
        (isIrreducible_rankCast F T h B.property.1)
  refine ⟨t, fun j => ?_, e'.symm ⟨e x1, Or.inr (by rw [Equiv.symm_apply_apply])⟩, ?_⟩
  · obtain ⟨ej⟩ := ht j
    exact (Weil.IsomorphismInvariance.irreducible_iff ej).mpr (hpiece _ (e' j).property)
  · have h1 := ht (e'.symm ⟨e x1, Or.inr (by rw [Equiv.symm_apply_apply])⟩)
    rw [Equiv.apply_symm_apply] at h1
    obtain ⟨e1⟩ := h1
    have h2 := hs (e x1)
    rw [Equiv.symm_apply_apply] at h2
    obtain ⟨φ⟩ := h2
    obtain ⟨h, ⟨eB⟩⟩ := leibnizPiece_top_zero F T ψ A.obj B.obj hA x1 rfl
    exact ⟨h, ⟨(e1.trans (Representation.equivOfIso (φ.app (A.obj, B.obj)))).trans eB.symm⟩⟩

end Leibniz

/-! ## Elementary facts on irreducible subquotients -/

section Elementary

universe uG uW

/-- An irreducible representation has a nonzero vector. -/
theorem exists_ne_zero_of_isIrreducible {G : Type uG} [Group G]
    {V : Type uW} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (hρ : ρ.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext w
  rw [hcon w]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

/-- An irreducible representation on which the group acts trivially is a line. -/
theorem nonempty_linearEquiv_of_isIrreducible_of_trivial {G : Type uG} [Group G]
    {V : Type uW} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (hρ : ρ.IsIrreducible) (h1 : ∀ g, ρ g = 1) : Nonempty (V ≃ₗ[ℂ] ℂ) := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible hρ
  let S : Subrepresentation ρ :=
    { toSubmodule := Submodule.span ℂ {v}
      apply_mem_toSubmodule := fun g w hw => by
        rw [h1 g]
        exact hw }
  have hS : S ≠ ⊥ := by
    intro h
    apply hv
    have hmem : v ∈ S.toSubmodule := Submodule.subset_span (Set.mem_singleton v)
    rw [h] at hmem
    exact hmem
  have htop : Submodule.span ℂ {v} = ⊤ := by
    have := (hρ.eq_bot_or_eq_top S).resolve_left hS
    exact congrArg Subrepresentation.toSubmodule this
  exact ⟨((LinearEquiv.toSpanNonzeroSingleton ℂ V v hv).trans
    (LinearEquiv.ofTop _ htop)).symm⟩

/-- No irreducible representation is a subquotient of a zero representation. -/
theorem not_isSubquotient_of_subsingleton {G : Type uG} [Group G] [TopologicalSpace G]
    {σ X : SmoothRep.{0, uG, uW} ℂ G} (hσ : σ.IsIrreducible) (hX : Subsingleton X) :
    ¬ SmoothRep.IsSubquotient σ X := by
  intro h
  obtain ⟨S, q, hq⟩ := SmoothRep.isSubquotient_iff_representation.mp h
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible hσ
  obtain ⟨x, rfl⟩ := hq v
  apply hv
  have hx : x = 0 := Subtype.ext (Subsingleton.elim _ _)
  rw [hx, map_zero]

/-- Smooth subquotients compose. -/
theorem isSubquotient_trans {G : Type uG} [Group G] [TopologicalSpace G]
    {A B C : SmoothRep.{0, uG, uW} ℂ G} (h₁ : SmoothRep.IsSubquotient A B)
    (h₂ : SmoothRep.IsSubquotient B C) : SmoothRep.IsSubquotient A C :=
  SmoothRep.isSubquotient_iff_representation.mpr
    ((SmoothRep.isSubquotient_iff_representation.mp h₂).trans
      (SmoothRep.isSubquotient_iff_representation.mp h₁))

end Elementary

/-! ## A two-step filtration argument

Let `A` carry a filtration `0 ⊂ S ⊂ A` with irreducible factors, one of which is
equivalent to `ξ`. If `K ↪ A ↠ θ` is exact, `K ≠ 0`, and `ξ` does not embed in `K`,
then `θ` is a quotient of `ξ`. -/

section TwoStep

open LengthCriterionProof (quotientRep lower)

universe uG uA uX uK uQ

variable {G : Type uG} [Group G]

/-- The intertwiner out of a successive quotient induced by an intertwiner that
vanishes on the lower step. -/
def quotientRepLift {V : Type uA} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {Q : Type uQ} [AddCommGroup Q] [Module ℂ Q] {θ : Representation ℂ G Q}
    (S T : Subrepresentation ρ) (g : ρ.IntertwiningMap θ) (hS : ∀ v ∈ S, g v = 0) :
    (quotientRep S T).IntertwiningMap θ where
  toLinearMap := (lower S T).liftQ (g.toLinearMap ∘ₗ T.toSubmodule.subtype)
    (fun v hv => LinearMap.mem_ker.mpr (hS (v : V) hv))
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (lower S T) x
    change g (ρ h (v : V)) = θ h (g (v : V))
    exact Representation.IntertwiningMap.isIntertwining _ _ g h (v : V)

theorem quotientRepLift_surjective {V : Type uA} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {Q : Type uQ} [AddCommGroup Q] [Module ℂ Q]
    {θ : Representation ℂ G Q} (S T : Subrepresentation ρ) (g : ρ.IntertwiningMap θ)
    (hS : ∀ v ∈ S, g v = 0) (hT : ∀ y, ∃ v ∈ T, g v = y) :
    Function.Surjective (quotientRepLift S T g hS) := by
  intro y
  obtain ⟨v, hv, rfl⟩ := hT y
  exact ⟨(lower S T).mkQ ⟨v, hv⟩, rfl⟩

/-- The two-step argument. -/
theorem twoStep_quotient {A : Rep.{uA} ℂ G} (s : ObjectRepFiltration A 2)
    (hs : s.HasSimpleFactors)
    {X : Type uX} [AddCommGroup X] [Module ℂ X] {ξ : Representation ℂ G X}
    (i : Fin 2) (ei : Nonempty ((s.gradedRepresentation i).ρ.Equiv ξ))
    {K : Type uK} [AddCommGroup K] [Module ℂ K] {κ : Representation ℂ G K}
    (f : κ.IntertwiningMap A.ρ) (hf : Function.Injective f) [Nontrivial K]
    (hX : ∀ j : ξ.IntertwiningMap κ, ¬ Function.Injective j)
    {Q : Type uQ} [AddCommGroup Q] [Module ℂ Q] {θ : Representation ℂ G Q}
    (g : A.ρ.IntertwiningMap θ) (hg : Function.Surjective g)
    (hfg : ∀ v, g v = 0 ↔ ∃ w, f w = v) :
    ∃ φ : ξ.IntertwiningMap θ, Function.Surjective φ := by
  obtain ⟨e⟩ := ei
  have hcov := (LengthCriterionProof.hasSimpleFactors_iff_covBy s).1 hs
  have h0 : (⊥ : Subrepresentation A.ρ) ⋖ s.subrepresentation 1 := by
    have := hcov 0
    rw [show (0 : Fin 2).castSucc = 0 from rfl, ObjectRepFiltration.subrepresentation_zero]
      at this
    exact this
  have h1 : s.subrepresentation 1 ⋖ ⊤ := by
    have := hcov 1
    rw [show (1 : Fin 2).succ = Fin.last 2 from rfl, ObjectRepFiltration.subrepresentation_last]
      at this
    exact this
  have hlast : ∀ v : A, v ∈ s.subrepresentation (Fin.last 2) := fun v => by
    rw [ObjectRepFiltration.subrepresentation_last]
    exact LengthCriterionProof.mem_top
  have hzero : ∀ v : A, v ∈ s.subrepresentation 0 → v = 0 := fun v hv => by
    rw [ObjectRepFiltration.subrepresentation_zero] at hv
    exact LengthCriterionProof.mem_bot_iff.mp hv
  let S := s.subrepresentation 1
  let Kr := f.range
  have memKr : ∀ v, v ∈ Kr ↔ g v = 0 := fun v => (Representation.IntertwiningMap.mem_range _ _ f v).trans (hfg v).symm
  have hKne : Kr ≠ ⊥ := by
    intro hK
    obtain ⟨w, hw⟩ := exists_ne (0 : K)
    have hmem : f w ∈ Kr := (Representation.IntertwiningMap.mem_range _ _ f _).mpr ⟨w, rfl⟩
    rw [hK] at hmem
    exact hw (hf ((LengthCriterionProof.mem_bot_iff.mp hmem).trans (map_zero f).symm))
  have hinf : ¬ S ≤ Kr → S ⊓ Kr = ⊥ := fun hSK =>
    ((h0.eq_or_eq bot_le inf_le_left).resolve_right fun h => hSK (h.symm.trans_le inf_le_right))
  have hsup : S ⊓ Kr = ⊥ → S ⊔ Kr = ⊤ := fun hb =>
    (h1.eq_or_eq le_sup_left le_top).resolve_left fun h => hKne (by
      apply le_antisymm _ bot_le
      rw [← hb]
      exact le_inf (le_sup_right.trans_eq h) le_rfl)
  fin_cases i
  · -- The bottom factor `S` is equivalent to `ξ`.
    have hSK : ¬ S ≤ Kr := by
      intro hSK
      let U := LengthTwo.comap f S
      let u : U.toRepresentation.IntertwiningMap (quotientRep (s.subrepresentation 0) S) :=
        { toLinearMap := (lower (s.subrepresentation 0) S).mkQ ∘ₗ
            { toFun := fun w => ⟨f (w : K), w.2⟩
              map_add' := fun a b => Subtype.ext (map_add f (a : K) b)
              map_smul' := fun c a => Subtype.ext (map_smul f c (a : K)) }
          isIntertwining' := fun h => LinearMap.ext fun w => by
            change (lower (s.subrepresentation 0) S).mkQ ⟨f (κ h (w : K)), _⟩ =
              (lower (s.subrepresentation 0) S).mkQ ⟨A.ρ h (f (w : K)), _⟩
            congr 2
            exact Representation.IntertwiningMap.isIntertwining _ _ f h (w : K) }
      have hu : Function.Bijective u := by
        constructor
        · intro a b hab
          have hab' := (Submodule.Quotient.eq _).mp hab
          have h0' := hzero _ hab'
          apply Subtype.ext
          apply hf
          change f a - f b = 0 at h0'
          exact sub_eq_zero.mp h0'
        · intro y
          obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.mkQ_surjective _ y
          obtain ⟨w, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ f v).mp (hSK hv)
          exact ⟨⟨w, hv⟩, rfl⟩
      let eU := (u.ofBijective hu).trans e
      apply hX ((FunctorLengthTwo.subtypeMap U).comp eU.symm.toIntertwiningMap)
      intro a b hab
      exact eU.symm.injective (Subtype.ext hab)
    have ht := hsup (hinf hSK)
    have hT : ∀ y, ∃ v ∈ S, g v = y := fun y => by
      obtain ⟨m, rfl⟩ := hg y
      have hm : m ∈ S ⊔ Kr := by rw [ht]; exact LengthCriterionProof.mem_top
      obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.mp hm
      exact ⟨a, ha, by rw [map_add, (memKr b).mp hb', add_zero]⟩
    have hS0 : ∀ v ∈ s.subrepresentation 0, g v = 0 := fun v hv => by
      rw [hzero v hv, map_zero]
    exact ⟨(quotientRepLift _ S g hS0).comp e.symm.toIntertwiningMap,
      (quotientRepLift_surjective _ S g hS0 hT).comp e.symm.surjective⟩
  · -- The top factor `A / S` is equivalent to `ξ`.
    have hSK : S ≤ Kr := by
      by_contra hSK
      have hb := hinf hSK
      have ht := hsup hb
      let u : κ.IntertwiningMap (quotientRep S (s.subrepresentation (Fin.last 2))) :=
        { toLinearMap := (lower S (s.subrepresentation (Fin.last 2))).mkQ ∘ₗ
            { toFun := fun w => ⟨f w, hlast _⟩
              map_add' := fun a b => Subtype.ext (map_add f a b)
              map_smul' := fun c a => Subtype.ext (map_smul f c a) }
          isIntertwining' := fun h => LinearMap.ext fun w => by
            change (lower S (s.subrepresentation (Fin.last 2))).mkQ ⟨f (κ h w), _⟩ =
              (lower S (s.subrepresentation (Fin.last 2))).mkQ ⟨A.ρ h (f w), _⟩
            congr 2
            exact Representation.IntertwiningMap.isIntertwining _ _ f h w }
      have hu : Function.Bijective u := by
        constructor
        · intro a b hab
          have hab' := (Submodule.Quotient.eq _).mp hab
          have hmem : f a - f b ∈ S ⊓ Kr :=
            ⟨hab', (Representation.IntertwiningMap.mem_range _ _ f _).mpr ⟨a - b, map_sub f a b⟩⟩
          rw [hb] at hmem
          exact hf (sub_eq_zero.mp (LengthCriterionProof.mem_bot_iff.mp hmem))
        · intro y
          obtain ⟨⟨m, hm⟩, rfl⟩ := Submodule.mkQ_surjective _ y
          have hm' : m ∈ S ⊔ Kr := by rw [ht]; exact LengthCriterionProof.mem_top
          obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.mp hm'
          obtain ⟨w, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ f b).mp hb'
          refine ⟨w, (Submodule.Quotient.eq _).mpr ?_⟩
          change f w - (a + f w) ∈ S.toSubmodule
          rw [sub_add_cancel_right]
          exact S.toSubmodule.neg_mem ha
      let eK := (u.ofBijective hu).trans e
      exact hX eK.symm.toIntertwiningMap eK.symm.injective
    have hS1 : ∀ v ∈ S, g v = 0 := fun v hv => (memKr v).mp (hSK hv)
    have hT : ∀ y, ∃ v ∈ s.subrepresentation (Fin.last 2), g v = y := fun y => by
      obtain ⟨m, rfl⟩ := hg y
      exact ⟨m, hlast m, rfl⟩
    exact ⟨(quotientRepLift S _ g hS1).comp e.symm.toIntertwiningMap,
      (quotientRepLift_surjective S _ g hS1 hT).comp e.symm.surjective⟩

end TwoStep

/-! ## Members of a segment, and the orders `0` and `deg Δ` -/

section Generic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

open PadicField.TopologicalData

/-- The actual supercuspidal representative `ν^i A` of the member `ν^i ρ` of `Δ`. -/
def memberRep (Δ : T.Segment.{uV, uF})
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (i : Fin Δ.length) :
    letI := T.topology
    SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (Δ.member (i : ℕ)).rank) :=
  letI := T.topology
  SupercuspidalRep.twist (T.determinantPowerCharacter Δ.rank ((i : ℕ) : ℝ))
    (T.isOpen_ker_determinantPowerCharacter _ _)
    (T.ker_determinant_le_ker_determinantPowerCharacter _ _) A

theorem memberRep_represent (Δ : T.Segment.{uV, uF})
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) (i : Fin Δ.length) :
    (Δ.member (i : ℕ)).IsRepresentedBy (memberRep F T Δ A i) := by
  let _ := T.topology
  change T.supercuspidalClassRealPowerTwist Δ.rank ((i : ℕ) : ℝ) A.isoClass =
    T.supercuspidalClassRealPowerTwist Δ.rank ((i : ℕ) : ℝ) Δ.base.cls
  exact congrArg _ hA

theorem sum_rank_member (Δ : T.Segment.{uV, uF}) :
    ∑ i : Fin Δ.length, (Δ.member (i : ℕ)).rank = Δ.degree := by
  simp [Segment.member, Segment.degree]

/-- `i(A, νA, …, ν^(m-1) A)` is the cuspidal product of the member representatives. -/
theorem segmentInduced_eq_cuspidalProductInduced (Δ : T.Segment.{uV, uF})
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)) :
    T.segmentInduced A.obj Δ.length Δ.rank_pos =
      T.cuspidalProductInduced (fun i : Fin Δ.length => Δ.member (i : ℕ))
        (sum_rank_member F T Δ) (memberRep F T Δ A) :=
  rfl

/-- At order `0`, an irreducible subquotient of the derivative of a segment head has
the whole segment as support. -/
theorem orderZero_support
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (Δ : T.Segment.{uV, uF})
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentHead Δ π) (k : ℕ) (hk : k ≤ Δ.degree) (hk0 : k = 0)
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.degree - k) F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (hsub : letI := T.topology
      SmoothRep.IsSubquotient σ ((generalLinearDerivative T ψ Δ.degree k hk).obj π)) :
    ∃ (s : Multiset (T.CuspidalDatum.{uV, uF})) (B : Option (T.Segment.{uV, uF})),
      T.IsSupercuspidalSupport σ s ∧ Segment.IsTerminalTruncation B Δ ∧
        {ρ | ρ ∈ s} = Segment.optionalSupport B := by
  let _ := T.topology
  subst hk0
  obtain ⟨A, hA, -, q, hq, -⟩ := hπ
  refine ⟨Δ.cuspidalContent, some Δ, ⟨Δ.length, fun i => Δ.member (i : ℕ), rfl, ?_⟩,
    ⟨subset_rfl, Δ.last_mem_support⟩, Set.ext fun ρ => Δ.mem_cuspidalContent ρ⟩
  refine ⟨sum_rank_member F T Δ, memberRep F T Δ A, memberRep_represent F T Δ A hA, hσ, ?_⟩
  exact isSubquotient_trans hsub (SmoothRep.IsQuotient.isSubquotient ⟨SmoothRep.ofHom q, hq⟩)

/-- A normalized product for a block shape of a rank-zero group has a carrier
linearly equivalent to `ℂ`. Adapted from `rankZeroNormalizedProductLinearEquiv` in
`OrderedMultisegmentHeadReduction`, with the rank given by an equation. -/
def rankZeroProductLinearEquiv {N : ℕ} (hN : N = 0) (B : GeneralLinear.BlockShape N)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup N
    Induction.SmoothFunctions (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B)
        ((B.blockTensor σ).comp (B.leviProjection F.Carrier))) ≃ₗ[ℂ] ℂ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup N
  have : Subsingleton (GeneralLinear N F.Carrier) := subsingleton_of_rank_eq_zero hN
  letI : IsEmpty (Fin B.length) := ⟨fun i =>
    (Fin.cast hN (B.indexEquiv ⟨i, ⟨0, B.positive i⟩⟩)).elim0⟩
  let ρ := Representation.trivial ℂ (GeneralLinear N F.Carrier) (PiTensorProduct ℂ V)
  have hρ : IsSmooth ρ := by
    intro v
    exact ⟨⊤, fun _ => rfl⟩
  have hP : B.parabolic F.Carrier = ⊤ := by
    apply top_unique
    intro g _
    rw [Subsingleton.elim g 1]
    exact (B.parabolic F.Carrier).one_mem
  let e := Induction.smoothInducedTopEquiv (B.parabolic F.Carrier) hP
    (twist (T.parabolicHalfModulus B)
      ((B.blockTensor σ).comp (B.leviProjection F.Carrier))) ρ
    (by intro g; rw [Subsingleton.elim g 1, map_one]; rfl) hρ
  exact e.toLinearEquiv.trans (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := V) _)

/-- An irreducible representation of a rank-zero group is a subquotient of every
one-dimensional representation. -/
theorem isSubquotient_of_rank_eq_zero {N : ℕ} (hN : N = 0)
    {σ X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)}
    (hσ : letI := T.topology; σ.IsIrreducible) (eX : X ≃ₗ[ℂ] ℂ) :
    letI := T.topology; SmoothRep.IsSubquotient σ X := by
  let _ := T.topology
  obtain ⟨eσ⟩ := nonempty_linearEquiv_of_isIrreducible_of_trivial hσ
    (representation_apply_of_rank_eq_zero hN σ.representation)
  let e : X.representation.Equiv σ.representation :=
    Representation.Equiv.mk (eX.trans eσ.symm) fun g => by
      rw [representation_apply_of_rank_eq_zero hN X.representation g,
        representation_apply_of_rank_eq_zero hN σ.representation g]
      rfl
  exact SmoothRep.isSubquotient_iff_representation.mpr (WeylBranchPieces.IsSubquotient.of_equiv e)

/-- At the top order, an irreducible subquotient of the derivative of any
representation has the empty support. -/
theorem topOrder_support (Δ : T.Segment.{uV, uF}) (k : ℕ) (hkt : k = Δ.degree)
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.degree - k) F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible) :
    ∃ (s : Multiset (T.CuspidalDatum.{uV, uF})) (B : Option (T.Segment.{uV, uF})),
      T.IsSupercuspidalSupport σ s ∧ Segment.IsTerminalTruncation B Δ ∧
        {ρ | ρ ∈ s} = Segment.optionalSupport B := by
  let _ := T.topology
  have hN : Δ.degree - k = 0 := by omega
  have h0 : ∑ i : Fin 0, ((Fin.elim0 i : T.CuspidalDatum.{uV, uF})).rank = Δ.degree - k := by
    rw [hN]
    rfl
  let A : ∀ i : Fin 0, SupercuspidalRep.{uF, uV} (F := F.Carrier)
      (n := ((Fin.elim0 i : T.CuspidalDatum.{uV, uF})).rank) := fun i => Fin.elim0 i
  refine ⟨0, none, ⟨0, Fin.elim0, by simp, h0, A, fun i => Fin.elim0 i, hσ, ?_⟩, trivial,
    Set.ext fun ρ => by simp [Segment.optionalSupport]⟩
  apply isSubquotient_of_rank_eq_zero F T hN hσ
  exact rankZeroProductLinearEquiv F T hN (T.cuspidalShape Fin.elim0 h0)
    (fun i => (A i).obj.representation)

/-- Supercuspidality and irreducibility survive the entry-preserving reindex. -/
theorem isIrreducible_isSupercuspidal_comp_reindex {a b : ℕ} (h : a = b)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear a F.Carrier) V) (hρ : ρ.IsIrreducible)
    (hsc : letI := T.topology; IsSupercuspidal ρ) :
    letI := T.topology
    Representation.IsIrreducible
        (ρ.comp (reindex (R := F.Carrier) (finCongr h)).symm.toMonoidHom) ∧
      IsSupercuspidal (ρ.comp (reindex (R := F.Carrier) (finCongr h)).symm.toMonoidHom) := by
  let _ := T.topology
  subst h
  have e : Representation.Equiv ρ
      (ρ.comp (reindex (R := F.Carrier) (finCongr (rfl : a = a))).symm.toMonoidHom) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun g => by
      change ρ g = ρ ((reindex (R := F.Carrier) (finCongr rfl)).symm g)
      rw [reindex_finCongr_rfl]
      rfl
  exact ⟨(Weil.IsomorphismInvariance.irreducible_iff e).mp hρ, isSupercuspidal_of_equiv e hsc⟩

/-- For a segment of length one, the induced representation `i(A)` is irreducible
and supercuspidal. -/
theorem lengthOne_segmentInduced (Δ : T.Segment.{uV, uF}) (hΔ : Δ.length = 1)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)) :
    letI := T.topology
    (T.segmentInduced A.obj Δ.length Δ.rank_pos).IsIrreducible ∧
      IsSupercuspidal (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation := by
  let _ := T.topology
  let B := GeneralLinear.BlockShape.uniform Δ.length Δ.rank Δ.rank_pos
  have hB : B.length = 1 := hΔ
  let i0 : Fin B.length := B.singleBlockIndex hB
  let X := memberRep F T Δ A i0
  let e := T.singleBlockNormalizedProductEquiv B hB
    (fun i => (T.segmentFactors A.obj Δ.length Δ.rank_pos i).representation)
    (fun i => SmoothRep.isSmooth _) i0
  obtain ⟨h1, h2⟩ := isIrreducible_isSupercuspidal_comp_reindex F T (B.singleBlock_size hB i0)
    X.obj.representation X.property.1 X.property.2
  exact ⟨(Weil.IsomorphismInvariance.irreducible_iff e).mpr h1,
    isSupercuspidal_of_equiv e.symm h2⟩

/-- A segment head of a segment of length one is irreducible and supercuspidal. -/
theorem lengthOne_head_isSupercuspidal (Δ : T.Segment.{uV, uF}) (hΔ : Δ.length = 1)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentHead Δ π) :
    letI := T.topology
    π.IsIrreducible ∧ IsSupercuspidal π.representation := by
  let _ := T.topology
  obtain ⟨A, -, hirr, q, hq, -⟩ := hπ
  obtain ⟨hI, hsc⟩ := lengthOne_segmentInduced F T Δ hΔ A
  have := hI
  have hq0 : q ≠ 0 := by
    intro hz
    obtain ⟨w, hw⟩ := exists_ne_zero_of_isIrreducible hirr
    obtain ⟨v, hv⟩ := hq w
    apply hw
    rw [← hv, hz]
    rfl
  have hqi := (Representation.IsIrreducible.injective_or_eq_zero q).resolve_right hq0
  exact ⟨hirr, isSupercuspidal_of_equiv (q.ofBijective ⟨hqi, hq⟩) hsc⟩

/-- For a segment of length one, every irreducible subquotient of every derivative
of a segment head has the support required by the target. -/
theorem lengthOne_support
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (Δ : T.Segment.{uV, uF})
    (hΔ : Δ.length = 1)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentHead Δ π) (k : ℕ) (hk : k ≤ Δ.degree)
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.degree - k) F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (hsub : letI := T.topology
      SmoothRep.IsSubquotient σ ((generalLinearDerivative T ψ Δ.degree k hk).obj π)) :
    ∃ (s : Multiset (T.CuspidalDatum.{uV, uF})) (B : Option (T.Segment.{uV, uF})),
      T.IsSupercuspidalSupport σ s ∧ Segment.IsTerminalTruncation B Δ ∧
        {ρ | ρ ∈ s} = Segment.optionalSupport B := by
  let _ := T.topology
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · exact orderZero_support F T ψ Δ π hπ k hk hk0 σ hσ hsub
  rcases eq_or_lt_of_le hk with hkt | hkt
  · exact topOrder_support F T Δ k hkt σ hσ
  exfalso
  obtain ⟨hirr, hsc⟩ := lengthOne_head_isSupercuspidal F T Δ hΔ π hπ
  have hpat := supercuspidalDerivativePattern_of_isSupercuspidal F T ψ Δ.degree_pos π hirr hsc
  exact not_isSubquotient_of_subsingleton hσ (hpat.1 k hk hk0 hkt) hsub

end Generic

/-! ## Shapes, supports and the reducibility of `ρ × νρ`

The first three comparisons are copied from `TwoSupercuspidalBinaryProductBridge`. -/

section Shapes

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

open PadicField.TopologicalData

/-- The published binary shape is the standard two-block shape. -/
theorem binary_eq_twoBlocks {a c : ℕ} (ha : 0 < a) (hc : 0 < c) :
    BlockShape.binary a c ha hc = Shahidi.twoBlocks a c ha hc := by
  unfold BlockShape.binary Shahidi.twoBlocks
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Normalized products on equal shapes agree on heterogeneously equal factors. -/
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

/-- For positive ranks, the binary product of `(A, B)` is the normalized product
of `twoBlockFactors A B` on the standard two-block shape. -/
theorem binaryNormalizedProductFunctor_obj_eq_twoBlocks {a c : ℕ} (ha : 0 < a) (hc : 0 < c)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear c F.Carrier)) :
    letI := T.topology
    (T.binaryNormalizedProductFunctor a c).obj (A, B) =
      (T.normalizedProductInductionFunctor (Shahidi.twoBlocks a c ha hc)).obj
        (twoBlockFactors ha hc A B) := by
  let _ := T.topology
  rw [T.binaryNormalizedProductFunctor_of_pos ha hc]
  change (T.normalizedProductInductionFunctor (BlockShape.binary a c ha hc)).obj
      ((T.binaryPairFamilyFunctor ha hc).obj (A, B)) = _
  apply normalizedProductInductionFunctor_obj_congr F T (binary_eq_twoBlocks ha hc)
  apply Function.hfunext rfl
  intro i i' hi
  cases hi
  fin_cases i <;> rfl

/-- `A0 × A1` is reducible when `[A1] = ν[A0]`. This is the only use of the
published reducibility theorem `twoSupercuspidalAdjacentProductReducible`. -/
theorem not_isIrreducible_binary {r : ℕ} (hr : 0 < r)
    (A0 A1 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (hA : letI := T.topology
      A1.isoClass = T.supercuspidalClassRealPowerTwist r 1 A0.isoClass) :
    letI := T.topology
    ¬ ((T.binaryNormalizedProductFunctor r r).obj (A0.obj, A1.obj)).IsIrreducible := by
  let _ := T.topology
  rw [binaryNormalizedProductFunctor_obj_eq_twoBlocks F T hr hr]
  exact twoSupercuspidalAdjacentProductReducible.{uF, uV} F T r hr A0 A1 (Or.inl hA)

/-- The pair of cuspidal data `([A0], [A1])` of rank `r`. -/
def pairDatum {r : ℕ} (hr : 0 < r)
    (A0 A1 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    Fin 2 → T.CuspidalDatum.{uV, uF} :=
  letI := T.topology
  fun i => ⟨r, hr, (![A0, A1] i).isoClass⟩

/-- The representatives `(A0, A1)` of `pairDatum`. -/
def pairRep {r : ℕ} (hr : 0 < r)
    (A0 A1 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (pairDatum F T hr A0 A1 i).rank) :=
  fun i => ![A0, A1] i

theorem sum_rank_pairDatum {r : ℕ} (hr : 0 < r)
    (A0 A1 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    ∑ i, (pairDatum F T hr A0 A1 i).rank = r + r := by
  rw [Fin.sum_univ_two]
  rfl

theorem pairRep_represent {r : ℕ} (hr : 0 < r)
    (A0 A1 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (i : Fin 2) : (pairDatum F T hr A0 A1 i).IsRepresentedBy (pairRep F T hr A0 A1 i) :=
  rfl

/-- The binary product `A0 × A1` is the cuspidal product of `pairDatum`. -/
theorem binary_eq_cuspidalProductInduced {r : ℕ} (hr : 0 < r)
    (A0 A1 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    (T.binaryNormalizedProductFunctor r r).obj (A0.obj, A1.obj) =
      T.cuspidalProductInduced (pairDatum F T hr A0 A1) (sum_rank_pairDatum F T hr A0 A1)
        (pairRep F T hr A0 A1) := by
  let _ := T.topology
  rw [T.binaryNormalizedProductFunctor_of_pos hr hr]
  change (T.normalizedProductInductionFunctor (BlockShape.binary r r hr hr)).obj
      ((T.binaryPairFamilyFunctor hr hr).obj (A0.obj, A1.obj)) = _
  refine normalizedProductInductionFunctor_obj_congr F T ?_ _ _ ?_
  · unfold BlockShape.binary cuspidalShape
    congr 1
    funext i
    fin_cases i <;> rfl
  · apply Function.hfunext rfl
    intro i i' hi
    cases hi
    fin_cases i <;> rfl

/-- A rank cast of a cuspidal product is the cuspidal product on the new rank. -/
theorem rankCast_cuspidalProductInduced {k a b : ℕ} (ρ : Fin k → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρ i).rank = a) (hab : a = b)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank)) :
    letI := T.topology
    (generalLinearRankCast T hab).obj (T.cuspidalProductInduced ρ h A) =
      T.cuspidalProductInduced ρ (h.trans hab) A := by
  subst hab
  rfl

/-- For a segment of length two, `i(A, νA)` is the rank cast of the binary product of
the member representatives. -/
theorem segmentInduced_eq_binary (Δ : T.Segment.{uV, uF}) (hΔ : Δ.length = 2)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (hn : Δ.rank + Δ.rank = Δ.degree)
    (A0 A1 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (h0 : A0 = memberRep F T Δ A ⟨0, by omega⟩) (h1 : A1 = memberRep F T Δ A ⟨1, by omega⟩) :
    letI := T.topology
    T.segmentInduced A.obj Δ.length Δ.rank_pos = (generalLinearRankCast T hn).obj
      ((T.binaryNormalizedProductFunctor Δ.rank Δ.rank).obj (A0.obj, A1.obj)) := by
  let _ := T.topology
  rw [binary_eq_cuspidalProductInduced F T Δ.rank_pos, rankCast_cuspidalProductInduced,
    segmentInduced_eq_cuspidalProductInduced]
  subst h0 h1
  obtain ⟨b, m, hm⟩ := Δ
  change m = 2 at hΔ
  subst hΔ
  unfold cuspidalProductInduced
  refine normalizedProductInductionFunctor_obj_congr F T rfl _ _ ?_
  apply Function.hfunext rfl
  intro i i' hi
  cases hi
  fin_cases i <;> rfl

/-- A representation-level subquotient of the rank cast of `B` is a subquotient of
the rank cast of the carrier lift of `B`. -/
theorem isSubquotient_rankCast_universeLift {d m : ℕ} (h : d = m)
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear d F.Carrier))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hs : letI := T.topology
      WeylBranchPieces.IsSubquotient ((generalLinearRankCast T h).obj B).representation
        σ.representation) :
    letI := T.topology
    SmoothRep.IsSubquotient σ
      ((generalLinearRankCast T h).obj (SmoothRep.universeLift.{uF} B)) := by
  let _ := T.topology
  subst h
  exact SmoothRep.isSubquotient_iff_representation.mpr
    ((WeylBranchPieces.IsSubquotient.of_equiv (SmoothRep.universeLiftEquiv.{uF} B).symm).trans hs)

theorem nontrivial_rankCast_universeLift {d m : ℕ} (h : d = m)
    (B : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := d)) :
    letI := T.topology
    Nontrivial ((generalLinearRankCast T h).obj (SmoothRep.universeLift.{uF} B.obj)) := by
  let _ := T.topology
  subst h
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible B.property.1
  have : Nontrivial B.obj := nontrivial_of_ne v 0 hv
  exact (SmoothRep.universeLiftEquiv.{uF} B.obj).toLinearEquiv.injective.nontrivial

/-- An irreducible subquotient of the rank cast of (the carrier lift of) a
supercuspidal `B` has the singleton support `{[B]}`. -/
theorem support_of_isSubquotient {d m : ℕ} (hd : 0 < d) (h : d = m)
    (B : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := d))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (hs : letI := T.topology
      SmoothRep.IsSubquotient σ
        ((generalLinearRankCast T h).obj (SmoothRep.universeLift.{uF} B.obj))) :
    letI := T.topology
    T.IsSupercuspidalSupport σ {(⟨d, hd, B.isoClass⟩ : T.CuspidalDatum.{uV, uF})} := by
  let _ := T.topology
  have := nontrivial_rankCast_universeLift F T h B
  obtain ⟨-, k, ρ, hρ, hh, AA, hAA, -, hsub⟩ :=
    OrderedCuspidalProductHeadShift.irreducible_support_of_injective F T hd h B
      ((generalLinearRankCast T h).obj (SmoothRep.universeLift.{uF} B.obj)) (𝟙 _)
      (fun _ _ hxy => hxy)
  exact ⟨k, ρ, hρ, hh, AA, hAA, hσ, isSubquotient_trans hs hsub⟩

end Shapes

/-! ## The length-two core -/

section Core

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

open PadicField.TopologicalData

/-- BZ77 4.7(b) in the form used here: if `K ⊂ ρ_1 × ⋯ × ρ_m` has level `j + 1`,
then no rank cast of a supercuspidal `B` with `ν[B] ∉ {ρ_1, …, ρ_m}` embeds in
`K^(j+1)`. -/
theorem no_shifted_embedding {N m : ℕ} (ρs : Fin m → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρs i).rank = N + 1)
    (As : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρs i).rank))
    (hAs : ∀ i, (ρs i).IsRepresentedBy (As i))
    (X : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (N + 1) F.Carrier))
    (hX : X = T.cuspidalProductInduced ρs h As)
    (K : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (N + 1) F.Carrier))
    (ι : letI := T.topology; K ⟶ X)
    (hι : letI := T.topology; Function.Injective (SmoothRep.hom ι))
    (j : ℕ) (hj : j + 1 ≤ N + 1)
    (hlev : letI := T.topology; level T ψ ((generalLinearRestriction T N).obj K) = j + 1)
    {d : ℕ} (hd : 0 < d)
    (B : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := d))
    (hdj : d = N + 1 - (j + 1))
    (hB : letI := T.topology
      (⟨d, hd, B.isoClass⟩ : T.CuspidalDatum.{uV, uF}).twist 1 ∉
        (List.ofFn ρs : Multiset (T.CuspidalDatum.{uV, uF})))
    (φ : letI := T.topology
      ((generalLinearRankCast T hdj).obj B.obj).representation.IntertwiningMap
        ((generalLinearDerivative T ψ (N + 1) (j + 1) hj).obj K).representation)
    (hφ : Function.Injective φ) : False := by
  let _ := T.topology
  subst hX
  have hk : 0 < j + 1 ∧ j + 1 ≤ N + 1 := ⟨Nat.succ_pos j, hj⟩
  let σ' := (generalLinearRankCast T hdj).obj (SmoothRep.universeLift.{uF} B.obj)
  have hσ' : σ'.IsIrreducible := by
    subst hdj
    exact (SmoothRep.isIrreducible_universeLift_iff B.obj).mpr B.property.1
  have e : σ'.representation.Equiv ((generalLinearRankCast T hdj).obj B.obj).representation := by
    subst hdj
    exact (SmoothRep.universeLiftEquiv.{uF} B.obj).symm
  have hsub : IsIrreducibleSubrepresentation
      ((mirabolicDerivativeOfOrder T ψ N (j + 1) hk).obj
        ((generalLinearRestriction T N).obj K)).representation σ'.representation := by
    rw [← RestrictionBridge.generalLinearDerivative_succ_obj_eq T ψ hj hk K]
    exact ⟨hσ', φ.comp e.toIntertwiningMap, hφ.comp e.injective⟩
  have hsupp := support_of_isSubquotient F T hd hdj B σ' hσ'
    (SmoothRep.IsQuotient.isSubquotient ⟨𝟙 σ', fun x => ⟨x, rfl⟩⟩)
  have hle := cuspidalProductMirabolicSupportShift.{uF, uV} F T ψ N m ρs h As hAs
    ((generalLinearRestriction T N).obj K) ((generalLinearRestriction T N).map ι)
    (fun x y hxy => hι hxy) (j + 1) hk hlev σ' hsub _ hsupp
  rw [Multiset.map_singleton, Multiset.singleton_le] at hle
  exact hB hle

/-- The cuspidal datum `ν[A1]` is not among `[A0], [A1]` when `[A1] = ν[A0]`. -/
theorem twist_not_mem_pairDatum {r : ℕ} (hr : 0 < r)
    (A0 A1 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (hA : letI := T.topology
      A1.isoClass = T.supercuspidalClassRealPowerTwist r 1 A0.isoClass) :
    letI := T.topology
    (⟨r, hr, A1.isoClass⟩ : T.CuspidalDatum.{uV, uF}).twist 1 ∉
      (List.ofFn (pairDatum F T hr A0 A1) : Multiset (T.CuspidalDatum.{uV, uF})) := by
  let _ := T.topology
  let ρ0 : T.CuspidalDatum.{uV, uF} := ⟨r, hr, A0.isoClass⟩
  have h1 : (⟨r, hr, A1.isoClass⟩ : T.CuspidalDatum.{uV, uF}) = ρ0.twist 1 := by
    rw [hA]
    rfl
  rw [Multiset.mem_coe, List.mem_ofFn]
  rintro ⟨i, hi⟩
  fin_cases i
  · change ρ0 = _ at hi
    rw [h1, CuspidalDatum.twist_twist] at hi
    have h2 : ρ0.twist ((2 : ℤ) : ℝ) = ρ0 := by
      rw [show ((2 : ℤ) : ℝ) = 1 + 1 by norm_num]
      exact hi.symm
    exact absurd ((cuspidalIntegralTwistFreeness.{uF, uV} F T ρ0 2).mp h2) (by norm_num)
  · exact OrderedCuspidalProductTwistOne.twist_one_ne_self T _ hi.symm

/-- `no_shifted_embedding` on a rank `n` that is only known to equal `N + 1`. Callers
pass the rank equation as a proof, so that no rank arithmetic is unfolded
definitionally when the lemma is applied. -/
theorem no_shifted_embedding_cast {n N m : ℕ} (hn : n = N + 1)
    (ρs : Fin m → T.CuspidalDatum.{uV, uF})
    (h : ∑ i, (ρs i).rank = n)
    (As : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρs i).rank))
    (hAs : ∀ i, (ρs i).IsRepresentedBy (As i))
    (X : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hX : X = T.cuspidalProductInduced ρs h As)
    (K : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (ι : letI := T.topology; K ⟶ X)
    (hι : letI := T.topology; Function.Injective (SmoothRep.hom ι))
    (j : ℕ) (hj : j + 1 ≤ n)
    (hlev : letI := T.topology
      level T ψ ((generalLinearRestriction T N).obj ((generalLinearRankCast T hn).obj K)) =
        j + 1)
    {d : ℕ} (hd : 0 < d)
    (B : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := d))
    (hdj : d = n - (j + 1))
    (hB : letI := T.topology
      (⟨d, hd, B.isoClass⟩ : T.CuspidalDatum.{uV, uF}).twist 1 ∉
        (List.ofFn ρs : Multiset (T.CuspidalDatum.{uV, uF})))
    (φ : letI := T.topology
      ((generalLinearRankCast T hdj).obj B.obj).representation.IntertwiningMap
        ((generalLinearDerivative T ψ n (j + 1) hj).obj K).representation)
    (hφ : Function.Injective φ) : False := by
  subst hn
  exact no_shifted_embedding F T ψ ρs h As hAs X hX K ι hι j hj hlev hd B hdj hB φ hφ

/-- The order-`r` case of the core: `π^(r)` is a quotient of the rank cast of `A1`. -/
theorem core_mid {r : ℕ} (hr : 0 < r)
    (A0 A1 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (hA : letI := T.topology
      A1.isoClass = T.supercuspidalClassRealPowerTwist r 1 A0.isoClass)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + r) F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible)
    (q : letI := T.topology; (T.binaryNormalizedProductFunctor r r).obj (A0.obj, A1.obj) ⟶ π)
    (hq : letI := T.topology; Function.Surjective (SmoothRep.hom q))
    (htop : letI := T.topology
      Nontrivial ((generalLinearDerivative T ψ (r + r) (r + r) le_rfl).obj π))
    (hd : r ≤ r + r)
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + r - r) F.Carrier))
    (hsub : letI := T.topology
      SmoothRep.IsSubquotient σ ((generalLinearDerivative T ψ (r + r) r hd).obj π)) :
    letI := T.topology
    ∃ h : r = r + r - r, WeylBranchPieces.IsSubquotient
      ((generalLinearRankCast T h).obj A1.obj).representation σ.representation := by
  let _ := T.topology
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hpat0 := supercuspidalDerivativePattern F T ψ hr A0
  have hpat1 := supercuspidalDerivativePattern F T ψ hr A1
  let K := SmoothRep.kernel q
  let ι := SmoothRep.kernelι q
  have hSE := LevelCalculus.isShortExact_kernelι q hq
  have hSEd : ∀ (k : ℕ) (hk : k ≤ r' + 1 + (r' + 1)), LevelCalculus.IsShortExact
      ((generalLinearDerivative T ψ _ k hk).map ι) ((generalLinearDerivative T ψ _ k hk).map q) :=
    fun k hk => LevelCalculus.isShortExact_map (generalLinearDerivativeExactness F T ψ _ k hk) hSE
  -- `K` is nonzero, since otherwise `A0 × A1 ≅ π` would be irreducible.
  have hKnt : Nontrivial K := by
    by_contra hK
    rw [not_nontrivial_iff_subsingleton] at hK
    have hqi : Function.Injective (SmoothRep.hom q) := by
      intro x y hxy
      have hmem : x - y ∈ LinearMap.ker (SmoothRep.hom q).toLinearMap := by
        rw [LinearMap.mem_ker, map_sub]
        exact sub_eq_zero.mpr hxy
      rw [← hSE.exact] at hmem
      obtain ⟨z, hz⟩ := hmem
      rw [Subsingleton.elim z 0, map_zero] at hz
      exact sub_eq_zero.mp hz.symm
    exact not_isIrreducible_binary F T hr A0 A1 hA
      ((Weil.IsomorphismInvariance.irreducible_iff
        ((SmoothRep.hom q).ofBijective ⟨hqi, hq⟩)).mpr hπ)
  -- The derivatives of `K` vanish at every positive order other than `r`.
  have hvan : ∀ (k : ℕ) (hk : k ≤ r' + 1 + (r' + 1)), 0 < k → k ≠ r' + 1 →
      Subsingleton ((generalLinearDerivative T ψ _ k hk).obj K) := by
    intro k hk hk0 hkr
    rcases lt_or_eq_of_le hk with hlt | heq
    · have := subsingleton_derivative_binary F T ψ hk hk0 hlt hkr hkr A0.obj A1.obj hpat0 hpat1
      exact (hSEd k hk).injective.subsingleton
    · subst heq
      by_contra hK
      rw [not_subsingleton_iff_nontrivial] at hK
      let D := generalLinearDerivative T ψ (r' + 1 + (r' + 1)) (r' + 1 + (r' + 1)) hk
      obtain ⟨z, hz⟩ := exists_ne (0 : D.obj K)
      let v := SmoothRep.hom (D.map ι) z
      have hv : v ≠ 0 := fun h0 => hz ((hSEd _ hk).injective (h0.trans (map_zero _).symm))
      have hqv : SmoothRep.hom (D.map q) v = 0 := by
        have hmem : v ∈ LinearMap.range (SmoothRep.hom (D.map ι)).toLinearMap := ⟨z, rfl⟩
        rw [(hSEd _ hk).exact] at hmem
        exact hmem
      have h1 := finrank_top_binary F T ψ hk rfl A0.obj A1.obj hpat0 hpat1
      obtain ⟨w, hw⟩ := exists_ne (0 : D.obj π)
      obtain ⟨u, rfl⟩ := (hSEd _ hk).surjective w
      obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp h1 u
      apply hw
      rw [map_smul, hqv, smul_zero]
  -- Hence the level of `K|P` is `r`.
  have hN : r' + 1 + (r' + 1) = r' + 1 + r' + 1 := by omega
  let W := (generalLinearRestriction T (r' + 1 + r')).obj ((generalLinearRankCast T hN).obj K)
  have hnd : ∀ (k : ℕ) (hk : k ≤ r' + 1 + (r' + 1)), 0 < k →
      (Nontrivial ((generalLinearDerivative T ψ _ k hk).obj K) ↔ HasNonzeroDerivative T ψ W k) :=
    fun k hk hk0 => RestrictionBridge.nontrivial_generalLinearDerivative_iff T ψ hN hk hk0 K
  have hWnt : Nontrivial W := (RestrictionBridge.nontrivial_generalLinearRankCast_iff T hN K).mpr hKnt
  have hlev : level T ψ W = r' + 1 := by
    have h0 : level T ψ W ≠ 0 := (LevelCalculus.level_pos T ψ W).ne'
    have hle := level_le T ψ W
    have hnz := LevelCalculus.hasNonzeroDerivative_level T ψ W h0
    by_contra hne
    have hnt := (hnd _ (by omega) (by omega)).mpr hnz
    exact not_nontrivial_iff_subsingleton.mpr (hvan _ (by omega) (by omega) hne) hnt
  have hKr : Nontrivial ((generalLinearDerivative T ψ _ (r' + 1) hd).obj K) := by
    have hnz := LevelCalculus.hasNonzeroDerivative_level T ψ W (by omega)
    rw [hlev] at hnz
    exact (hnd _ hd hr).mpr hnz
  -- The two-step filtration of `(A0 × A1)^(r)` and the two-step argument.
  obtain ⟨s, hs, i0, hdj, ei⟩ := exists_twoStep_filtration_binary F T ψ hr hd A0 A1
  have hX : ∀ j : ((generalLinearRankCast T hdj).obj A1.obj).representation.IntertwiningMap
      ((generalLinearDerivative T ψ _ (r' + 1) hd).obj K).representation,
      ¬ Function.Injective j := fun j hj =>
    no_shifted_embedding_cast F T ψ hN (pairDatum F T hr A0 A1)
      (sum_rank_pairDatum F T hr A0 A1) (pairRep F T hr A0 A1) (pairRep_represent F T hr A0 A1)
      _ (binary_eq_cuspidalProductInduced F T hr A0 A1) K ι hSE.injective r' hd hlev hr A1 hdj
      (twist_not_mem_pairDatum F T hr A0 A1 hA) j hj
  obtain ⟨φ, hφ⟩ := twoStep_quotient s hs i0 ei
    (SmoothRep.hom ((generalLinearDerivative T ψ _ (r' + 1) hd).map ι)) (hSEd _ hd).injective hX
    (SmoothRep.hom ((generalLinearDerivative T ψ _ (r' + 1) hd).map q)) (hSEd _ hd).surjective
    (fun v => by
      have h := SetLike.ext_iff.mp (hSEd _ hd).exact v
      rw [LinearMap.mem_range, LinearMap.mem_ker] at h
      exact h.symm)
  exact ⟨hdj, (WeylBranchPieces.IsSubquotient.of_surjective φ hφ).trans
    (SmoothRep.isSubquotient_iff_representation.mp hsub)⟩

/-- The core on `GL_n`, `n = r + r`: an irreducible subquotient of an intermediate
derivative of an irreducible quotient of `A0 × A1` occurs only in order `r`, as a
subquotient of the rank cast of `A1`. -/
theorem core {r : ℕ} (hr : 0 < r)
    (A0 A1 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (hA : letI := T.topology
      A1.isoClass = T.supercuspidalClassRealPowerTwist r 1 A0.isoClass)
    {n : ℕ} (hn : r + r = n)
    (I : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hI : letI := T.topology; I = (generalLinearRankCast T hn).obj
      ((T.binaryNormalizedProductFunctor r r).obj (A0.obj, A1.obj)))
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible)
    (q : letI := T.topology; I.representation.IntertwiningMap π.representation)
    (hq : letI := T.topology; Function.Surjective q)
    (htop : letI := T.topology; Nontrivial ((generalLinearDerivative T ψ n n le_rfl).obj π))
    (k : ℕ) (hk : k ≤ n) (hk0 : 0 < k) (hkn : k < n)
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (hsub : letI := T.topology
      SmoothRep.IsSubquotient σ ((generalLinearDerivative T ψ n k hk).obj π)) :
    letI := T.topology
    k = r ∧ ∃ h : r = n - k, WeylBranchPieces.IsSubquotient
      ((generalLinearRankCast T h).obj A1.obj).representation σ.representation := by
  let _ := T.topology
  subst hn
  subst hI
  let qh : (T.binaryNormalizedProductFunctor r r).obj (A0.obj, A1.obj) ⟶ π := SmoothRep.ofHom q
  by_cases hkr : k = r
  · subst hkr
    exact ⟨rfl, core_mid F T ψ hr A0 A1 hA π hπ qh hq htop hk σ hsub⟩
  · exfalso
    have := subsingleton_derivative_binary F T ψ hk hk0 hkn hkr hkr A0.obj A1.obj
      (supercuspidalDerivativePattern F T ψ hr A0) (supercuspidalDerivativePattern F T ψ hr A1)
    have hSE := LevelCalculus.isShortExact_map (generalLinearDerivativeExactness F T ψ _ k hk)
      (LevelCalculus.isShortExact_kernelι qh hq)
    have : Subsingleton ((generalLinearDerivative T ψ (r + r) k hk).obj π) :=
      hSE.surjective.subsingleton
    exact not_isSubquotient_of_subsingleton hσ this hsub

/-- For a segment `Δ = [ρ, νρ]` of length two, every irreducible subquotient of every
derivative of a segment head has the support required by the target: the whole
segment in order `0`, the empty support in order `deg Δ`, and `{νρ}` in order
`rank Δ` (the only other order with a nonzero derivative). -/
theorem lengthTwo_support (Δ : T.Segment.{uV, uF}) (hΔ : Δ.length = 2)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentHead Δ π) (k : ℕ) (hk : k ≤ Δ.degree)
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.degree - k) F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (hsub : letI := T.topology
      SmoothRep.IsSubquotient σ ((generalLinearDerivative T ψ Δ.degree k hk).obj π)) :
    ∃ (s : Multiset (T.CuspidalDatum.{uV, uF})) (B : Option (T.Segment.{uV, uF})),
      T.IsSupercuspidalSupport σ s ∧ Segment.IsTerminalTruncation B Δ ∧
        {ρ | ρ ∈ s} = Segment.optionalSupport B := by
  let _ := T.topology
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · exact orderZero_support F T ψ Δ π hπ k hk hk0 σ hσ hsub
  rcases eq_or_lt_of_le hk with hkt | hkt
  · exact topOrder_support F T Δ k hkt σ hσ
  have htop := segmentHeadTopDerivativeNontrivial T ψ Δ π hπ
  obtain ⟨A, hA, hirr, q, hq, -⟩ := hπ
  let i0 : Fin Δ.length := ⟨0, by omega⟩
  let i1 : Fin Δ.length := ⟨1, by omega⟩
  let A0 : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank) := memberRep F T Δ A i0
  let A1 : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank) := memberRep F T Δ A i1
  have hA01 : A1.isoClass = T.supercuspidalClassRealPowerTwist Δ.rank 1 A0.isoClass := by
    have e0 : A0.isoClass = (Δ.member 0).cls := memberRep_represent F T Δ A hA i0
    have e1 : A1.isoClass = (Δ.member 1).cls := memberRep_represent F T Δ A hA i1
    rw [e0, e1]
    change T.supercuspidalClassRealPowerTwist Δ.rank ((1 : ℕ) : ℝ) Δ.base.cls =
      T.supercuspidalClassRealPowerTwist Δ.rank 1
        (T.supercuspidalClassRealPowerTwist Δ.rank ((0 : ℕ) : ℝ) Δ.base.cls)
    rw [supercuspidalClassRealPowerTwist_add]
    norm_num
  have hn : Δ.rank + Δ.rank = Δ.degree := by
    change Δ.rank + Δ.rank = Δ.length * Δ.rank
    rw [hΔ]
    omega
  obtain ⟨-, h, hs⟩ := core F T ψ Δ.rank_pos A0 A1 hA01 hn _
    (segmentInduced_eq_binary F T Δ hΔ A hn A0 A1 rfl rfl) π hirr q hq htop k hk hk0 hkt σ hσ hsub
  have hsupp := support_of_isSubquotient F T Δ.rank_pos h A1 σ hσ
    (isSubquotient_rankCast_universeLift F T h A1.obj σ hs)
  have hρ1 : (⟨Δ.rank, Δ.rank_pos, A1.isoClass⟩ : T.CuspidalDatum.{uV, uF}) = Δ.member 1 := by
    have e1 : A1.isoClass = (Δ.member 1).cls := memberRep_represent F T Δ A hA i1
    rw [e1]
    rfl
  rw [hρ1] at hsupp
  have hlast : Δ.last = Δ.member 1 := by
    unfold Segment.last
    rw [hΔ]
  have hE : (⟨Δ.member 1, 1, one_pos⟩ : T.Segment.{uV, uF}).support = {Δ.member 1} := by
    ext ρ
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain rfl : i = 0 := by
        change i < 1 at hi
        omega
      simp [Segment.member_zero]
    · rintro rfl
      exact ⟨0, one_pos, by simp⟩
  refine ⟨{Δ.member 1}, some ⟨Δ.member 1, 1, one_pos⟩, hsupp, ⟨?_, ?_⟩, ?_⟩
  · rw [hE, Set.singleton_subset_iff]
    exact Δ.member_mem_support (by omega)
  · rw [hE, hlast]
    rfl
  · change _ = (⟨Δ.member 1, 1, one_pos⟩ : T.Segment.{uV, uF}).support
    rw [hE]
    ext ρ
    simp

end Core

end Langlands.Classification.SegmentHeadDerivativeSupportLengthTwo
