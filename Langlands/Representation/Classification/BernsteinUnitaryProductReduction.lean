import Langlands.Representation.Classification.BernsteinUnitaryStatement
import Langlands.Representation.Induction.EmptyProductUnit
import Langlands.Representation.Induction.HeadTailBinaryProduct
import Langlands.Representation.Induction.UnitaryProof
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Binary reduction for Bernstein's finite normalized product theorem. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The positive-rank binary irreducibility assertion sufficient for the
finite-block formulation. Unitarizability of the product is already proved. -/
def BernsteinPositiveBinaryUnitaryProductIrreducibility : Prop :=
  letI := T.topology
  ∀ (a b : ℕ), 0 < a → 0 < b →
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)),
      Representation.IsIrreducible A.representation → IsUnitarizable A.representation →
      Representation.IsIrreducible B.representation → IsUnitarizable B.representation →
        Representation.IsIrreducible
          ((T.binaryNormalizedProductFunctor a b).obj (A, B)).representation

private theorem irreducible_one_dimensional {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hV : Module.finrank ℂ V = 1) : Representation.IsIrreducible ρ := by
  have : IsSimpleOrder (Submodule ℂ V) :=
    is_simple_module_of_finrank_eq_one (K := ℂ) hV
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · intro S
    rcases eq_bot_or_eq_top S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

private theorem irreducible_of_iso {G : Type uF} [Group G] [TopologicalSpace G]
    {A B : SmoothRep.{0, uF, max uF uV} ℂ G}
    (e : A ≅ B) (hB : Representation.IsIrreducible B.representation) :
    Representation.IsIrreducible A.representation :=
  (isIrreducible_iff_of_equiv (SmoothRep.equivOfIso e)).mpr hB

/-- The actual empty product is irreducible and unitarizable, in every
representation universe allowed by the target statement. -/
theorem bernstein_emptyProduct_irreducible_unitarizable
    (B : BlockShape 0)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    Representation.IsIrreducible
        ((T.normalizedProductInductionFunctor B).obj σ).representation ∧
      IsUnitarizable ((T.normalizedProductInductionFunctor B).obj σ).representation := by
  let := T.topology
  let U := T.binaryProductUnit.{uF, max uF uV}
  let e := SmoothRep.equivOfIso (T.emptyProductUnitIso B σ)
  have hU : Representation.IsIrreducible U.representation :=
    irreducible_one_dimensional U.representation T.finrank_binaryProductUnit
  let b : InvariantPositiveForm
      (Representation.trivial ℂ (GeneralLinear 0 F.Carrier) ℂ) :=
    { toInnerProductCore := InnerProductSpace.toCore
      invariant := by intro g v w; rfl }
  let eU : U.representation.Equiv
      (Representation.trivial ℂ (GeneralLinear 0 F.Carrier) ℂ) :=
    Representation.Equiv.mk (ULift.moduleEquiv (R := ℂ) (M := ℂ))
      (fun _ => by ext v; rfl)
  exact ⟨(isIrreducible_iff_of_equiv e).mpr hU,
    (isUnitarizable_iff_of_equiv e).mpr ⟨b.ofEquiv eU⟩⟩

/-- The published positive-rank preservation theorem also gives the empty
rank-zero product, using the actual unit isomorphism. -/
theorem bernstein_product_unitarizable (n : ℕ) (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hσ : letI := T.topology; ∀ i, IsUnitarizable (σ i).representation) :
    letI := T.topology
    IsUnitarizable ((T.normalizedProductInductionFunctor B).obj σ).representation := by
  cases n with
  | zero => exact (bernstein_emptyProduct_irreducible_unitarizable F T B σ).2
  | succ n =>
    exact glNormalizedProductInductionUnitarity.{uF, uV}
      p F T (n + 1) (Nat.succ_pos n) B σ hσ

private theorem irreducible_rankCast {a b : ℕ} (h : a = b)
    (A : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hA : letI := T.topology; Representation.IsIrreducible A.representation) :
    letI := T.topology
    Representation.IsIrreducible ((Derivative.generalLinearRankCast T h).obj A).representation := by
  subst b
  exact hA

private theorem irreducible_reindex {a b : ℕ} (h : a = b)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear a F.Carrier) V)
    (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible
      (ρ.comp (GeneralLinear.reindex (R := F.Carrier) (finCongr h)).symm.toMonoidHom) := by
  subst b
  rw [GeneralLinear.reindex_finCongr_rfl]
  exact hρ

private theorem singleBlock_irreducible {n : ℕ} (B : BlockShape n) (hB : B.length = 1)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hσ : letI := T.topology; ∀ i, Representation.IsIrreducible (σ i).representation) :
    letI := T.topology
    Representation.IsIrreducible
      ((T.normalizedProductInductionFunctor B).obj σ).representation := by
  let := T.topology
  let i := B.singleBlockIndex hB
  let e := T.singleBlockNormalizedProductEquiv B hB
    (fun j => (σ j).representation) (fun j => (σ j).property) i
  exact (isIrreducible_iff_of_equiv e).mpr
    (irreducible_reindex F (B.singleBlock_size hB i) (σ i).representation (hσ i))

private theorem headTail_irreducible
    (hbinary : BernsteinPositiveBinaryUnitaryProductIrreducibility.{uF, uV} F T)
    {n k : ℕ} (B : BlockShape n) (hlen : B.length = k + 2)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hσ : letI := T.topology
      ∀ i, Representation.IsIrreducible (σ i).representation ∧
        IsUnitarizable (σ i).representation)
    (hCi : letI := T.topology
      Representation.IsIrreducible
        ((T.normalizedProductInductionFunctor (B.tailShape hlen)).obj
          (fun j => σ (B.tailIndex hlen j))).representation) :
    letI := T.topology
    Representation.IsIrreducible
      ((T.normalizedProductInductionFunctor B).obj σ).representation := by
  let := T.topology
  let C := (T.normalizedProductInductionFunctor (B.tailShape hlen)).obj
    (fun j => σ (B.tailIndex hlen j))
  have hCu : IsUnitarizable C.representation :=
    bernstein_product_unitarizable F T _ (B.tailShape hlen)
      (fun j => σ (B.tailIndex hlen j)) (fun j => (hσ (B.tailIndex hlen j)).2)
  have hprod := hbinary (B.headRank hlen) (B.tailRank hlen)
    (B.headRank_pos hlen) (B.tailRank_pos hlen)
    (σ (B.headIndex hlen)) C (hσ (B.headIndex hlen)).1
    (hσ (B.headIndex hlen)).2 hCi hCu
  have hcast := irreducible_rankCast F T (B.headRank_add_tailRank hlen)
    ((T.binaryNormalizedProductFunctor (B.headRank hlen) (B.tailRank hlen)).obj
      (σ (B.headIndex hlen), C)) hprod
  exact irreducible_of_iso
    (A := (T.normalizedProductInductionFunctor B).obj σ)
    (B := (Derivative.generalLinearRankCast T (B.headRank_add_tailRank hlen)).obj
      ((T.binaryNormalizedProductFunctor (B.headRank hlen) (B.tailRank hlen)).obj
        (σ (B.headIndex hlen), C)))
    (T.headTailBinaryProductIso B hlen σ) hcast

private theorem allProducts_irreducible
    (hbinary : BernsteinPositiveBinaryUnitaryProductIrreducibility.{uF, uV} F T) :
    letI := T.topology
    ∀ k n (B : BlockShape n), B.length = k →
      ∀ σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier),
        (∀ i, Representation.IsIrreducible (σ i).representation ∧
          IsUnitarizable (σ i).representation) →
        Representation.IsIrreducible
          ((T.normalizedProductInductionFunctor B).obj σ).representation := by
  let := T.topology
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro n B hB σ hσ
    cases k with
    | zero =>
      have hn : n = 0 := by
        have : IsEmpty (Fin B.length) := ⟨fun i => by have := i.isLt; omega⟩
        simpa only [Finset.univ_eq_empty, Finset.sum_empty] using B.sum_eq.symm
      subst n
      exact (bernstein_emptyProduct_irreducible_unitarizable F T B σ).1
    | succ k =>
      cases k with
      | zero => exact singleBlock_irreducible F T B hB σ (fun i => (hσ i).1)
      | succ k =>
        have hlen : B.length = k + 2 := hB
        apply headTail_irreducible F T hbinary B hlen σ hσ
        exact ih (k + 1) (by omega) (B.tailRank hlen) (B.tailShape hlen) rfl
          (fun j => σ (B.tailIndex hlen j)) (fun j => hσ (B.tailIndex hlen j))

/-- Bernstein's positive-rank binary assertion implies the exact published
all-block proposition, including one-block induction and the empty product. -/
theorem bernsteinUnitaryProductIrreducibility_of_binary
    (hbinary : BernsteinPositiveBinaryUnitaryProductIrreducibility.{uF, uV} F T) :
    BernsteinUnitaryProductIrreducibility.{uF, uV} F T := by
  let := T.topology
  intro n B σ hσ
  exact ⟨allProducts_irreducible F T hbinary B.length n B rfl σ hσ,
    bernstein_product_unitarizable F T n B σ (fun i => (hσ i).2)⟩

end Langlands.Classification
