import Langlands.Representation.Filtration.SmoothDualEvaluation
import Langlands.Representation.Classification.SupercuspidalContragredientAux

/-! # Actual smooth-dual quotients extracted from invariant pairings -/

noncomputable section

namespace Langlands.InvariantBilinear

universe uK uG uV uW uX

section SmoothMap

variable {k : Type uK} [Field k]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable {ρ : Representation k G V} {σ : Representation k G W}

/-- An invariant bilinear form gives an actual map from its smooth right input
to the full smooth dual of its left input. -/
def rightSmoothDualMap (hσ : IsSmooth σ) (B : forms ρ σ (fun _ => 1)) :
    σ.IntertwiningMap (smoothContragredient ρ) :=
  smoothLift hσ
    { toLinearMap := B.val.flip
      isIntertwining' := by
        intro g
        ext w v
        change B.val v (σ g w) = B.val (ρ g⁻¹ v) w
        simpa only [ρ.self_inv_apply, one_mul] using B.property g (ρ g⁻¹ v) w }

@[simp]
theorem rightSmoothDualMap_apply (hσ : IsSmooth σ)
    (B : forms ρ σ (fun _ => 1)) (w : W) (v : V) :
    (rightSmoothDualMap hσ B w).val v = B.val v w := rfl

theorem rightSmoothDualMap_ne_zero (hσ : IsSmooth σ)
    (B : forms ρ σ (fun _ => 1)) (hB : B ≠ 0) :
    rightSmoothDualMap hσ B ≠ 0 := by
  intro h
  apply hB
  apply Subtype.ext
  ext v w
  exact congrArg
    (fun f : σ.IntertwiningMap (smoothContragredient ρ) => (f w).val v) h

/-- A nonzero form maps onto an irreducible actual smooth dual. -/
theorem rightSmoothDualMap_surjective (hσ : IsSmooth σ)
    (B : forms ρ σ (fun _ => 1)) (hB : B ≠ 0)
    (hdual : Representation.IsIrreducible (k := k) (G := G) (V := SmoothDual ρ)
      (smoothContragredient ρ)) :
    Function.Surjective (rightSmoothDualMap hσ B) := by
  let := hdual
  have h :
      Function.Surjective (rightSmoothDualMap hσ B) ∨ rightSmoothDualMap hσ B = 0 :=
    Representation.IsIrreducible.surjective_or_eq_zero
      (k := k) (G := G) (V := SmoothDual ρ) (W := W)
      (ρ := smoothContragredient ρ) (σ := σ) (rightSmoothDualMap hσ B)
  exact h.resolve_right (rightSmoothDualMap_ne_zero hσ B hB)

end SmoothMap

section Complex

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
variable {τ : Representation ℂ G X}

private theorem dualIrreducible
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (hirr : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible (smoothContragredient ρ) :=
  (isIrreducible_smoothContragredient_iff_of_bidual
    (fun _ _ _ π hπ => smoothBidual_injective_of_compact_cofinal hcofinal π hπ)
    ρ hρ.1 ⟨smoothBidual_injective_of_compact_cofinal hcofinal ρ hρ.1,
      smoothBidual_surjective_of_compact_cofinal hcofinal ρ hρ⟩).mpr hirr

/-- The actual surjective map, retaining its evaluation formula, for any
nonzero invariant form with irreducible admissible left input. -/
def smoothDualQuotientOfNonzeroForm
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (hirr : Representation.IsIrreducible ρ)
    (hσ : IsSmooth σ) (B : forms ρ σ (fun _ => 1)) (hB : B ≠ 0) :
    {q : σ.IntertwiningMap (smoothContragredient ρ) // Function.Surjective q} :=
  ⟨rightSmoothDualMap hσ B,
    rightSmoothDualMap_surjective hσ B hB (dualIrreducible hcofinal hρ hirr)⟩

@[simp]
theorem smoothDualQuotientOfNonzeroForm_apply
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (hirr : Representation.IsIrreducible ρ)
    (hσ : IsSmooth σ) (B : forms ρ σ (fun _ => 1)) (hB : B ≠ 0)
    (w : W) (v : V) :
    ((smoothDualQuotientOfNonzeroForm hcofinal hρ hirr hσ B hB).val w).val v =
      B.val v w := rfl

/-- Restrict a left-separating invariant form to a supplied irreducible
admissible subrepresentation, and obtain an actual quotient onto its smooth dual. -/
def smoothDualQuotientOfLeftEmbedding
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hτ : IsAdmissible τ) (hirr : Representation.IsIrreducible τ)
    (hσ : IsSmooth σ) (i : τ.IntertwiningMap ρ) (hi : Function.Injective i)
    (B : forms ρ σ (fun _ => 1)) (hB : B.val.SeparatingLeft) :
    {q : σ.IntertwiningMap (smoothContragredient τ) // Function.Surjective q} := by
  letI := hirr
  letI : Nontrivial X :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) τ.asModule
  exact smoothDualQuotientOfNonzeroForm hcofinal hτ hirr hσ
    (comapLeft σ (fun _ => 1) i B)
    (comapLeft_ne_zero_of_separatingLeft σ (fun _ => 1) i hi B hB)

@[simp]
theorem smoothDualQuotientOfLeftEmbedding_apply
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hτ : IsAdmissible τ) (hirr : Representation.IsIrreducible τ)
    (hσ : IsSmooth σ) (i : τ.IntertwiningMap ρ) (hi : Function.Injective i)
    (B : forms ρ σ (fun _ => 1)) (hB : B.val.SeparatingLeft)
    (w : W) (x : X) :
    ((smoothDualQuotientOfLeftEmbedding hcofinal hτ hirr hσ i hi B hB).val w).val x =
      B.val (i x) w := rfl

end Complex

end Langlands.InvariantBilinear
