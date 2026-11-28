import Langlands.HarmonicAnalysis.UnitConjugation.LatticeLevelFourier
import Mathlib.GroupTheory.GroupAction.Basic

/-! # Grouping the finite lattice indicator expansion into conjugation orbits -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory Set

universe u

variable {A : Type u} [Ring A] [TopologicalSpace A]
  {e : A → A → ℂ} (he : IsSelfDualBicharacter e) (L N : AddSubgroup A) (H : Subgroup Aˣ)

/-- When a group of units preserves the two lattices and the bicharacter, the
finite expansion of the level indicator splits into its conjugation orbit sums. -/
def LatticeLevelOrbitExpansionStatement [IsTopologicalRing A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [CompactOpenExhaustion A] [MeasurableSpace A] [BorelSpace A] : Prop :=
  IsCompact (L : Set A) → IsOpen (N : Set A) → IsCompact (N : Set A) →
  (∀ k ∈ H, ∀ x ∈ L, conjugationHomeomorph k x ∈ L) →
  (∀ k ∈ H, ∀ x ∈ N, conjugationHomeomorph k x ∈ N) →
  (∀ k ∈ H, ∀ x z, e (conjugationHomeomorph k x) (conjugationHomeomorph k z) = e x z) →
  ∃ (I : Type u) (S : Finset I) (z : I → A) (P : I → Finset (AddChar L ℂ)) (n : ℕ),
    n ≠ 0 ∧ (∀ i ∈ S, z i ∈ he.annihilator (N : Set A)) ∧
    (∀ i ∈ S, (P i : Set (AddChar L ℂ)) = latticeCharacterOrbit he L H (z i)) ∧
    ∀ x : L, (∑ i ∈ S, ∑ χ ∈ P i, χ x) = (N : Set A).indicator (fun _ => (n : ℂ)) x.val

variable [IsTopologicalRing A] [LocallyCompactSpace A] [SecondCountableTopology A]
  [CompactOpenExhaustion A] [MeasurableSpace A] [BorelSpace A]

theorem latticeLevelOrbitExpansion (μ : Measure A) [μ.IsAddHaarMeasure] :
    LatticeLevelOrbitExpansionStatement he L N H := by
  classical
  intro hLc hNo hNc hL hN hPair
  obtain ⟨S, hS, hSpos, hFormula⟩ := latticeLevelFourier he L N μ hLc hNo hNc
  let B := latticeLevelCharacters he L N
  let : Fintype B := (latticeLevelCharacters_finite he L N hLc hNo hNc).fintype
  let a (k : H) : L →+ L :=
    { toFun := fun x => ⟨conjugationHomeomorph k.val x.val, hL k.val k.property x.val x.property⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp [mul_add, add_mul]) }
  have hComp (k : H) (x z : A) :
      e (conjugationHomeomorph (k⁻¹ : H).val x) z = e x (conjugationHomeomorph k.val z) := by
    have h := hPair k.val k.property (conjugationHomeomorph (k⁻¹ : H).val x) z
    rw [← conjugationHomeomorph_mul, show k.val * (k⁻¹ : H).val = 1 from mul_inv_cancel k.val] at h
    simpa only [conjugationHomeomorph_one] using h.symm
  have hChar (k : H) (z : A) :
      (latticeAddChar he L z).compAddMonoidHom (a k⁻¹) =
        latticeAddChar he L (conjugationHomeomorph k.val z) :=
    AddChar.ext _ _ fun x => hComp k x.val z
  have hStable (k : H) (z : A) (hz : z ∈ he.annihilator (N : Set A)) :
      conjugationHomeomorph k.val z ∈ he.annihilator (N : Set A) := by
    intro x hx
    rw [← hComp]
    exact hz _ (hN _ (k⁻¹ : H).property _ hx)
  let shift (k : H) (χ : B) : B :=
    ⟨χ.val.compAddMonoidHom (a k⁻¹), by
      obtain ⟨z, hz, hχ⟩ := (mem_latticeLevelCharacters_iff he L N χ.val).mp χ.property
      exact ⟨conjugationHomeomorph k.val z, hStable k z hz, (hChar k z).symm.trans
        (congrArg (fun ψ : AddChar L ℂ => ψ.compAddMonoidHom (a k⁻¹)) hχ)⟩⟩
  let : MulAction H B :=
    { smul := shift
      one_smul := fun χ => Subtype.ext (AddChar.ext _ _ fun x => by
        change χ.val (a (1 : H)⁻¹ x) = χ.val x
        congr 1
        apply Subtype.ext
        change conjugationHomeomorph ((1 : H)⁻¹ : H).val x.val = x.val
        simp)
      mul_smul := fun k l χ => Subtype.ext (AddChar.ext _ _ fun x => by
        change χ.val (a (k * l)⁻¹ x) = χ.val (a l⁻¹ (a k⁻¹ x))
        congr 1
        apply Subtype.ext
        change conjugationHomeomorph ((k * l)⁻¹ : H).val x.val =
          conjugationHomeomorph (l⁻¹ : H).val (conjugationHomeomorph (k⁻¹ : H).val x.val)
        rw [mul_inv_rev, Subgroup.coe_mul, conjugationHomeomorph_mul]) }
  let I := MulAction.orbitRel.Quotient H B
  let : Fintype I := Fintype.ofFinite I
  choose z hz hχ using fun i : I =>
    (mem_latticeLevelCharacters_iff he L N (Quotient.out i).val).mp (Quotient.out i).property
  let O (i : I) := MulAction.orbit H (Quotient.out i)
  let : ∀ i : I, Fintype (O i) := fun i => Fintype.ofFinite (O i)
  let emb : B ↪ AddChar L ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  let P (i : I) := (O i).toFinset.map emb
  refine ⟨I, Finset.univ, z, P, S.card, hSpos.card_ne_zero, fun i _ => hz i, ?_, ?_⟩
  · intro i _
    ext χ
    change χ ∈ ((O i).toFinset.map emb) ↔ χ ∈ latticeCharacterOrbit he L H (z i)
    rw [Finset.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨k, hk⟩ := Set.mem_toFinset.mp hb
      refine ⟨k, ?_⟩
      change _ = b.val
      rw [← hk]
      change _ = (Quotient.out i).val.compAddMonoidHom (a k⁻¹)
      rw [← hχ i, hChar]
    · rintro ⟨k, rfl⟩
      refine ⟨k • Quotient.out i, Set.mem_toFinset.mpr ⟨k, rfl⟩, ?_⟩
      change (Quotient.out i).val.compAddMonoidHom (a k⁻¹) = _
      rw [← hχ i, hChar]
  intro x
  rw [← hFormula x]
  have hP (i : I) : (∑ χ ∈ P i, χ x) = ∑ χ : O i, χ.val.val x := by
    rw [show P i = (O i).toFinset.map emb from rfl, Finset.sum_map]
    exact Finset.sum_subtype _ (fun _ => Set.mem_toFinset) _
  simp_rw [hP]
  rw [← Fintype.sum_sigma (fun p : Σ i : I, O i => p.2.val.val x)]
  have hS' (χ : AddChar L ℂ) : χ ∈ S ↔ χ ∈ B :=
    Set.ext_iff.mp hS χ
  rw [Finset.sum_subtype S hS']
  apply Fintype.sum_equiv (MulAction.selfEquivSigmaOrbits H B).symm
  intro χ
  rfl

end Langlands.HarmonicAnalysis.UnitConjugation
