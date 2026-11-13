import Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement
import Langlands.GroupScheme.Rational.PositiveRootInduction

/-! # Dominant Weyl displacements as sums of simple roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

namespace DominantDisplacement

/-- Every positive relative root is a sum of simple relative roots. -/
theorem positive_mem_closure {χ : characterLattice T}
    (hχ : χ ∈ positiveRelativeRoots i ν) :
    χ ∈ AddSubmonoid.closure (simpleRelativeRoots i ν) :=
  positiveRelativeRoots_induction i ν
    (P := fun χ => χ ∈ AddSubmonoid.closure (simpleRelativeRoots i ν))
    (fun _ h => AddSubmonoid.subset_closure h)
    (fun _ _ _ _ h₁ h₂ => add_mem h₁ h₂) hχ

/-- A sum of simple roots either avoids `α` entirely, or still is a sum of simple roots
after removing one copy of `α`. -/
theorem mem_closure_diff_or_sub_mem (α : characterLattice T) {χ : characterLattice T}
    (hχ : χ ∈ AddSubmonoid.closure (simpleRelativeRoots i ν)) :
    χ ∈ AddSubmonoid.closure (simpleRelativeRoots i ν \ {α}) ∨
      χ - α ∈ AddSubmonoid.closure (simpleRelativeRoots i ν) := by
  induction hχ using AddSubmonoid.closure_induction with
  | mem β hβ =>
    by_cases h : β = α
    · right
      rw [h, sub_self]
      exact zero_mem _
    · left
      exact AddSubmonoid.subset_closure ⟨hβ, h⟩
  | zero =>
    left
    exact zero_mem _
  | add χ₁ χ₂ _ hχ₂ h₁ h₂ =>
    rcases h₁ with h₁ | h₁
    · rcases h₂ with h₂ | h₂
      · left
        exact add_mem h₁ h₂
      · right
        have e : χ₁ + χ₂ - α = χ₁ + (χ₂ - α) := by abel
        rw [e]
        exact add_mem (AddSubmonoid.closure_mono Set.sdiff_subset h₁) h₂
    · right
      have e : χ₁ + χ₂ - α = (χ₁ - α) + χ₂ := by abel
      rw [e]
      exact add_mem h₁ hχ₂

/-- A cocharacter vanishing on a set of characters vanishes on their sums. -/
theorem pairing_eq_zero_of_mem_closure {S : Set (characterLattice T)}
    {ζ : cocharacterLattice T} (hS : ∀ β ∈ S, latticePairing T β ζ = 0)
    {χ : characterLattice T} (hχ : χ ∈ AddSubmonoid.closure S) :
    latticePairing T χ ζ = 0 := by
  induction hχ using AddSubmonoid.closure_induction with
  | mem β hβ => exact hS β hβ
  | zero => simp
  | add χ₁ χ₂ _ _ h₁ h₂ => simp [h₁, h₂]

variable [Mono i.hom.hom.left]

open scoped Classical in
/-- The finite label set of the simple roots other than `α`. -/
def complementLabels [Fintype (SimpleRoot i ν)] (α : SimpleRoot i ν) :
    Finset (SimpleRoot i ν) :=
  Finset.univ.filter (fun a => a ≠ α)

omit [Mono i.hom.hom.left] in
theorem mem_complementLabels [Fintype (SimpleRoot i ν)] {α a : SimpleRoot i ν} :
    a ∈ complementLabels α ↔ a ≠ α := by
  classical
  simp [complementLabels]

omit [Mono i.hom.hom.left] in
theorem rootSet_complementLabels [Fintype (SimpleRoot i ν)] (α : SimpleRoot i ν) :
    rootSet i ν (complementLabels α) = simpleRelativeRoots i ν \ {α.1} := by
  ext β
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.2, ?_⟩
    intro h
    exact mem_complementLabels.mp ha (Subtype.ext h)
  · rintro ⟨hβ, hne⟩
    refine ⟨⟨β, hβ⟩, mem_complementLabels.mpr ?_, rfl⟩
    intro h
    exact hne (congrArg Subtype.val h)

variable {M : CoxeterMatrix (SimpleRoot i ν)} {cs : CoxeterSystem M (relativeWeylGroup i)}

/-- In a Coxeter realization, the standard relative Weyl subgroup of `Δ \ {α}` is generated
by the simple reflections other than that of `α`. -/
theorem standardRelativeWeylGroup_complement_eq [Fintype (SimpleRoot i ν)]
    (hcs : IsRelativeWeylCoxeterRealization i ν cs) (α : SimpleRoot i ν) :
    standardRelativeWeylGroup i ν (simpleRelativeRoots i ν \ {α.1}) =
      standardSubgroup cs (complementLabels α) := by
  rw [← rootSet_complementLabels α, hcs.2.2.2.2]

omit [Mono i.hom.hom.left] in
/-- A property preserved by the simple reflections other than `α` holds for every element of
the standard relative Weyl subgroup of `Δ \ {α}`, provided it is stable under products and
inverses. -/
theorem standardSubgroup_complement_induction [Fintype (SimpleRoot i ν)]
    (α : SimpleRoot i ν) {P : relativeWeylGroup i → Prop}
    (hsimple : ∀ a : SimpleRoot i ν, a ≠ α → P (cs.simple a))
    (hone : P 1) (hmul : ∀ v w, P v → P w → P (v * w)) (hinv : ∀ v, P v → P v⁻¹)
    {w : relativeWeylGroup i} (hw : w ∈ standardSubgroup cs (complementLabels α)) : P w := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact hsimple a (mem_complementLabels.mp ha)
  | one => exact hone
  | mul v w _ _ hv hw => exact hmul v w hv hw
  | inv v _ hv => exact hinv v hv

/-- The main combinatorial input to Springer's Proposition 2.6. Suppose that `ψ` is fixed by
the simple reflections other than `α`, and that `ψ - s_α ψ` is a positive multiple of `α`.
Then `ψ - w ψ` is a sum of simple roots for every relative Weyl element `w`, and if `w` lies
outside the standard relative Weyl subgroup of `Δ \ {α}`, then `ψ - w ψ - α` is still a sum
of simple roots. -/
theorem displacement_mem_closure [Fintype (SimpleRoot i ν)]
    (hcs : IsRelativeWeylCoxeterRealization i ν cs) (α : SimpleRoot i ν)
    {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν (simpleRelativeRoots i ν \ {α.1}) ζ)
    (ψ : characterLattice T)
    (hfix : ∀ a : SimpleRoot i ν, a ≠ α → schemeWeylCharacterAction i (cs.simple a) ψ = ψ)
    (m : ℕ) (hm : 0 < m)
    (hα : ψ - schemeWeylCharacterAction i (cs.simple α) ψ = m • α.1)
    (w : relativeWeylGroup i) :
    ψ - schemeWeylCharacterAction i w ψ ∈ AddSubmonoid.closure (simpleRelativeRoots i ν) ∧
      (w ∉ standardRelativeWeylGroup i ν (simpleRelativeRoots i ν \ {α.1}) →
        ψ - schemeWeylCharacterAction i w ψ - α.1 ∈
          AddSubmonoid.closure (simpleRelativeRoots i ν)) := by
  set Δ := simpleRelativeRoots i ν
  set act := schemeWeylCharacterAction i
  rw [standardRelativeWeylGroup_complement_eq hcs α]
  set WJ := standardSubgroup cs (complementLabels α)
  -- `ψ` is fixed by the standard subgroup.
  have hψfix : ∀ v ∈ WJ, act v ψ = ψ := by
    intro v hv
    refine standardSubgroup_complement_induction (cs := cs) α
      (P := fun v => act v ψ = ψ) hfix (by simp) ?_ ?_ hv
    · intro v w hv hw
      simp only [map_mul, LinearEquiv.mul_apply, hw, hv]
    · intro v hv
      have h := congrArg (act v⁻¹) hv
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h
      simpa using h.symm
  -- the pairing with `ζ` is invariant under the standard subgroup.
  have hφfix : ∀ v ∈ WJ, ∀ χ, latticePairing T (act v χ) ζ = latticePairing T χ ζ := by
    intro v hv
    refine standardSubgroup_complement_induction (cs := cs) α
      (P := fun v => ∀ χ, latticePairing T (act v χ) ζ = latticePairing T χ ζ)
      ?_ (by simp) ?_ ?_ hv
    · intro a ha χ
      obtain ⟨f, -, hf⟩ := hcs.1 a
      rw [hf χ, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
      have hzero : latticePairing T a.1 ζ = 0 := by
        refine hζ.2.1 a.1 ⟨a.2, ?_⟩
        intro h
        exact ha (Subtype.ext h)
      rw [hzero, smul_zero, sub_zero]
    · intro v w hv hw χ
      simp only [map_mul, LinearEquiv.mul_apply, hv, hw]
    · intro v hv χ
      have h := hv (act v⁻¹ χ)
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
      simpa using h.symm
  have hαζ : 0 < latticePairing T α.1 ζ := hζ.2.2 α.1 α.2 (fun h => h.2 rfl)
  suffices h : ∀ n (v : relativeWeylGroup i), cs.length v = n →
      ψ - act v ψ ∈ AddSubmonoid.closure Δ ∧
        (v ∉ WJ → ψ - act v ψ - α.1 ∈ AddSubmonoid.closure Δ) from h _ w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v hv
    by_cases hv1 : v = 1
    · subst v
      refine ⟨by simp, fun h => (h WJ.one_mem).elim⟩
    obtain ⟨a, ha⟩ := cs.exists_rightDescent_of_ne_one hv1
    change cs.length (v * cs.simple a) < cs.length v at ha
    set v' := v * cs.simple a with hv'def
    have hv'len : cs.length v' < n := by
      rw [← hv]
      exact ha
    have hv's : v' * cs.simple a = v := cs.simple_mul_simple_cancel_right a
    have hstep : cs.length v' < cs.length (v' * cs.simple a) := by
      rw [hv's]
      exact ha
    have hpos : act v' a.1 ∈ positiveRelativeRoots i ν := (hcs.2.2.1 v' a).mp hstep
    have hposc : act v' a.1 ∈ AddSubmonoid.closure Δ := positive_mem_closure hpos
    obtain ⟨ih₁, ih₂⟩ := ih _ hv'len v' rfl
    have hdecomp : ψ - act v ψ = (ψ - act v' ψ) + act v' (ψ - act (cs.simple a) ψ) := by
      rw [← hv's, map_mul, LinearEquiv.mul_apply, map_sub]
      abel
    by_cases haα : a = α
    · subst haα
      rw [hα, map_nsmul] at hdecomp
      have hmem : ψ - act v ψ ∈ AddSubmonoid.closure Δ := by
        rw [hdecomp]
        exact add_mem ih₁ (AddSubmonoid.nsmul_mem _ hposc m)
      refine ⟨hmem, fun hvJ => ?_⟩
      by_cases hv'J : v' ∈ WJ
      · -- `ψ - v' ψ = 0`, and `v' α - α` is a sum of simple roots
        have h0 : ψ - act v' ψ = 0 := by rw [hψfix v' hv'J, sub_self]
        rw [h0, zero_add] at hdecomp
        have hφ : latticePairing T (act v' a.1) ζ = latticePairing T a.1 ζ :=
          hφfix v' hv'J a.1
        rcases mem_closure_diff_or_sub_mem a.1 hposc with hJ | hsub
        · exfalso
          have hz := pairing_eq_zero_of_mem_closure
            (S := Δ \ {a.1}) (fun β hβ => hζ.2.1 β hβ) hJ
          rw [hφ] at hz
          exact hαζ.ne' hz
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          have e : ψ - act v ψ - a.1 =
              (m' • act v' a.1) + (act v' a.1 - a.1) := by
            rw [hdecomp, succ_nsmul]
            abel
          rw [e]
          exact add_mem (AddSubmonoid.nsmul_mem _ hposc m') hsub
      · have e : ψ - act v ψ - a.1 =
            (ψ - act v' ψ - a.1) + m • act v' a.1 := by
          rw [hdecomp]
          abel
        rw [e]
        exact add_mem (ih₂ hv'J) (AddSubmonoid.nsmul_mem _ hposc m)
    · rw [hfix a haα, sub_self, map_zero, add_zero] at hdecomp
      refine ⟨hdecomp ▸ ih₁, fun hvJ => ?_⟩
      rw [hdecomp]
      refine ih₂ (fun hv'J => hvJ ?_)
      rw [← hv's]
      exact WJ.mul_mem hv'J (simple_mem_standardSubgroup cs (mem_complementLabels.mpr haα))

end DominantDisplacement

end Langlands.GroupScheme
