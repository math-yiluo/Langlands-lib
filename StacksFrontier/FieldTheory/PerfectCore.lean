module

public import Mathlib.Algebra.Polynomial.Eval.Subring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The perfect core of a field

For a field `F` of exponential characteristic `p`, the *perfect core* is the subfield

$$\operatorname{perfectCore} F p = \bigcap_{n \ge 1} F^{p^n},$$

the largest perfect subfield of `F`. It is the field Epp's theorem on elimination of wild
ramification is stated in terms of: the hypothesis there is that every element of the perfect
core of the residue field upstairs is separable algebraic over the residue field downstairs.

This is not Mathlib's `perfectClosure F E`, which is the *relative* purely inseparable closure
of `F` in an extension `E`. The perfect core is absolute: it is a subfield of `F` itself, defined
as the infimum of the ranges of the iterated Frobenius endomorphisms, and it is the object
Kuhlmann calls the "largest perfect subfield".

## Main definitions

* `perfectCore F p`: the perfect core, as a `Subfield F`.

## Main results

* `mem_perfectCore_iff` and `mem_perfectCore_iff_forall_one_le`: membership is being a `p ^ n`-th
  power for every `n` (equivalently, for every `n ≥ 1`, which is the form Epp's hypothesis takes).
* `exists_pow_eq_and_not_pow_of_notMem_perfectCore`: an element outside the perfect core has a
  finite Frobenius depth — a last stage at which it is a `p`-power. This is Kuhlmann's `ν_x`, and
  it is what the tame/wild split of the degree-`p` step needs; taken against the perfect core it
  is free of any residue-field hypothesis.
* `perfectCore.perfectRing` and `perfectCore.perfectField`: the perfect core is perfect. This is
  what makes it the *largest* perfect subfield: `mem_perfectCore_of_perfectRing` shows every
  perfect subfield lands inside it.
* `perfectCore.isAlgClosed`: the perfect core of a *separably closed* field is algebraically
  closed. This is the reason the proof of Epp's theorem first enlarges the residue fields to
  their separable closures — it is what turns the perfect core into a field to which the
  algebraically-closed-residue-field case of the theorem applies.
* `perfectCore.isAlgClosed_of_exists_aeval_eq_zero` and
  `perfectCore.isAlgClosed_iff_exists_aeval_eq_zero`: separable closedness of `F` is *more* than
  that conclusion needs. All that is required — and it is equivalent to the conclusion — is that
  every separable polynomial with coefficients in the perfect core have a root somewhere in `F`.
* `minpoly_coeff_mem_perfectCore`: for a separable extension `E / F`, the minimal polynomial over
  `F` of an element of the perfect core of `E` has all its coefficients in the perfect core of
  `F`. This is the mechanism by which Epp's hypothesis transfers *upward* along a separable
  enlargement of the residue fields, via `perfectCore_mem_range_of_separable_square`.

## References

* [Epp, *Elimination of wild ramification*][epp1973]
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

variable (F : Type*) [Field F] (p : ℕ) [ExpChar F p]

/-- The perfect core `⋂_{n ≥ 1} F ^ (p ^ n)` of a field `F` of exponential characteristic `p`,
namely its largest perfect subfield, realised as the infimum of the ranges of the iterated
Frobenius endomorphisms.

In characteristic zero (`p = 1`) every Frobenius iterate is the identity and the perfect core is
all of `F`. -/
def perfectCore : Subfield F :=
  ⨅ n : ℕ, (iterateFrobenius F p n).fieldRange

variable {F p}

/-- An element lies in the perfect core exactly when it is a `p ^ n`-th power for every `n`. -/
theorem mem_perfectCore_iff {x : F} :
    x ∈ perfectCore F p ↔ ∀ n : ℕ, ∃ y : F, y ^ p ^ n = x := by
  simp only [perfectCore, Subfield.mem_iInf, RingHom.mem_fieldRange, iterateFrobenius_def]

/-- Epp's form of membership in the perfect core: being a `p ^ n`-th power for every `n ≥ 1`.

The restriction to `n ≥ 1` is harmless, since `n = 0` is witnessed by the element itself. -/
theorem mem_perfectCore_iff_forall_one_le {x : F} :
    x ∈ perfectCore F p ↔ ∀ n : ℕ, 1 ≤ n → ∃ y : F, y ^ p ^ n = x := by
  rw [mem_perfectCore_iff]
  refine ⟨fun h n _ => h n, fun h n => ?_⟩
  cases n with
  | zero => exact ⟨x, by simp⟩
  | succ n => exact h (n + 1) (Nat.succ_pos n)

/-- **An element outside the perfect core has a finite Frobenius depth.**

If `x` is not a `p ^ n`-th power for every `n`, then there is a *last* stage of the Frobenius
tower at which it is one: some `r` and `y` with `y ^ (p ^ r) = x` and `y` not itself a `p`-th
power. This `r` is Kuhlmann's `ν_x`.

The degree-`p` step of Epp's theorem splits the Laurent coefficients of an Artin–Schreier
equation into a tame and a wild part, and for each wild coefficient it needs exactly this: the
largest stage at which the coefficient is a `p`-power. Made against the perfect core itself, the
split needs no residue-field hypothesis: being outside the perfect core is already, by definition,
the failure of roots at some stage, and `Nat.find` turns that into the last surviving stage.

Compare `bddAbove_setOf_mem_frobeniusPowRange` and `frobeniusDepth` in
`StacksFrontier.RingTheory.DiscreteValuationRing.EppKuhlmannCompleteCase`, which work with a
`Subfield`-valued Frobenius tower and produce a boundedness statement and a numerical invariant;
the existential form here — a root `y` together with the witness that it admits no further `p`-th
root — is the shape the Artin–Schreier argument uses. -/
theorem exists_pow_eq_and_not_pow_of_notMem_perfectCore
    {F : Type*} [Field F] (p : ℕ) [ExpChar F p] {x : F} (hx : x ∉ perfectCore F p) :
    ∃ (r : ℕ) (y : F), y ^ (p ^ r) = x ∧ ¬∃ z : F, z ^ p = y := by
  classical
  have H : ∃ n : ℕ, ¬∃ y : F, y ^ p ^ n = x := by
    by_contra! H
    exact hx (mem_perfectCore_iff_forall_one_le.mpr fun n _ => H n)
  have hn : ¬∃ y : F, y ^ p ^ Nat.find H = x := Nat.find_spec H
  have hpos : 0 < Nat.find H := by
    rcases Nat.eq_zero_or_pos (Nat.find H) with h | h
    · exact absurd ⟨x, by rw [h]; simp⟩ hn
    · exact h
  obtain ⟨y, hy⟩ : ∃ y : F, y ^ p ^ (Nat.find H - 1) = x :=
    not_not.mp (Nat.find_min H (Nat.sub_lt hpos Nat.zero_lt_one))
  refine ⟨Nat.find H - 1, y, hy, ?_⟩
  rintro ⟨z, rfl⟩
  refine hn ⟨z, ?_⟩
  rw [← pow_mul, ← pow_succ'] at hy
  simpa only [Nat.sub_add_cancel hpos] using hy

/-- The perfect core is a perfect ring: every element of it has a `p`-th root inside it. -/
instance perfectCore.perfectRing : PerfectRing (perfectCore F p) p := by
  apply PerfectRing.ofSurjective
  intro x
  obtain ⟨y, hy⟩ := mem_perfectCore_iff.mp x.property 1
  have hy' : y ^ p = (x : F) := by simpa using hy
  have hmem : y ∈ perfectCore F p := by
    rw [mem_perfectCore_iff]
    intro n
    obtain ⟨z, hz⟩ := mem_perfectCore_iff.mp x.property (n + 1)
    refine ⟨z, ?_⟩
    apply frobenius_inj F p
    change (z ^ p ^ n) ^ p = y ^ p
    rw [← pow_mul, ← pow_succ, hz, hy']
  exact ⟨⟨y, hmem⟩, Subtype.ext hy'⟩

/-- The perfect core is a perfect field. -/
instance perfectCore.perfectField : PerfectField (perfectCore F p) :=
  PerfectRing.toPerfectField _ p

/-- The image of a perfect ring under any ring homomorphism lands in the perfect core.

Together with `perfectCore.perfectRing` this says the perfect core is the *largest* perfect
subfield: applied to the inclusion of a perfect subfield, it shows that subfield is contained in
the perfect core. -/
theorem mem_perfectCore_of_perfectRing {E : Type*} [Field E] [ExpChar E p] [PerfectRing E p]
    (f : E →+* F) (x : E) : f x ∈ perfectCore F p := by
  rw [mem_perfectCore_iff]
  intro n
  obtain ⟨y, hy⟩ := (bijective_iterateFrobenius E p n).surjective x
  exact ⟨f y, by rw [← map_pow]; exact congrArg f hy⟩

/-- Membership in the perfect core is invariant under a ring isomorphism. -/
theorem mem_perfectCore_ringEquiv_iff {E : Type*} [Field E] [ExpChar E p] (e : F ≃+* E) (x : F) :
    e x ∈ perfectCore E p ↔ x ∈ perfectCore F p := by
  simp only [mem_perfectCore_iff]
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · obtain ⟨y, hy⟩ := h n
    exact ⟨e.symm y, by apply e.injective; simpa only [map_pow, e.apply_symm_apply] using hy⟩
  · obtain ⟨y, hy⟩ := h n
    exact ⟨e y, by rw [← map_pow, hy]⟩

/-! ### Transport through a separable extension -/

section SeparablyClosed

/-- A separable element over `k` stays separable over any `K` in the tower `k → l → L` after
mapping it to `L`. -/
private theorem isSeparable_algebraMap_tower_top {k l L : Type*} (K : Type*) [Field k] [Field l]
    [Field K] [Field L] [Algebra k l] [Algebra l L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k l L] [IsScalarTower k K L] {y : l} (hy : IsSeparable k y) :
    IsSeparable K (algebraMap l L y) :=
  (hy.map (IsScalarTower.toAlgHom k l L) (algebraMap l L).injective).tower_top K

end SeparablyClosed

/-- The perfect-core separability condition passes along a square of fields whose upper
horizontal map is surjective, hence an isomorphism.

The application is to the residue fields of a completion, or of a `ULift`, where the residue field
does not change: Epp's hypothesis for the original extension gives it for the completed one. -/
theorem isSeparable_of_mem_perfectCore_of_surjective {k l K L : Type*} [Field k] [Field l]
    [Field K] [Field L] [Algebra k l] [Algebra l L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k l L] [IsScalarTower k K L] [ExpChar l p] [ExpChar L p]
    (hsurj : Function.Surjective (algebraMap l L))
    (hcore : ∀ x : l, x ∈ perfectCore l p → IsSeparable k x)
    {x : L} (hx : x ∈ perfectCore L p) : IsSeparable K x := by
  obtain ⟨y, rfl⟩ := hsurj x
  have hy : y ∈ perfectCore l p :=
    (mem_perfectCore_ringEquiv_iff
      (RingEquiv.ofBijective (algebraMap l L) ⟨(algebraMap l L).injective, hsurj⟩) y).mp hx
  exact isSeparable_algebraMap_tower_top K (hcore y hy)
