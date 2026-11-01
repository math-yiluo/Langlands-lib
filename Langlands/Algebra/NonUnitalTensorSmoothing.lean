import Langlands.Algebra.NonUnitalModuleTensor
import Langlands.Algebra.NonUnitalModuleDualFixedPartMaps

/-!
# Tensor smoothing: the inclusion and its balanced reverse

The two additive comparison maps in the tensor argument of Renard (9 July 2026),
I.4.3, printed p. 25: the map `N_A ⊗_A M → N ⊗_A M` induced by the inclusion of the
nondegenerate part of an arbitrary right module, and the reverse map induced by
`(n, m) ↦ (n · e) ⊗ m` for an idempotent `e` fixing `m`. Only the original additive
groups, ring multiplication, actions and finite local units are used.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalTensorSmoothing

open MulOpposite
open NonUnitalModuleTensor
open NonUnitalModuleDualFixedPartMaps (oppositeIdempotent oppositeIdempotent_val)

universe uA uN uM

section Construction

variable {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
  (N : Type uN) [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
  (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]

/-! ## The inclusion -/

/-- The actual inclusion map `N_A ⊗_A M → N ⊗_A M`, induced through the published tensor
map by the published nondegenerate-part subtype and the identity of `M`. -/
def inclusion : Tensor A (nondegeneratePart hA.op N) M →+ Tensor A N M :=
  map A (nondegeneratePart hA.op N).subtype (NonUnitalModuleHom.id A M)

/-- The entire additive inclusion is exactly the published tensor map. -/
theorem inclusion_eq_map :
    inclusion hA N M =
      map A (nondegeneratePart hA.op N).subtype (NonUnitalModuleHom.id A M) := rfl

@[simp] theorem inclusion_tmul (n : nondegeneratePart hA.op N) (m : M) :
    inclusion hA N M (tmul A (nondegeneratePart hA.op N) M n m) = tmul A N M (n : N) m := rfl

theorem inclusion_pure_function :
    (fun (n : nondegeneratePart hA.op N) (m : M) =>
      inclusion hA N M (tmul A (nondegeneratePart hA.op N) M n m)) =
      fun (n : nondegeneratePart hA.op N) (m : M) => tmul A N M (n : N) m := rfl

/-! ## The smoothed element `n · e` of the nondegenerate part -/

variable {N} in
/-- The right action of an idempotent fixes its own values: `(n · e) · e = n · e`. -/
theorem op_smul_op_smul_self (e : Idempotent A) (n : N) :
    op (e : A) • (op (e : A) • n) = op (e : A) • n := by
  rw [← right_mul_smul, e.property.eq]

variable {N} in
/-- `n · e` lies in the nondegenerate part, being fixed by the idempotent `op e`. -/
theorem smul_mem_nondegeneratePart (n : N) (e : Idempotent A) :
    op (e : A) • n ∈ nondegeneratePart hA.op N :=
  ⟨oppositeIdempotent e, op_smul_op_smul_self e n⟩

variable {N} in
/-- The actual element `n · e` of `N_A`; its original value is `op e • n`. -/
def smoothing (n : N) (e : Idempotent A) : nondegeneratePart hA.op N :=
  ⟨op (e : A) • n, smul_mem_nondegeneratePart hA n e⟩

@[simp] theorem smoothing_val (n : N) (e : Idempotent A) :
    (smoothing hA n e : N) = op (e : A) • n := rfl

/-- The inherited action of `op e` fixes the element `n · e` of `N_A`. -/
theorem oppositeIdempotent_smul_smoothing (n : N) (e : Idempotent A) :
    (oppositeIdempotent e : Aᵐᵒᵖ) • smoothing hA n e = smoothing hA n e :=
  Subtype.ext (op_smul_op_smul_self e n)

theorem smoothing_zero (e : Idempotent A) : smoothing hA (0 : N) e = 0 :=
  Subtype.ext (smul_zero _)

theorem smoothing_add (n n' : N) (e : Idempotent A) :
    smoothing hA (n + n') e = smoothing hA n e + smoothing hA n' e :=
  Subtype.ext (smul_add _ n n')

/-- For `e ≤ h`, the inherited action of `op e` sends `n · h` to `n · e`, since `h e = e`. -/
theorem op_smul_smoothing_of_le (n : N) {e h : Idempotent A} (heh : e ≤ h) :
    op (e : A) • smoothing hA n h = smoothing hA n e := by
  apply Subtype.ext
  change op (e : A) • (op (h : A) • n) = op (e : A) • n
  rw [← right_mul_smul, ((Idempotent.le_iff_mul e h).mp heh).1]

/-- In the actual quotient `N_A ⊗_A M`, an idempotent `e` fixing `m` and any larger
idempotent `h` give the same value: `(n · h) ⊗ m = (n · e) ⊗ m`. -/
theorem tmul_smoothing_eq_of_le (n : N) {m : M} {e h : Idempotent A} (heh : e ≤ h)
    (he : (e : A) • m = m) :
    tmul A (nondegeneratePart hA.op N) M (smoothing hA n h) m =
      tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m := by
  calc
    tmul A (nondegeneratePart hA.op N) M (smoothing hA n h) m =
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n h) ((e : A) • m) := by rw [he]
    _ = tmul A (nondegeneratePart hA.op N) M (op (e : A) • smoothing hA n h) m :=
        (tmul_balanced A _ M _ _ _).symm
    _ = tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m := by
        rw [op_smul_smoothing_of_le hA N n heh]

/-- Choice independence: any two idempotents fixing `m` give the same value
`(n · e) ⊗ m = (n · f) ⊗ m` in the actual quotient `N_A ⊗_A M`. -/
theorem tmul_smoothing_eq (n : N) {m : M} {e f : Idempotent A}
    (he : (e : A) • m = m) (hf : (f : A) • m = m) :
    tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m =
      tmul A (nondegeneratePart hA.op N) M (smoothing hA n f) m := by
  classical
  obtain ⟨h, hh⟩ := hA.finite_upper_bound {e, f}
  rw [← tmul_smoothing_eq_of_le hA N M n (hh e (by simp)) he,
    tmul_smoothing_eq_of_le hA N M n (hh f (by simp)) hf]

/-! ## The balanced biadditive map `φ` -/

variable {M} (hM : IsNondegenerate A M)

/-- The idempotent fixing `m` chosen from the specified nondegeneracy witness `hM`. -/
noncomputable def chosenFixer (m : M) : Idempotent A := (hM m).choose

theorem chosenFixer_smul (m : M) : (chosenFixer hM m : A) • m = m := (hM m).choose_spec

/-- The function `φ(n, m) = (n · e) ⊗ m`, with `e` the fixer of `m` chosen from `hM`. -/
noncomputable def reverseFun (n : N) (m : M) : Tensor A (nondegeneratePart hA.op N) M :=
  tmul A (nondegeneratePart hA.op N) M (smoothing hA n (chosenFixer hM m)) m

/-- The exact value of `φ(n, m)` is `(n · e) ⊗ m` for every idempotent `e` fixing `m`. -/
theorem reverseFun_eq (n : N) (m : M) (e : Idempotent A) (he : (e : A) • m = m) :
    reverseFun hA N hM n m = tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  tmul_smoothing_eq hA N M n (chosenFixer_smul hM m) he

theorem reverseFun_zero_left (m : M) : reverseFun hA N hM 0 m = 0 := by
  rw [reverseFun, smoothing_zero, zero_tmul]

theorem reverseFun_add_left (n n' : N) (m : M) :
    reverseFun hA N hM (n + n') m = reverseFun hA N hM n m + reverseFun hA N hM n' m := by
  rw [reverseFun, reverseFun, reverseFun, smoothing_add, add_tmul]

theorem reverseFun_zero_right (n : N) : reverseFun hA N hM n 0 = 0 := by
  rw [reverseFun, tmul_zero]

theorem reverseFun_add_right (n : N) (m m' : M) :
    reverseFun hA N hM n (m + m') = reverseFun hA N hM n m + reverseFun hA N hM n m' := by
  classical
  obtain ⟨h, hh⟩ := hA.finite_upper_bound {chosenFixer hM m, chosenFixer hM m'}
  have hm : (h : A) • m = m :=
    Idempotent.smul_eq_of_le (hh _ (by simp)) (chosenFixer_smul hM m)
  have hm' : (h : A) • m' = m' :=
    Idempotent.smul_eq_of_le (hh _ (by simp)) (chosenFixer_smul hM m')
  have hmm' : (h : A) • (m + m') = m + m' := by rw [smul_add, hm, hm']
  rw [reverseFun_eq hA N hM n m h hm, reverseFun_eq hA N hM n m' h hm',
    reverseFun_eq hA N hM n (m + m') h hmm', tmul_add]

/-- The bundled biadditive map `φ : N → M → N_A ⊗_A M`. -/
noncomputable def reverseBiadditive : N →+ M →+ Tensor A (nondegeneratePart hA.op N) M where
  toFun n :=
    { toFun := reverseFun hA N hM n
      map_zero' := reverseFun_zero_right hA N hM n
      map_add' := reverseFun_add_right hA N hM n }
  map_zero' := AddMonoidHom.ext (reverseFun_zero_left hA N hM)
  map_add' n n' := AddMonoidHom.ext (reverseFun_add_left hA N hM n n')

@[simp] theorem reverseBiadditive_apply (n : N) (m : M) :
    reverseBiadditive hA N hM n m = reverseFun hA N hM n m := rfl

theorem reverseBiadditive_eq (n : N) (m : M) (e : Idempotent A) (he : (e : A) • m = m) :
    reverseBiadditive hA N hM n m =
      tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  reverseFun_eq hA N hM n m e he

include hA hM in
/-- An idempotent fixing `m` whose corner contains `a`. -/
theorem exists_fixer_mem_corner (a : A) (m : M) :
    ∃ h : Idempotent A, (h : A) • m = m ∧ (h : A) * a = a ∧ a * (h : A) = a := by
  classical
  obtain ⟨f, hf⟩ := hA.exists_mem_corner a
  obtain ⟨h, hh⟩ := hA.finite_upper_bound {chosenFixer hM m, f}
  refine ⟨h, Idempotent.smul_eq_of_le (hh _ (by simp)) (chosenFixer_smul hM m), ?_⟩
  exact (Idempotent.mem_corner_iff h a).mp (hh f (by simp) hf)

/-- `φ` is balanced for the original actions: `φ(n · a, m) = φ(n, a · m)`. -/
theorem reverseBiadditive_balanced : IsBalanced A (reverseBiadditive hA N hM) := by
  intro a n m
  obtain ⟨h, hm, hha, hah⟩ := exists_fixer_mem_corner hA hM a m
  have ham : (h : A) • (a • m) = a • m := by rw [← mul_smul, hha]
  rw [reverseBiadditive_eq hA N hM (op a • n) m h hm,
    reverseBiadditive_eq hA N hM n (a • m) h ham, ← tmul_balanced]
  congr 1
  apply Subtype.ext
  change op (h : A) • (op a • n) = op a • (op (h : A) • n)
  rw [← right_mul_smul, ← right_mul_smul, hah, hha]

/-! ## The reverse map `Φ` -/

/-- The actual reverse map `Φ : N ⊗_A M → N_A ⊗_A M`, the published lift of `φ`. -/
noncomputable def reverse : Tensor A N M →+ Tensor A (nondegeneratePart hA.op N) M :=
  lift A (reverseBiadditive hA N hM) (reverseBiadditive_balanced hA N hM)

/-- The entire reverse map is exactly the published lift of `φ` and its balancing proof. -/
theorem reverse_eq_lift :
    reverse hA N hM = lift A (reverseBiadditive hA N hM) (reverseBiadditive_balanced hA N hM) :=
  rfl

/-- Factorization through the published quotient map, as complete additive maps. -/
theorem reverse_comp_projection :
    (reverse hA N hM).comp (projection A N M) = integerLift (reverseBiadditive hA N hM) := rfl

theorem reverse_tmul_eq_reverseBiadditive (n : N) (m : M) :
    reverse hA N hM (tmul A N M n m) = reverseBiadditive hA N hM n m := rfl

theorem reverse_pure_function :
    (fun (n : N) (m : M) => reverse hA N hM (tmul A N M n m)) =
      fun n m => reverseBiadditive hA N hM n m := rfl

/-- Uniqueness of `Φ` among additive maps with the values of `φ` on pure tensors. -/
theorem reverse_unique (f : Tensor A N M →+ Tensor A (nondegeneratePart hA.op N) M)
    (hf : ∀ n m, f (tmul A N M n m) = reverseBiadditive hA N hM n m) :
    f = reverse hA N hM :=
  lift_unique A _ _ f hf

/-- The exact pure-tensor formula: `Φ(n ⊗ m) = (n · e) ⊗ m` for every `e` fixing `m`. -/
theorem reverse_tmul (n : N) (m : M) (e : Idempotent A) (he : (e : A) • m = m) :
    reverse hA N hM (tmul A N M n m) =
      tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  reverseFun_eq hA N hM n m e he

include hM in
/-- Through the public formula, the value of `Φ` does not depend on the fixing idempotent. -/
theorem reverse_tmul_independent (n : N) (m : M) (e f : Idempotent A)
    (he : (e : A) • m = m) (hf : (f : A) • m = m) :
    tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m =
      tmul A (nondegeneratePart hA.op N) M (smoothing hA n f) m :=
  (reverse_tmul hA N hM n m e he).symm.trans (reverse_tmul hA N hM n m f hf)

end Construction

/-! ## Degenerate right modules and the scalar specialization -/

section ZeroAction

variable {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN) [AddCommGroup N]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M] (hM : IsNondegenerate A M)

/-- An arbitrary group, possibly nonzero, with the original zero right action is admitted;
every smoothed element `n · e` is then `0`. -/
example (n : N) (e : Idempotent A) :
    letI := NonUnitalModule.zero (A := Aᵐᵒᵖ) (M := N)
    smoothing hA n e = 0 :=
  Subtype.ext rfl

/-- For the zero right action, the reverse map vanishes on every pure tensor. -/
example (n : N) (m : M) :
    letI := NonUnitalModule.zero (A := Aᵐᵒᵖ) (M := N)
    reverse hA N hM (tmul A N M n m) = 0 := by
  let _ := NonUnitalModule.zero (A := Aᵐᵒᵖ) (M := N)
  rw [reverse_tmul hA N hM n m (chosenFixer hM m) (chosenFixer_smul hM m),
    show smoothing hA n (chosenFixer hM m) = 0 from Subtype.ext rfl, zero_tmul]

end ZeroAction

/-- The original unital action of `ℤ` on itself is nondegenerate, with the unit fixing every
element. -/
example :
    letI := NonUnitalModule.ofModule ℤ ℤ
    IsNondegenerate ℤ ℤ := by
  let _ := NonUnitalModule.ofModule ℤ ℤ
  exact fun m => ⟨⟨1, IsIdempotentElem.one⟩, one_smul ℤ m⟩

/-- A concrete nonzero right module with the zero action: `N = ℤ` over the unital ring `ℤ`,
with `M = ℤ` carrying the original unital left action. -/
example :
    letI := NonUnitalModule.zero (A := ℤᵐᵒᵖ) (M := ℤ)
    letI := NonUnitalModule.ofModule ℤ ℤ
    ∀ (hM : IsNondegenerate ℤ ℤ) (n m : ℤ),
      reverse (IsIdempotented.of_ring ℤ) ℤ hM (tmul ℤ ℤ ℤ n m) = 0 := by
  let _ := NonUnitalModule.zero (A := ℤᵐᵒᵖ) (M := ℤ)
  let _ := NonUnitalModule.ofModule ℤ ℤ
  intro hM n m
  rw [reverse_tmul _ ℤ hM n m (chosenFixer hM m) (chosenFixer_smul hM m),
    show smoothing (IsIdempotented.of_ring ℤ) n (chosenFixer hM m) = 0 from Subtype.ext rfl,
    zero_tmul]

/-- The source's complex-algebra case (`k = ℂ`) is a specialization: scalar structures on `A`,
`N` and `M` add no hypothesis and are not used by the construction. -/
example {k : Type*} [CommRing k] {A : Type uA} [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (hA : IsIdempotented A)
    (N : Type uN) [AddCommGroup N] [Module k N] [NonUnitalModule Aᵐᵒᵖ N]
    {M : Type uM} [AddCommGroup M] [Module k M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) (n : N) (m : M) (e : Idempotent A) (he : (e : A) • m = m) :
    reverse hA N hM (tmul A N M n m) =
      tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  reverse_tmul hA N hM n m e he


/-! ## Complete unapplied interfaces at independent universes -/

noncomputable section UniverseChecks

set_option linter.unusedVariables false

/-! Independent universe variables for the ring and both carriers. -/

section ArbitraryUniverses

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M],
      Tensor A (nondegeneratePart hA.op N) M →+ Tensor A N M :=
  @inclusion

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M],
      inclusion hA N M =
        map A (nondegeneratePart hA.op N).subtype (NonUnitalModuleHom.id A M) :=
  @inclusion_eq_map

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M],
      ∀ (n : nondegeneratePart hA.op N) (m : M),
        inclusion hA N M (tmul A (nondegeneratePart hA.op N) M n m) = tmul A N M (n : N) m :=
  @inclusion_tmul

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M],
      (fun (n : nondegeneratePart hA.op N) (m : M) =>
          inclusion hA N M (tmul A (nondegeneratePart hA.op N) M n m)) =
        fun (n : nondegeneratePart hA.op N) (m : M) => tmul A N M (n : N) m :=
  @inclusion_pure_function

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
      Idempotent Aᵐᵒᵖ :=
  @oppositeIdempotent

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
      (oppositeIdempotent e : Aᵐᵒᵖ) = op (e : A) :=
  @oppositeIdempotent_val

example : ∀ {A : Type uA} [NonUnitalRing A] {N : Type uN} [AddCommGroup N]
    [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (e : Idempotent A) (n : N), op (e : A) • (op (e : A) • n) = op (e : A) • n :=
  @op_smul_op_smul_self

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) {N : Type uN}
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) (e : Idempotent A), op (e : A) • n ∈ nondegeneratePart hA.op N :=
  @smul_mem_nondegeneratePart

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) {N : Type uN}
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) (e : Idempotent A), nondegeneratePart hA.op N :=
  @smoothing

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) (e : Idempotent A), (smoothing hA n e : N) = op (e : A) • n :=
  @smoothing_val

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (e : Idempotent A), smoothing hA (0 : N) e = 0 :=
  @smoothing_zero

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n n' : N) (e : Idempotent A),
        smoothing hA (n + n') e = smoothing hA n e + smoothing hA n' e :=
  @smoothing_add

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) (e : Idempotent A),
        (oppositeIdempotent e : Aᵐᵒᵖ) • smoothing hA n e = smoothing hA n e :=
  @oppositeIdempotent_smul_smoothing

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) {e h : Idempotent A}, e ≤ h →
        op (e : A) • smoothing hA n h = smoothing hA n e :=
  @op_smul_smoothing_of_le

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M],
      ∀ (n : N) {m : M} {e h : Idempotent A}, e ≤ h → (e : A) • m = m →
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n h) m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  @tmul_smoothing_eq_of_le

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M],
      ∀ (n : N) {m : M} {e f : Idempotent A}, (e : A) • m = m → (f : A) • m = m →
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n f) m :=
  @tmul_smoothing_eq

example : ∀ {A : Type uA} [NonUnitalRing A] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (m : M), Idempotent A :=
  @chosenFixer

example : ∀ {A : Type uA} [NonUnitalRing A] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (m : M), (chosenFixer hM m : A) • m = m :=
  @chosenFixer_smul

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M), Tensor A (nondegeneratePart hA.op N) M :=
  @reverseFun

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
        reverseFun hA N hM n m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  @reverseFun_eq

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (m : M), reverseFun hA N hM 0 m = 0 :=
  @reverseFun_zero_left

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n n' : N) (m : M),
        reverseFun hA N hM (n + n') m = reverseFun hA N hM n m + reverseFun hA N hM n' m :=
  @reverseFun_add_left

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N), reverseFun hA N hM n 0 = 0 :=
  @reverseFun_zero_right

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m m' : M),
        reverseFun hA N hM n (m + m') = reverseFun hA N hM n m + reverseFun hA N hM n m' :=
  @reverseFun_add_right

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      N →+ M →+ Tensor A (nondegeneratePart hA.op N) M :=
  @reverseBiadditive

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M), reverseBiadditive hA N hM n m = reverseFun hA N hM n m :=
  @reverseBiadditive_apply

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
        reverseBiadditive hA N hM n m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  @reverseBiadditive_eq

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) {M : Type uM}
    [AddCommGroup M] [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (a : A) (m : M),
        ∃ h : Idempotent A, (h : A) • m = m ∧ (h : A) * a = a ∧ a * (h : A) = a :=
  @exists_fixer_mem_corner

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      IsBalanced A (reverseBiadditive hA N hM) :=
  @reverseBiadditive_balanced

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      Tensor A N M →+ Tensor A (nondegeneratePart hA.op N) M :=
  @reverse

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      reverse hA N hM =
        lift A (reverseBiadditive hA N hM) (reverseBiadditive_balanced hA N hM) :=
  @reverse_eq_lift

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      (reverse hA N hM).comp (projection A N M) =
        integerLift (reverseBiadditive hA N hM) :=
  @reverse_comp_projection

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M),
        reverse hA N hM (tmul A N M n m) = reverseBiadditive hA N hM n m :=
  @reverse_tmul_eq_reverseBiadditive

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      (fun (n : N) (m : M) => reverse hA N hM (tmul A N M n m)) =
        fun n m => reverseBiadditive hA N hM n m :=
  @reverse_pure_function

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (f : Tensor A N M →+ Tensor A (nondegeneratePart hA.op N) M),
        (∀ n m, f (tmul A N M n m) = reverseBiadditive hA N hM n m) → f = reverse hA N hM :=
  @reverse_unique

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
        reverse hA N hM (tmul A N M n m) =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  @reverse_tmul

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type uN)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type uM} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M) (e f : Idempotent A), (e : A) • m = m → (f : A) • m = m →
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n f) m :=
  @reverse_tmul_independent

end ArbitraryUniverses

/-! Ring and left carrier in `Type 0`, right carrier in `Type 1`. -/

section ZeroOneZero

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type 0) [AddCommGroup M]
    [NonUnitalModule A M],
      Tensor A (nondegeneratePart hA.op N) M →+ Tensor A N M :=
  @inclusion

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type 0) [AddCommGroup M]
    [NonUnitalModule A M],
      inclusion hA N M =
        map A (nondegeneratePart hA.op N).subtype (NonUnitalModuleHom.id A M) :=
  @inclusion_eq_map

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type 0) [AddCommGroup M]
    [NonUnitalModule A M],
      ∀ (n : nondegeneratePart hA.op N) (m : M),
        inclusion hA N M (tmul A (nondegeneratePart hA.op N) M n m) = tmul A N M (n : N) m :=
  @inclusion_tmul

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type 0) [AddCommGroup M]
    [NonUnitalModule A M],
      (fun (n : nondegeneratePart hA.op N) (m : M) =>
          inclusion hA N M (tmul A (nondegeneratePart hA.op N) M n m)) =
        fun (n : nondegeneratePart hA.op N) (m : M) => tmul A N M (n : N) m :=
  @inclusion_pure_function

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A),
      Idempotent Aᵐᵒᵖ :=
  @oppositeIdempotent

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A),
      (oppositeIdempotent e : Aᵐᵒᵖ) = op (e : A) :=
  @oppositeIdempotent_val

example : ∀ {A : Type 0} [NonUnitalRing A] {N : Type 1} [AddCommGroup N]
    [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (e : Idempotent A) (n : N), op (e : A) • (op (e : A) • n) = op (e : A) • n :=
  @op_smul_op_smul_self

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) {N : Type 1}
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) (e : Idempotent A), op (e : A) • n ∈ nondegeneratePart hA.op N :=
  @smul_mem_nondegeneratePart

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) {N : Type 1}
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) (e : Idempotent A), nondegeneratePart hA.op N :=
  @smoothing

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) (e : Idempotent A), (smoothing hA n e : N) = op (e : A) • n :=
  @smoothing_val

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (e : Idempotent A), smoothing hA (0 : N) e = 0 :=
  @smoothing_zero

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n n' : N) (e : Idempotent A),
        smoothing hA (n + n') e = smoothing hA n e + smoothing hA n' e :=
  @smoothing_add

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) (e : Idempotent A),
        (oppositeIdempotent e : Aᵐᵒᵖ) • smoothing hA n e = smoothing hA n e :=
  @oppositeIdempotent_smul_smoothing

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) {e h : Idempotent A}, e ≤ h →
        op (e : A) • smoothing hA n h = smoothing hA n e :=
  @op_smul_smoothing_of_le

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type 0) [AddCommGroup M]
    [NonUnitalModule A M],
      ∀ (n : N) {m : M} {e h : Idempotent A}, e ≤ h → (e : A) • m = m →
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n h) m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  @tmul_smoothing_eq_of_le

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type 0) [AddCommGroup M]
    [NonUnitalModule A M],
      ∀ (n : N) {m : M} {e f : Idempotent A}, (e : A) • m = m → (f : A) • m = m →
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n f) m :=
  @tmul_smoothing_eq

example : ∀ {A : Type 0} [NonUnitalRing A] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (m : M), Idempotent A :=
  @chosenFixer

example : ∀ {A : Type 0} [NonUnitalRing A] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (m : M), (chosenFixer hM m : A) • m = m :=
  @chosenFixer_smul

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M), Tensor A (nondegeneratePart hA.op N) M :=
  @reverseFun

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
        reverseFun hA N hM n m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  @reverseFun_eq

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (m : M), reverseFun hA N hM 0 m = 0 :=
  @reverseFun_zero_left

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n n' : N) (m : M),
        reverseFun hA N hM (n + n') m = reverseFun hA N hM n m + reverseFun hA N hM n' m :=
  @reverseFun_add_left

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N), reverseFun hA N hM n 0 = 0 :=
  @reverseFun_zero_right

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m m' : M),
        reverseFun hA N hM n (m + m') = reverseFun hA N hM n m + reverseFun hA N hM n m' :=
  @reverseFun_add_right

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      N →+ M →+ Tensor A (nondegeneratePart hA.op N) M :=
  @reverseBiadditive

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M), reverseBiadditive hA N hM n m = reverseFun hA N hM n m :=
  @reverseBiadditive_apply

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
        reverseBiadditive hA N hM n m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  @reverseBiadditive_eq

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) {M : Type 0}
    [AddCommGroup M] [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (a : A) (m : M),
        ∃ h : Idempotent A, (h : A) • m = m ∧ (h : A) * a = a ∧ a * (h : A) = a :=
  @exists_fixer_mem_corner

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      IsBalanced A (reverseBiadditive hA N hM) :=
  @reverseBiadditive_balanced

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      Tensor A N M →+ Tensor A (nondegeneratePart hA.op N) M :=
  @reverse

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      reverse hA N hM =
        lift A (reverseBiadditive hA N hM) (reverseBiadditive_balanced hA N hM) :=
  @reverse_eq_lift

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      (reverse hA N hM).comp (projection A N M) =
        integerLift (reverseBiadditive hA N hM) :=
  @reverse_comp_projection

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M),
        reverse hA N hM (tmul A N M n m) = reverseBiadditive hA N hM n m :=
  @reverse_tmul_eq_reverseBiadditive

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      (fun (n : N) (m : M) => reverse hA N hM (tmul A N M n m)) =
        fun n m => reverseBiadditive hA N hM n m :=
  @reverse_pure_function

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (f : Tensor A N M →+ Tensor A (nondegeneratePart hA.op N) M),
        (∀ n m, f (tmul A N M n m) = reverseBiadditive hA N hM n m) → f = reverse hA N hM :=
  @reverse_unique

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
        reverse hA N hM (tmul A N M n m) =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  @reverse_tmul

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 1)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 0} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M) (e f : Idempotent A), (e : A) • m = m → (f : A) • m = m →
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n f) m :=
  @reverse_tmul_independent

end ZeroOneZero

/-! Ring and left carrier in `Type 1`, right carrier in `Type 0`. -/

section OneZeroOne

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type 1) [AddCommGroup M]
    [NonUnitalModule A M],
      Tensor A (nondegeneratePart hA.op N) M →+ Tensor A N M :=
  @inclusion

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type 1) [AddCommGroup M]
    [NonUnitalModule A M],
      inclusion hA N M =
        map A (nondegeneratePart hA.op N).subtype (NonUnitalModuleHom.id A M) :=
  @inclusion_eq_map

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type 1) [AddCommGroup M]
    [NonUnitalModule A M],
      ∀ (n : nondegeneratePart hA.op N) (m : M),
        inclusion hA N M (tmul A (nondegeneratePart hA.op N) M n m) = tmul A N M (n : N) m :=
  @inclusion_tmul

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type 1) [AddCommGroup M]
    [NonUnitalModule A M],
      (fun (n : nondegeneratePart hA.op N) (m : M) =>
          inclusion hA N M (tmul A (nondegeneratePart hA.op N) M n m)) =
        fun (n : nondegeneratePart hA.op N) (m : M) => tmul A N M (n : N) m :=
  @inclusion_pure_function

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A),
      Idempotent Aᵐᵒᵖ :=
  @oppositeIdempotent

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A),
      (oppositeIdempotent e : Aᵐᵒᵖ) = op (e : A) :=
  @oppositeIdempotent_val

example : ∀ {A : Type 1} [NonUnitalRing A] {N : Type 0} [AddCommGroup N]
    [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (e : Idempotent A) (n : N), op (e : A) • (op (e : A) • n) = op (e : A) • n :=
  @op_smul_op_smul_self

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) {N : Type 0}
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) (e : Idempotent A), op (e : A) • n ∈ nondegeneratePart hA.op N :=
  @smul_mem_nondegeneratePart

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) {N : Type 0}
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) (e : Idempotent A), nondegeneratePart hA.op N :=
  @smoothing

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) (e : Idempotent A), (smoothing hA n e : N) = op (e : A) • n :=
  @smoothing_val

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (e : Idempotent A), smoothing hA (0 : N) e = 0 :=
  @smoothing_zero

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n n' : N) (e : Idempotent A),
        smoothing hA (n + n') e = smoothing hA n e + smoothing hA n' e :=
  @smoothing_add

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) (e : Idempotent A),
        (oppositeIdempotent e : Aᵐᵒᵖ) • smoothing hA n e = smoothing hA n e :=
  @oppositeIdempotent_smul_smoothing

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N],
      ∀ (n : N) {e h : Idempotent A}, e ≤ h →
        op (e : A) • smoothing hA n h = smoothing hA n e :=
  @op_smul_smoothing_of_le

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type 1) [AddCommGroup M]
    [NonUnitalModule A M],
      ∀ (n : N) {m : M} {e h : Idempotent A}, e ≤ h → (e : A) • m = m →
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n h) m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  @tmul_smoothing_eq_of_le

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] (M : Type 1) [AddCommGroup M]
    [NonUnitalModule A M],
      ∀ (n : N) {m : M} {e f : Idempotent A}, (e : A) • m = m → (f : A) • m = m →
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n f) m :=
  @tmul_smoothing_eq

example : ∀ {A : Type 1} [NonUnitalRing A] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (m : M), Idempotent A :=
  @chosenFixer

example : ∀ {A : Type 1} [NonUnitalRing A] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (m : M), (chosenFixer hM m : A) • m = m :=
  @chosenFixer_smul

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M), Tensor A (nondegeneratePart hA.op N) M :=
  @reverseFun

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
        reverseFun hA N hM n m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  @reverseFun_eq

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (m : M), reverseFun hA N hM 0 m = 0 :=
  @reverseFun_zero_left

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n n' : N) (m : M),
        reverseFun hA N hM (n + n') m = reverseFun hA N hM n m + reverseFun hA N hM n' m :=
  @reverseFun_add_left

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N), reverseFun hA N hM n 0 = 0 :=
  @reverseFun_zero_right

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m m' : M),
        reverseFun hA N hM n (m + m') = reverseFun hA N hM n m + reverseFun hA N hM n m' :=
  @reverseFun_add_right

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      N →+ M →+ Tensor A (nondegeneratePart hA.op N) M :=
  @reverseBiadditive

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M), reverseBiadditive hA N hM n m = reverseFun hA N hM n m :=
  @reverseBiadditive_apply

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
        reverseBiadditive hA N hM n m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  @reverseBiadditive_eq

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) {M : Type 1}
    [AddCommGroup M] [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (a : A) (m : M),
        ∃ h : Idempotent A, (h : A) • m = m ∧ (h : A) * a = a ∧ a * (h : A) = a :=
  @exists_fixer_mem_corner

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      IsBalanced A (reverseBiadditive hA N hM) :=
  @reverseBiadditive_balanced

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      Tensor A N M →+ Tensor A (nondegeneratePart hA.op N) M :=
  @reverse

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      reverse hA N hM =
        lift A (reverseBiadditive hA N hM) (reverseBiadditive_balanced hA N hM) :=
  @reverse_eq_lift

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      (reverse hA N hM).comp (projection A N M) =
        integerLift (reverseBiadditive hA N hM) :=
  @reverse_comp_projection

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M),
        reverse hA N hM (tmul A N M n m) = reverseBiadditive hA N hM n m :=
  @reverse_tmul_eq_reverseBiadditive

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      (fun (n : N) (m : M) => reverse hA N hM (tmul A N M n m)) =
        fun n m => reverseBiadditive hA N hM n m :=
  @reverse_pure_function

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (f : Tensor A N M →+ Tensor A (nondegeneratePart hA.op N) M),
        (∀ n m, f (tmul A N M n m) = reverseBiadditive hA N hM n m) → f = reverse hA N hM :=
  @reverse_unique

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M) (e : Idempotent A), (e : A) • m = m →
        reverse hA N hM (tmul A N M n m) =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m :=
  @reverse_tmul

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (N : Type 0)
    [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N] {M : Type 1} [AddCommGroup M]
    [NonUnitalModule A M] (hM : IsNondegenerate A M),
      ∀ (n : N) (m : M) (e f : Idempotent A), (e : A) • m = m → (f : A) • m = m →
        tmul A (nondegeneratePart hA.op N) M (smoothing hA n e) m =
          tmul A (nondegeneratePart hA.op N) M (smoothing hA n f) m :=
  @reverse_tmul_independent

end OneZeroOne

end UniverseChecks

end Langlands.Algebra.NonUnitalTensorSmoothing
