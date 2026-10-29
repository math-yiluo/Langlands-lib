import Langlands.Representation.Filtration.InvariantBilinearBounds

/-! Covariant form-length bounds for subrepresentations and quotients of
filtered representations whose graded pieces are zero or irreducible. -/

noncomputable section

namespace Langlands.InvariantBilinear

universe uK uG uV uW uX uY

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable [AddCommGroup X] [Module k X]

/-- A representation whose carrier is zero or which is irreducible. -/
def ZeroOrIrreducible (ρ : Representation k G V) : Prop :=
  Subsingleton V ∨ ρ.IsIrreducible

/-- A zero first argument admits only the zero form. -/
theorem length_eq_zero_of_subsingleton_left (ρ : Representation k G V)
    (σ : Representation k G W) (χ : G → k) [Subsingleton V] : length ρ σ χ = 0 := by
  apply Module.length_eq_zero_iff.mpr
  constructor
  intro B C
  apply Subtype.ext
  ext v w
  rw [Subsingleton.elim v 0]
  simp

/-- An injective intertwiner into a zero or irreducible representation bounds length. -/
theorem length_le_of_injective_left {ρ : Representation k G V} {τ : Representation k G X}
    (σ : Representation k G W) (χ : G → k) (f : ρ.IntertwiningMap τ)
    (hf : Function.Injective f) (hτ : ZeroOrIrreducible τ) :
    length ρ σ χ ≤ length τ σ χ := by
  have hzero : Subsingleton V → length ρ σ χ ≤ length τ σ χ := fun _ => by
    rw [length_eq_zero_of_subsingleton_left]
    exact zero_le
  rcases hτ with hX | hirr
  · exact hzero ⟨fun a b => hf (Subsingleton.elim _ _)⟩
  · have := hirr
    rcases Representation.IsIrreducible.surjective_or_eq_zero f with hs | h0
    · exact le_of_eq (length_congr_left σ χ (f.ofBijective ⟨hf, hs⟩))
    · apply hzero
      refine ⟨fun a b => hf ?_⟩
      rw [h0]
      rfl

/-- A surjective intertwiner from the first argument bounds length. -/
theorem length_le_of_surjective_left {ρ : Representation k G V} {τ : Representation k G X}
    (σ : Representation k G W) (χ : G → k) (f : ρ.IntertwiningMap τ)
    (hf : Function.Surjective f) : length τ σ χ ≤ length ρ σ χ :=
  Module.length_le_of_injective (comapLeft σ χ f) (comapLeft_injective σ χ f hf)

/-- The preimage of an invariant subspace under an intertwining map. -/
def subrepresentationComap {ρ : Representation k G X} {τ : Representation k G V}
    (f : ρ.IntertwiningMap τ) (S : Subrepresentation τ) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.comap f.toLinearMap
  apply_mem_toSubmodule g v hv := by
    change f (ρ g v) ∈ S.toSubmodule
    rw [f.isIntertwining]
    exact S.apply_mem_toSubmodule g hv

/-- Pull an actual object filtration back along an injective intertwining map. -/
def filtrationComap {A : Rep.{uX} k G} {B : Rep.{uV} k G} {n : ℕ}
    (f : A.ρ.IntertwiningMap B.ρ) (hf : Function.Injective f)
    (t : ObjectRepFiltration B n) : ObjectRepFiltration A n :=
  ObjectRepFiltration.ofSubrepresentations
    (fun i => subrepresentationComap f (t.subrepresentation i))
    (fun _ _ hij _ hv => t.monotone_subrepresentation hij hv)
    (by
      apply Subrepresentation.ext
      ext v
      change f v ∈ (t.subrepresentation 0).toSubmodule ↔ v ∈ (⊥ : Submodule k A)
      rw [t.subrepresentation_zero]
      change f v ∈ (⊥ : Submodule k B) ↔ v ∈ (⊥ : Submodule k A)
      rw [Submodule.mem_bot, Submodule.mem_bot]
      constructor
      · intro h
        exact hf (h.trans (map_zero f).symm)
      · intro h
        rw [h, map_zero])
    (by
      apply Subrepresentation.ext
      ext v
      change f v ∈ (t.subrepresentation (Fin.last n)).toSubmodule ↔ v ∈ (⊤ : Submodule k A)
      rw [t.subrepresentation_last]
      exact Iff.rfl)

/-- The graded pieces of a pulled-back filtration map injectively to the original ones. -/
def filtrationComapGradedMap {A : Rep.{uX} k G} {B : Rep.{uV} k G} {n : ℕ}
    (f : A.ρ.IntertwiningMap B.ρ) (hf : Function.Injective f)
    (t : ObjectRepFiltration B n) (i : Fin n) :
    ((filtrationComap f hf t).gradedRepresentation i).ρ.IntertwiningMap
      (t.gradedRepresentation i).ρ where
  toLinearMap :=
    Submodule.mapQ _ _
      (f.toLinearMap.restrict (p := (t.subrepresentation i.succ).toSubmodule.comap f.toLinearMap)
        (q := (t.subrepresentation i.succ).toSubmodule) (fun _ hv => hv))
      (fun _ hv => hv)
  isIntertwining' g := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ q
    apply congrArg (Submodule.mkQ _)
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining A.ρ B.ρ f g v.val

theorem filtrationComapGradedMap_injective {A : Rep.{uX} k G} {B : Rep.{uV} k G} {n : ℕ}
    (f : A.ρ.IntertwiningMap B.ρ) (hf : Function.Injective f)
    (t : ObjectRepFiltration B n) (i : Fin n) :
    Function.Injective (filtrationComapGradedMap f hf t i) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ b
  have hab' := (Submodule.Quotient.eq _).mp hab
  apply (Submodule.Quotient.eq _).mpr
  change f (a.val - b.val) ∈ (t.subrepresentation i.castSucc).toSubmodule
  rw [map_sub]
  exact hab'

/-- `A` is an actual subrepresentation or an actual quotient of `M`, witnessed by an
injective or a surjective intertwining map. -/
def IsSubOrQuotient (A : Rep.{uX} k G) (M : Rep.{uV} k G) : Prop :=
  (∃ f : A.ρ.IntertwiningMap M.ρ, Function.Injective f) ∨
    ∃ f : M.ρ.IntertwiningMap A.ρ, Function.Surjective f

/-- Zero or irreducible graded pieces bound the form length of a subrepresentation. -/
theorem length_le_sum_of_injective_left {A : Rep.{uX} k G} {M : Rep.{uV} k G} {n : ℕ}
    (f : A.ρ.IntertwiningMap M.ρ) (hf : Function.Injective f) (t : ObjectRepFiltration M n)
    (ht : ∀ i, ZeroOrIrreducible (t.gradedRepresentation i).ρ)
    (σ : Representation k G W) (χ : G → k) :
    length A.ρ σ χ ≤ ∑ i : Fin n, length (t.gradedRepresentation i).ρ σ χ :=
  (length_le_sum_left (filtrationComap f hf t) σ χ).trans
    (Finset.sum_le_sum fun i _ => length_le_of_injective_left σ χ
      (filtrationComapGradedMap f hf t i) (filtrationComapGradedMap_injective f hf t i) (ht i))

/-- The graded bound for a subrepresentation or a quotient in the first argument. -/
theorem length_le_sum_of_isSubOrQuotient_left {A : Rep.{uX} k G} {M : Rep.{uV} k G} {n : ℕ}
    (hA : IsSubOrQuotient A M) (t : ObjectRepFiltration M n)
    (ht : ∀ i, ZeroOrIrreducible (t.gradedRepresentation i).ρ)
    (σ : Representation k G W) (χ : G → k) :
    length A.ρ σ χ ≤ ∑ i : Fin n, length (t.gradedRepresentation i).ρ σ χ := by
  rcases hA with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact length_le_sum_of_injective_left f hf t ht σ χ
  · exact (length_le_of_surjective_left σ χ f hf).trans (length_le_sum_left t σ χ)

/-- If no pair of graded pieces carries a nonzero covariant form, then neither does any
pair of subrepresentations or quotients of the two filtered representations. -/
theorem length_eq_zero_of_isSubOrQuotient {A : Rep.{uX} k G} {M : Rep.{uV} k G}
    {C : Rep.{uY} k G} {N : Rep.{uW} k G} {m n : ℕ}
    (hA : IsSubOrQuotient A M) (hC : IsSubOrQuotient C N)
    (s : ObjectRepFiltration M m) (t : ObjectRepFiltration N n)
    (hs : ∀ i, ZeroOrIrreducible (s.gradedRepresentation i).ρ)
    (ht : ∀ j, ZeroOrIrreducible (t.gradedRepresentation j).ρ) (χ : G → k)
    (hzero : ∀ i j, length (s.gradedRepresentation i).ρ (t.gradedRepresentation j).ρ χ = 0) :
    length A.ρ C.ρ χ = 0 := by
  refine le_antisymm ?_ zero_le
  refine (length_le_sum_of_isSubOrQuotient_left hA s hs C.ρ χ).trans (le_of_eq ?_)
  apply Finset.sum_eq_zero
  intro i _
  rw [length_flip]
  refine le_antisymm ?_ zero_le
  refine (length_le_sum_of_isSubOrQuotient_left hC t ht _ χ).trans (le_of_eq ?_)
  apply Finset.sum_eq_zero
  intro j _
  rw [length_flip]
  exact hzero i j

end Langlands.InvariantBilinear
