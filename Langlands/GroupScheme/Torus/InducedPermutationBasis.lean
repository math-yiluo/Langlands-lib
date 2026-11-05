import Langlands.GroupScheme.Torus.Induced
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Basis.Submodule

/-! # Permuted bases and the induced-torus lattice criterion -/

noncomputable section

universe u v w

namespace Langlands.PermutationBasis

section Transport

variable {R Γ L N I : Type*} [CommRing R] [Monoid Γ]
  [AddCommGroup L] [Module R L] [AddCommGroup N] [Module R N]

/-- An equivariant linear equivalence carries a permuted basis to a permuted basis. -/
theorem map_permuted (ρ : Representation R Γ L) (τ : Representation R Γ N)
    (b : Module.Basis I R L) (e : L ≃ₗ[R] N)
    (he : ∀ g x, e (ρ g x) = τ g (e x))
    (hb : ∀ g i, ∃ j, ρ g (b i) = b j) :
    ∀ g i, ∃ j, τ g ((b.map e) i) = (b.map e) j := by
  intro g i
  obtain ⟨j, hj⟩ := hb g i
  refine ⟨j, ?_⟩
  simpa only [Module.Basis.map_apply, he] using congrArg e hj

end Transport

section IndexAction

variable {R Γ L I : Type*} [CommRing R] [Nontrivial R] [Group Γ]
  [AddCommGroup L] [Module R L]
  (ρ : Representation R Γ L) (b : Module.Basis I R L)
  (hb : ∀ g i, ∃ j, ρ g (b i) = b j)

private def indexMap (g : Γ) (i : I) : I := Classical.choose (hb g i)

omit [Nontrivial R] in
private theorem indexMap_spec (g : Γ) (i : I) :
    ρ g (b i) = b (indexMap ρ b hb g i) :=
  Classical.choose_spec (hb g i)

private theorem indexMap_inv (g : Γ) (i : I) :
    indexMap ρ b hb g⁻¹ (indexMap ρ b hb g i) = i := by
  apply b.injective
  rw [← indexMap_spec, ← indexMap_spec]
  change (ρ g⁻¹ * ρ g) (b i) = b i
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

/-- Setwise preservation of a basis by a group representation gives a permutation
of its index set, including when the index type is empty or infinite. -/
def indexEquiv (g : Γ) : Equiv.Perm I where
  toFun := indexMap ρ b hb g
  invFun := indexMap ρ b hb g⁻¹
  left_inv := indexMap_inv ρ b hb g
  right_inv := by
    intro i
    simpa only [inv_inv] using indexMap_inv ρ b hb g⁻¹ i

theorem apply_basis (g : Γ) (i : I) :
    ρ g (b i) = b (indexEquiv ρ b hb g i) :=
  indexMap_spec ρ b hb g i

/-- The permutations induced by the representation satisfy the group law. -/
def indexAction : Γ →* Equiv.Perm I where
  toFun := indexEquiv ρ b hb
  map_one' := by
    apply Equiv.ext
    intro i
    apply b.injective
    rw [← apply_basis, map_one]
    rfl
  map_mul' g h := by
    apply Equiv.ext
    intro i
    apply b.injective
    change b (indexEquiv ρ b hb (g * h) i) =
      b (indexEquiv ρ b hb g (indexEquiv ρ b hb h i))
    rw [← apply_basis, ← apply_basis, ← apply_basis, map_mul]
    rfl

end IndexAction

section Complement

variable {R L I : Type*} [CommRing R] [AddCommGroup L] [Module R L]
  (b : Module.Basis I R L) (s : Set I)

/-- The span of the basis vectors whose indices lie outside `s`. -/
def complementSpan : Submodule R L :=
  Submodule.span R (Set.range fun i : {i // i ∉ s} => b i)

theorem complementSpan_eq_span_image :
    complementSpan b s = Submodule.span R (b '' sᶜ) := by
  unfold complementSpan
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_image, Set.mem_compl_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.property, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

/-- The complement span consists precisely of vectors whose `s`-coordinates vanish. -/
theorem mem_complementSpan_iff (x : L) :
    x ∈ complementSpan b s ↔ ∀ i ∈ s, b.repr x i = 0 := by
  classical
  rw [complementSpan_eq_span_image, b.mem_span_image]
  constructor
  · intro hx i hi
    by_contra h
    exact hx (Finsupp.mem_support_iff.mpr h) hi
  · intro hx i hi his
    exact (Finsupp.mem_support_iff.mp hi) (hx i his)

/-- The surviving basis vectors form a basis of the complement span. -/
def complementBasis : Module.Basis {i // i ∉ s} R (complementSpan b s) :=
  Module.Basis.span (b.linearIndependent.comp _ Subtype.val_injective)

@[simp] theorem complementBasis_apply (i : {i // i ∉ s}) :
    (complementBasis b s i : L) = b i :=
  Module.Basis.coe_span_apply _ _

end Complement

section CharacterImage

variable {R Γ L N I : Type*} [CommRing R] [Monoid Γ]
  [AddCommGroup L] [Module R L] [AddCommGroup N] [Module R N]
  (b : Module.Basis I R L) (s : Set I)
  (f : N →ₗ[R] L) (hf : Function.Injective f)
  (hrange : f.range = complementSpan b s)

/-- An injective linear map onto the complement span identifies its domain with that span. -/
def complementRangeEquiv : N ≃ₗ[R] complementSpan b s :=
  (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hrange)

@[simp] theorem complementRangeEquiv_apply (x : N) :
    (complementRangeEquiv b s f hf hrange x : L) = f x := rfl

/-- The complementary basis pulled back along an injective map with the stated image. -/
def pullbackComplementBasis : Module.Basis {i // i ∉ s} R N :=
  (complementBasis b s).map (complementRangeEquiv b s f hf hrange).symm

@[simp] theorem map_pullbackComplementBasis (i : {i // i ∉ s}) :
    f (pullbackComplementBasis b s f hf hrange i) = b i := by
  change f ((complementRangeEquiv b s f hf hrange).symm (complementBasis b s i)) = b i
  calc
    _ = (complementRangeEquiv b s f hf hrange
        ((complementRangeEquiv b s f hf hrange).symm (complementBasis b s i)) : L) := rfl
    _ = (complementBasis b s i : L) :=
      congrArg (fun x : complementSpan b s => (x : L)) (LinearEquiv.apply_symm_apply _ _)
    _ = b i := complementBasis_apply b s i

/-- A basis-permuting twisted action descends through the character embedding when
each twisting operator fixes its entire image. The twisting operators need not
themselves form a representation. -/
theorem pullbackComplementBasis_permuted_of_twist
    (ρ : Representation R Γ L) (τ : Representation R Γ N)
    (w : Γ → L →ₗ[R] L)
    (he : ∀ g x, f (τ g x) = ρ g (f x))
    (hfix : ∀ g x, w g (f x) = f x)
    (hb : ∀ g (i : {i // i ∉ s}), ∃ j : {i // i ∉ s},
      w g (ρ g (b i)) = b j) :
    ∀ g i, ∃ j,
      τ g (pullbackComplementBasis b s f hf hrange i) =
        pullbackComplementBasis b s f hf hrange j := by
  intro g i
  obtain ⟨j, hj⟩ := hb g i
  refine ⟨j, hf ?_⟩
  calc
    f (τ g (pullbackComplementBasis b s f hf hrange i)) =
        w g (f (τ g (pullbackComplementBasis b s f hf hrange i))) := (hfix _ _).symm
    _ = w g (ρ g (b i)) := by rw [he, map_pullbackComplementBasis]
    _ = b j := hj
    _ = f (pullbackComplementBasis b s f hf hrange j) :=
      (map_pullbackComplementBasis b s f hf hrange j).symm

/-- The untwisted specialization of the complement-basis transport. -/
theorem pullbackComplementBasis_permuted
    (ρ : Representation R Γ L) (τ : Representation R Γ N)
    (he : ∀ g x, f (τ g x) = ρ g (f x))
    (hb : ∀ g (i : {i // i ∉ s}), ∃ j : {i // i ∉ s}, ρ g (b i) = b j) :
    ∀ g i, ∃ j,
      τ g (pullbackComplementBasis b s f hf hrange i) =
        pullbackComplementBasis b s f hf hrange j :=
  pullbackComplementBasis_permuted_of_twist b s f hf hrange ρ τ
    (fun _ => LinearMap.id) he (fun _ _ => rfl) hb

end CharacterImage

end Langlands.PermutationBasis

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A finite Galois splitting field and an equivariant permuted lattice basis
give the actual induced-torus predicate. -/
theorem isInducedTorus_of_equivariant_basis
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E]
    (hsplit : IsSplitTorus (GaloisPointComparison.baseChanged k E T.toGrp))
    {L I : Type u} [AddCommGroup L] [Module ℤ L]
    (ρ : Representation ℤ (E ≃ₐ[k] E) L) (b : Module.Basis I ℤ L)
    (e : L ≃ₗ[ℤ]
      characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
    (he : ∀ σ x, e (ρ σ x) = characterLattice.galoisRepresentation k E T σ (e x))
    (hb : ∀ σ i, ∃ j, ρ σ (b i) = b j) :
    IsInducedTorus T := by
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, hsplit,
    I, b.map e, ?_⟩
  exact Langlands.PermutationBasis.map_permuted ρ
    (characterLattice.galoisRepresentation k E T) b e he hb

open Langlands.PermutationBasis

/-- A finite Galois splitting field and a fundamental-weight complement model of
the actual character lattice imply that the torus is induced. Weyl corrections
are allowed provided they fix every character in the image of that lattice. -/
theorem isInducedTorus_of_twisted_complement
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E]
    (hsplit : IsSplitTorus (GaloisPointComparison.baseChanged k E T.toGrp))
    {L I : Type u} [AddCommGroup L] [Module ℤ L]
    (b : Module.Basis I ℤ L) (s : Set I)
    (f : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T) →ₗ[ℤ] L)
    (hf : Function.Injective f) (hrange : f.range = complementSpan b s)
    (ρ : Representation ℤ (E ≃ₐ[k] E) L)
    (w : (E ≃ₐ[k] E) → L →ₗ[ℤ] L)
    (he : ∀ σ x, f (characterLattice.galoisRepresentation k E T σ x) = ρ σ (f x))
    (hfix : ∀ σ x, w σ (f x) = f x)
    (hb : ∀ σ (i : {i // i ∉ s}), ∃ j : {i // i ∉ s},
      w σ (ρ σ (b i)) = b j) :
    IsInducedTorus T := by
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, hsplit,
    {i // i ∉ s}, pullbackComplementBasis b s f hf hrange, ?_⟩
  exact pullbackComplementBasis_permuted_of_twist b s f hf hrange ρ
    (characterLattice.galoisRepresentation k E T) w he hfix hb

end Langlands.GroupScheme
