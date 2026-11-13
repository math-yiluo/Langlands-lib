import Langlands.Geometry.Building.AffineChamberCartanMarks
import Langlands.Geometry.Building.AffineChamberWallComparisonProof
import Langlands.Geometry.Building.AffineChamberTransitivity

/-!
# Irreducible affine root systems and linear independence of simple affine roots

KP Definition 1.3.13 (irreducibility) and KP Proposition 1.3.22(5): for an irreducible affine
root system, the simple affine roots of a chamber are linearly independent affine functionals.
The proof goes through the Cartan matrix of the chamber: an orthogonal splitting of the simple
roots splits the whole root system, and otherwise the left kernel of the Cartan matrix is a line
spanned by the positive marks.
-/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

open Matrix GalleryGeometry

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

/-- Two sets of roots of `Ψ` are orthogonal (KP Definition 1.3.13) when `ψ̇(η̇∨) = 0` and
`η̇(ψ̇∨) = 0` for every `ψ` in the first, every `η` in the second, and all their coroot
vectors. -/
def RootsOrthogonal (Ψ Ψ₁ Ψ₂ : Set (A →ᵃ[ℝ] ℝ)) : Prop :=
  ∀ ψ ∈ Ψ₁, ∀ η ∈ Ψ₂, ∀ u v : V, IsCoroot Ψ ψ u → IsCoroot Ψ η v →
    ψ.linear v = 0 ∧ η.linear u = 0

/-- `Ψ` is irreducible (KP Definition 1.3.13): it is not the union of two nonempty orthogonal
subsets. The empty set satisfies this predicate; nonemptiness is a separate hypothesis. -/
def IsIrreducibleRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Prop :=
  ∀ Ψ₁ Ψ₂ : Set (A →ᵃ[ℝ] ℝ), Ψ₁ ∪ Ψ₂ = Ψ → RootsOrthogonal Ψ Ψ₁ Ψ₂ → Ψ₁ = ∅ ∨ Ψ₂ = ∅

/-! ### Invariant subspaces of the dual space -/

section Invariant

/-- If every generator `g` and its inverse pull a subspace `U` of `V*` back into itself, then so
does every element of the generated subgroup. -/
theorem comp_linear_mem_of_mem_closure {G : Set (A ≃ᵃ[ℝ] A)}
    (U : Submodule ℝ (Module.Dual ℝ V))
    (hG : ∀ g ∈ G, ∀ α ∈ U, α ∘ₗ (g.linear : V →ₗ[ℝ] V) ∈ U)
    (hGinv : ∀ g ∈ G, ∀ α ∈ U, α ∘ₗ ((g⁻¹ : A ≃ᵃ[ℝ] A).linear : V →ₗ[ℝ] V) ∈ U)
    {w : A ≃ᵃ[ℝ] A} (hw : w ∈ Subgroup.closure G) {α : Module.Dual ℝ V} (hα : α ∈ U) :
    α ∘ₗ (w.linear : V →ₗ[ℝ] V) ∈ U := by
  let Q : (A ≃ᵃ[ℝ] A) → Prop := fun w =>
    (∀ α ∈ U, α ∘ₗ (w.linear : V →ₗ[ℝ] V) ∈ U) ∧
      ∀ α ∈ U, α ∘ₗ ((w⁻¹ : A ≃ᵃ[ℝ] A).linear : V →ₗ[ℝ] V) ∈ U
  have hQ : Q w := by
    induction hw using Subgroup.closure_induction with
    | mem g hg => exact ⟨hG g hg, hGinv g hg⟩
    | one =>
      refine ⟨fun α hα => ?_, fun α hα => ?_⟩
      · convert hα using 1
        ext v
        rfl
      · convert hα using 1
        ext v
        rfl
    | mul w₁ w₂ _ _ h₁ h₂ =>
      refine ⟨fun α hα => ?_, fun α hα => ?_⟩
      · have h := h₂.1 _ (h₁.1 α hα)
        convert h using 1
        ext v
        rfl
      · have h := h₁.2 _ (h₂.2 α hα)
        convert h using 1
        rw [_root_.mul_inv_rev]
        ext v
        rfl
    | inv w _ h =>
      refine ⟨h.2, fun α hα => ?_⟩
      rw [inv_inv]
      exact h.1 α hα
  exact hQ.1 α hα

/-- Pulling back along the linear part of an affine reflection. -/
theorem comp_affineReflection_linear (ψ : A →ᵃ[ℝ] ℝ) {v : V} (hv : ψ.linear v = 2)
    (α : Module.Dual ℝ V) :
    α ∘ₗ ((affineReflection ψ hv).linear : V →ₗ[ℝ] V) = α - α v • ψ.linear := by
  ext w
  simp only [affineReflection_linear, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Module.reflection_apply, map_sub, map_smul, smul_eq_mul,
    LinearMap.sub_apply, LinearMap.smul_apply]
  ring

end Invariant

namespace IsAffineRootSystemWithRankZero

variable {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ) {c : A}

include hΨ

/-! ### The coroot form on spans -/

/-- The coroot form as a bilinear map. -/
def corootBilin : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ hΨ.corootForm
    (fun a b c => by
      simp only [corootForm, LinearMap.add_apply, add_mul, Finset.sum_add_distrib])
    (fun r a b => by
      simp only [corootForm, LinearMap.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum])
    (fun a b c => by
      simp only [corootForm, LinearMap.add_apply, mul_add, Finset.sum_add_distrib])
    (fun r a b => by
      simp only [corootForm, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)

theorem corootBilin_apply (α α' : Module.Dual ℝ V) :
    hΨ.corootBilin α α' = hΨ.corootForm α α' :=
  rfl

/-- The coroot form vanishes on the spans of two mutually orthogonal sets. -/
theorem corootForm_eq_zero_of_mem_span {s t : Set (Module.Dual ℝ V)}
    (hst : ∀ x ∈ s, ∀ y ∈ t, hΨ.corootForm x y = 0) {α α' : Module.Dual ℝ V}
    (hα : α ∈ Submodule.span ℝ s) (hα' : α' ∈ Submodule.span ℝ t) :
    hΨ.corootForm α α' = 0 := by
  have h1 : ∀ y ∈ t, α ∈ LinearMap.ker (hΨ.corootBilin.flip y) := by
    intro y hy
    refine (Submodule.span_le.2 ?_) hα
    intro x hx
    exact hst x hx y hy
  have h2 : α' ∈ LinearMap.ker (hΨ.corootBilin α) := by
    refine (Submodule.span_le.2 ?_) hα'
    intro y hy
    exact h1 y hy
  exact h2

/-! ### Orthogonal splittings of the simple affine roots -/

section Split

/-- The span in `V*` of the derivatives of a set of simple affine roots. -/
def simpleDerivativeSpan (T : Set (simpleAffineRoots Ψ (facet Ψ c))) :
    Submodule ℝ (Module.Dual ℝ V) :=
  Submodule.span ℝ ((fun ψ : simpleAffineRoots Ψ (facet Ψ c) =>
    (ψ : A →ᵃ[ℝ] ℝ).linear) '' T)

omit hΨ in
theorem linear_mem_simpleDerivativeSpan {T : Set (simpleAffineRoots Ψ (facet Ψ c))}
    {ψ : simpleAffineRoots Ψ (facet Ψ c)} (hψ : ψ ∈ T) :
    (ψ : A →ᵃ[ℝ] ℝ).linear ∈ simpleDerivativeSpan T :=
  Submodule.subset_span ⟨ψ, hψ, rfl⟩

omit hΨ in
/-- A simple reflection pulls `simpleDerivativeSpan T` back into itself when its root is in
`T` or its coroot is killed by the derivatives of the roots in `T`. -/
theorem comp_reflection_mem_simpleDerivativeSpan {T : Set (simpleAffineRoots Ψ (facet Ψ c))}
    (δ : simpleAffineRoots Ψ (facet Ψ c)) {v : V} (hv : IsCoroot Ψ (δ : A →ᵃ[ℝ] ℝ) v)
    (hδ : δ ∈ T ∨ ∀ ε ∈ T, (ε : A →ᵃ[ℝ] ℝ).linear v = 0) {α : Module.Dual ℝ V}
    (hα : α ∈ simpleDerivativeSpan T) :
    α ∘ₗ ((affineReflection (δ : A →ᵃ[ℝ] ℝ) hv.1).linear : V →ₗ[ℝ] V) ∈
      simpleDerivativeSpan T := by
  rw [comp_affineReflection_linear]
  rcases hδ with hδ | hδ
  · exact Submodule.sub_mem _ hα (Submodule.smul_mem _ _ (linear_mem_simpleDerivativeSpan hδ))
  · have hαv : α v = 0 := by
      have hle : simpleDerivativeSpan T ≤ LinearMap.ker (Module.Dual.eval ℝ V v) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨ε, hε, rfl⟩
        exact hδ ε hε
      exact hle hα
    rw [hαv, zero_smul, sub_zero]
    exact hα

/-- Every element of the affine Weyl group pulls `simpleDerivativeSpan T` back into itself when
the simple roots in `T` and outside `T` are orthogonal. -/
theorem comp_linear_mem_simpleDerivativeSpan (hc : IsRegular Ψ c)
    {T : Set (simpleAffineRoots Ψ (facet Ψ c))}
    (horth : ∀ ψ ∈ T, ∀ η ∉ T, chamberCartanMatrix Ψ (facet Ψ c) ψ η = 0)
    {w : A ≃ᵃ[ℝ] A} (hw : w ∈ affineWeylGroup Ψ) {α : Module.Dual ℝ V}
    (hα : α ∈ simpleDerivativeSpan T) :
    α ∘ₗ (w.linear : V →ₗ[ℝ] V) ∈ simpleDerivativeSpan T := by
  have hgen := (affineReflectionGalleryGeometry V A Ψ
    hΨ.isLocallyFiniteReflectionArrangement c hc).1
  rw [← affineChamberWallComparison V A Ψ hΨ c hc] at hgen
  rw [← hgen] at hw
  have hsimple : ∀ g ∈ (affineWeylGroup Ψ).subtype '' chamberSimpleReflections Ψ (facet Ψ c),
      ∀ α ∈ simpleDerivativeSpan T,
        α ∘ₗ (g.linear : V →ₗ[ℝ] V) ∈ simpleDerivativeSpan T := by
    rintro _ ⟨s, hs, rfl⟩ α hα
    let δ : simpleAffineRoots Ψ (facet Ψ c) :=
      ⟨chamberSimpleRoot ⟨s, hs⟩, chamberSimpleRoot_mem ⟨s, hs⟩⟩
    have hv := isCoroot_chamberSimpleCoroot ⟨s, hs⟩
    have hcoe := coe_eq_affineReflection_chamberSimpleRoot ⟨s, hs⟩
    change α ∘ₗ (((s : A ≃ᵃ[ℝ] A)).linear : V →ₗ[ℝ] V) ∈ _
    rw [show (s : A ≃ᵃ[ℝ] A) = _ from hcoe]
    refine comp_reflection_mem_simpleDerivativeSpan (c := c) δ hv ?_ hα
    by_cases hδ : δ ∈ T
    · exact Or.inl hδ
    · refine Or.inr fun ε hε => ?_
      have h0 := horth ε hε δ hδ
      have hcast := hΨ.cast_chamberCartanMatrix ε δ
      rw [h0, Int.cast_zero, hΨ.corootVector_eq hv] at hcast
      exact hcast.symm
  refine comp_linear_mem_of_mem_closure _ hsimple ?_ hw hα
  rintro _ ⟨s, hs, rfl⟩ α hα
  have hinv : ((affineWeylGroup Ψ).subtype s)⁻¹ = (affineWeylGroup Ψ).subtype s := by
    rw [inv_eq_iff_mul_eq_one]
    obtain ⟨ψ, -, v, hv, hsv⟩ := hs
    change (s : A ≃ᵃ[ℝ] A) * (s : A ≃ᵃ[ℝ] A) = 1
    rw [hsv]
    exact affineReflection_mul_self ψ hv.1
  rw [hinv]
  exact hsimple _ ⟨s, hs, rfl⟩ α hα

/-- An orthogonal splitting of the simple affine roots of a chamber into two nonempty parts
splits the affine root system: it is not irreducible. -/
theorem not_isIrreducibleRoots_of_split (hc : IsRegular Ψ c)
    (T : Set (simpleAffineRoots Ψ (facet Ψ c)))
    (hT : T.Nonempty) (hTc : Tᶜ.Nonempty)
    (horth : ∀ ψ ∈ T, ∀ η ∉ T, chamberCartanMatrix Ψ (facet Ψ c) ψ η = 0) :
    ¬ IsIrreducibleRoots Ψ := by
  intro hirr
  have horth' : ∀ ψ ∈ Tᶜ, ∀ η ∉ Tᶜ, chamberCartanMatrix Ψ (facet Ψ c) ψ η = 0 := by
    intro ψ hψ η hη
    rw [Set.notMem_compl_iff] at hη
    exact (hΨ.chamberCartanMatrix_eq_zero_iff η ψ).1 (horth η hη ψ hψ)
  -- every root has its derivative in one of the two spans
  have hcover : ∀ ψ ∈ Ψ, ψ.linear ∈ simpleDerivativeSpan T ∨
      ψ.linear ∈ simpleDerivativeSpan Tᶜ := by
    intro ψ hψ
    obtain ⟨u, hu⟩ := hΨ.exists_isCoroot ψ hψ
    have hW := affineReflection_mem_affineWeylGroup hψ hu
    obtain ⟨δ, hδ⟩ : ∃ δ : simpleAffineRoots Ψ (facet Ψ c),
        (δ : A →ᵃ[ℝ] ℝ).linear u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hu0 : u = 0 := hΨ.eq_zero_of_forall_simpleAffineRoots_linear_nonneg hc
        fun η hη => (hcon ⟨η, hη⟩).ge
      have h2 := hu.1
      rw [hu0, map_zero] at h2
      norm_num at h2
    have key : ∀ T' : Set (simpleAffineRoots Ψ (facet Ψ c)), δ ∈ T' →
        (∀ ψ ∈ T', ∀ η ∉ T', chamberCartanMatrix Ψ (facet Ψ c) ψ η = 0) →
        ψ.linear ∈ simpleDerivativeSpan T' := by
      intro T' hδT' horthT'
      have h := hΨ.comp_linear_mem_simpleDerivativeSpan hc horthT' hW
        (linear_mem_simpleDerivativeSpan hδT')
      rw [comp_affineReflection_linear] at h
      have h' : (δ : A →ᵃ[ℝ] ℝ).linear u • ψ.linear ∈ simpleDerivativeSpan T' := by
        have := Submodule.sub_mem _ (linear_mem_simpleDerivativeSpan hδT') h
        rwa [sub_sub_cancel] at this
      have := Submodule.smul_mem _ ((δ : A →ᵃ[ℝ] ℝ).linear u)⁻¹ h'
      rwa [smul_smul, inv_mul_cancel₀ hδ, one_smul] at this
    by_cases hδT : δ ∈ T
    · exact Or.inl (key T hδT horth)
    · exact Or.inr (key Tᶜ hδT horth')
  -- the spans are orthogonal for the coroot form
  have hform : ∀ α ∈ simpleDerivativeSpan T, ∀ α' ∈ simpleDerivativeSpan Tᶜ,
      hΨ.corootForm α α' = 0 := by
    intro α hα α' hα'
    refine hΨ.corootForm_eq_zero_of_mem_span ?_ hα hα'
    rintro _ ⟨ψ, hψ, rfl⟩ _ ⟨η, hη, rfl⟩
    exact (hΨ.chamberCartanMatrix_eq_zero_iff_corootForm ψ η).1 (horth ψ hψ η hη)
  let Ψ₁ : Set (A →ᵃ[ℝ] ℝ) := {ψ | ψ ∈ Ψ ∧ ψ.linear ∈ simpleDerivativeSpan T}
  let Ψ₂ : Set (A →ᵃ[ℝ] ℝ) := {ψ | ψ ∈ Ψ ∧ ψ.linear ∈ simpleDerivativeSpan Tᶜ}
  have hunion : Ψ₁ ∪ Ψ₂ = Ψ := by
    ext ψ
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro hψ
      rcases hcover ψ hψ with h | h
      · exact Or.inl ⟨hψ, h⟩
      · exact Or.inr ⟨hψ, h⟩
  have horthΨ : RootsOrthogonal Ψ Ψ₁ Ψ₂ := by
    intro ψ hψ η hη u v hu hv
    have h0 := hform _ hψ.2 _ hη.2
    have hposψ := hΨ.corootForm_self_pos hψ.1
    have hposη := hΨ.corootForm_self_pos hη.1
    have e1 := hΨ.two_mul_corootForm hv ψ.linear
    have e2 := hΨ.two_mul_corootForm hu η.linear
    rw [hΨ.corootForm_comm] at e2
    rw [h0, mul_zero, eq_comm, mul_eq_zero] at e1 e2
    exact ⟨e1.resolve_right hposη.ne', e2.resolve_right hposψ.ne'⟩
  rcases hirr Ψ₁ Ψ₂ hunion horthΨ with h | h
  · obtain ⟨ψ, hψ⟩ := hT
    have hmem : (ψ : A →ᵃ[ℝ] ℝ) ∈ Ψ₁ :=
      ⟨ψ.2.1.1, linear_mem_simpleDerivativeSpan hψ⟩
    rw [h] at hmem
    exact hmem
  · obtain ⟨ψ, hψ⟩ := hTc
    have hmem : (ψ : A →ᵃ[ℝ] ℝ) ∈ Ψ₂ :=
      ⟨ψ.2.1.1, linear_mem_simpleDerivativeSpan hψ⟩
    rw [h] at hmem
    exact hmem

end Split

/-! ### The left kernel of the Cartan matrix -/

section Kernel

variable [Fintype (simpleAffineRoots Ψ (facet Ψ c))]

/-- The support of a nonnegative real left-kernel vector of the Cartan matrix is orthogonal to
its complement. -/
theorem chamberCartanMatrix_eq_zero_of_nonneg_leftKernel (hc : IsRegular Ψ c)
    {y : simpleAffineRoots Ψ (facet Ψ c) → ℝ} (hy0 : ∀ ψ, 0 ≤ y ψ)
    (hy : ∀ η : simpleAffineRoots Ψ (facet Ψ c),
      ∑ ψ, y ψ * (ψ : A →ᵃ[ℝ] ℝ).linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ)) = 0)
    {ψ η : simpleAffineRoots Ψ (facet Ψ c)} (hψ : y ψ ≠ 0) (hη : y η = 0) :
    chamberCartanMatrix Ψ (facet Ψ c) ψ η = 0 := by
  classical
  have hnonpos : ∀ θ ∈ (Finset.univ : Finset (simpleAffineRoots Ψ (facet Ψ c))),
      y θ * (θ : A →ᵃ[ℝ] ℝ).linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ)) ≤ 0 := by
    intro θ _
    by_cases hθ : θ = η
    · rw [hθ, hη, zero_mul]
    · rw [← hΨ.cast_chamberCartanMatrix]
      exact mul_nonpos_of_nonneg_of_nonpos (hy0 θ)
        (by exact_mod_cast hΨ.chamberCartanMatrix_nonpos hc hθ)
  have hall := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).1 (hy η) ψ (Finset.mem_univ _)
  rw [← hΨ.cast_chamberCartanMatrix, mul_eq_zero] at hall
  exact_mod_cast hall.resolve_left hψ

/-- For an irreducible root system, every real left-kernel vector of the Cartan matrix of a
chamber is a multiple of any strictly positive one. -/
theorem exists_eq_smul_of_leftKernel (hc : IsRegular Ψ c) (hirr : IsIrreducibleRoots Ψ)
    {m : simpleAffineRoots Ψ (facet Ψ c) → ℝ} (hm0 : ∀ ψ, 0 < m ψ)
    (hm : ∀ η : simpleAffineRoots Ψ (facet Ψ c),
      ∑ ψ, m ψ * (ψ : A →ᵃ[ℝ] ℝ).linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ)) = 0)
    {y : simpleAffineRoots Ψ (facet Ψ c) → ℝ}
    (hy : ∀ η : simpleAffineRoots Ψ (facet Ψ c),
      ∑ ψ, y ψ * (ψ : A →ᵃ[ℝ] ℝ).linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ)) = 0) :
    ∃ t : ℝ, y = t • m := by
  classical
  by_cases hempty : IsEmpty (simpleAffineRoots Ψ (facet Ψ c))
  · exact ⟨0, funext fun ψ => (hempty.false ψ).elim⟩
  obtain ⟨ψ₀⟩ := not_isEmpty_iff.1 hempty
  set t := y ψ₀ / m ψ₀
  refine ⟨t, ?_⟩
  let z : simpleAffineRoots Ψ (facet Ψ c) → ℝ := fun ψ => y ψ - t * m ψ
  have hz : ∀ η : simpleAffineRoots Ψ (facet Ψ c),
      ∑ ψ, z ψ * (ψ : A →ᵃ[ℝ] ℝ).linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ)) = 0 := by
    intro η
    simp only [z, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hy η, hm η,
      mul_zero, sub_zero]
  have hzψ₀ : z ψ₀ = 0 := by
    simp only [z, t]
    rw [div_mul_cancel₀ _ (hm0 ψ₀).ne', sub_self]
  have habs := hΨ.abs_mem_leftKernel hc z hz
  have hz0 : ∀ ψ, z ψ = 0 := by
    by_contra hcon
    push Not at hcon
    let T : Set (simpleAffineRoots Ψ (facet Ψ c)) := {ψ | z ψ ≠ 0}
    refine hΨ.not_isIrreducibleRoots_of_split hc T hcon ⟨ψ₀, fun h => h hzψ₀⟩ ?_ hirr
    intro ψ hψ η hη
    refine hΨ.chamberCartanMatrix_eq_zero_of_nonneg_leftKernel hc (y := fun ψ => |z ψ|)
      (fun ψ => abs_nonneg _) habs ?_ ?_
    · exact abs_ne_zero.2 hψ
    · have : z η = 0 := by
        by_contra h
        exact hη h
      simp [this]
  funext ψ
  have := hz0 ψ
  simp only [z, sub_eq_zero] at this
  simp [this]

end Kernel

/-! ### Linear independence -/

/-- KP Proposition 1.3.22(5): the simple affine roots of a chamber of an irreducible affine root
system are linearly independent affine functionals. -/
theorem linearIndependent_simpleAffineRoots (hirr : IsIrreducibleRoots Ψ) (hc : IsRegular Ψ c) :
    LinearIndependent ℝ
      (fun ψ : simpleAffineRoots Ψ (facet Ψ c) => (ψ : A →ᵃ[ℝ] ℝ)) := by
  classical
  have : Fintype (simpleAffineRoots Ψ (facet Ψ c)) :=
    (finite_simpleAffineRoots hΨ hc).fintype
  rw [Fintype.linearIndependent_iff]
  intro b hb ψ₀
  obtain ⟨m, hm0, hm⟩ := hΨ.exists_pos_vecMul_chamberCartanMatrix_eq_zero hc
  have hmR : ∀ η : simpleAffineRoots Ψ (facet Ψ c),
      ∑ ψ, (m ψ : ℝ) * (ψ : A →ᵃ[ℝ] ℝ).linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ)) = 0 := by
    intro η
    have hη := congrFun hm η
    simp only [vecMul, dotProduct, Pi.zero_apply] at hη
    have hR : ((∑ ψ, m ψ * chamberCartanMatrix Ψ (facet Ψ c) ψ η : ℤ) : ℝ) = 0 := by
      rw [hη, Int.cast_zero]
    push_cast at hR
    simpa only [hΨ.cast_chamberCartanMatrix] using hR
  have hlin : ∑ ψ, b ψ • (ψ : A →ᵃ[ℝ] ℝ).linear = 0 := by
    have := congrArg (derivativeMap : (A →ᵃ[ℝ] ℝ) →ₗ[ℝ] Module.Dual ℝ V) hb
    rw [map_sum, map_zero] at this
    simp only [map_smul] at this
    exact this
  have hbL : ∀ η : simpleAffineRoots Ψ (facet Ψ c),
      ∑ ψ, b ψ * (ψ : A →ᵃ[ℝ] ℝ).linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ)) = 0 := by
    intro η
    have := LinearMap.congr_fun hlin (corootVector Ψ (η : A →ᵃ[ℝ] ℝ))
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply] using this
  obtain ⟨t, ht⟩ := hΨ.exists_eq_smul_of_leftKernel hc hirr
    (m := fun ψ => (m ψ : ℝ)) (fun ψ => by exact_mod_cast hm0 ψ) hmR hbL
  have hval : ∑ ψ, b ψ * (ψ : A →ᵃ[ℝ] ℝ) c = 0 := by
    let ev : (A →ᵃ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun f => f c
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have := congrArg ev hb
    rw [map_sum, map_zero] at this
    simp only [map_smul, smul_eq_mul] at this
    exact this
  have hpos : 0 < ∑ ψ, (m ψ : ℝ) * (ψ : A →ᵃ[ℝ] ℝ) c := by
    refine Finset.sum_pos (fun ψ _ => mul_pos (by exact_mod_cast hm0 ψ)
      (pos_of_mem_simpleAffineRoots ψ.2 (mem_facet_self Ψ c))) ⟨ψ₀, Finset.mem_univ _⟩
  have ht0 : t = 0 := by
    have : t * ∑ ψ, (m ψ : ℝ) * (ψ : A →ᵃ[ℝ] ℝ) c = 0 := by
      rw [Finset.mul_sum, ← hval]
      refine Finset.sum_congr rfl fun ψ _ => ?_
      rw [ht, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact (mul_eq_zero.1 this).resolve_right hpos.ne'
  rw [ht, ht0, zero_smul, Pi.zero_apply]

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
