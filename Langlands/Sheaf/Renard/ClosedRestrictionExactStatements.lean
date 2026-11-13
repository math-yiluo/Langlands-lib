import Langlands.Sheaf.Renard.VectorSheafScalars
import Langlands.Sheaf.CompactSupport
import Langlands.Topology.LocallyProfinite

/-!
# Compact sections over an open subset and its closed complement (Renard II.2.5, Proposition)

For a sheaf `F` of complex vector spaces on a t.d. space `X`, an open `U` and `Z = X ∖ U`,
the sequence `0 → F_c(U) → F_c(X) → F_c(Z) → 0` (extension by zero, restriction) is exact, and
so is its dual `0 → F_c(Z)* → F_c(X)* → F_c(U)* → 0`.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Langlands.Sheaf.Renard.ClosedRestriction

open VectorSheafScalars

variable {X : Type} [TopologicalSpace X]

/-- `F_c(U) = (F|_U)_c(U)`: the compactly supported global sections of the restriction of `F`
to the open subspace `U` (Mathlib's restriction along the open embedding of `U`). -/
abbrev openCompactSections (F : VectorSheaf X) (U : Opens (TopCat.of X)) :
    Submodule ℂ ((U.isOpenEmbedding.functor.op ⋙ F.presheaf).obj (op ⊤)) :=
  CompactSupport.submodule (U.isOpenEmbedding.functor.op ⋙ F.presheaf)

/-- Renard's sections of the restriction `F|_Z` over a subset `Z`: families of germs
`z ↦ t(z) ∈ F_z` that agree, near each point of `Z`, with the germs of a section of `F`. -/
def IsLocalRestriction (F : VectorSheaf X) (Z : Set X)
    (t : ∀ z : Z, F.presheaf.stalk (z : X)) : Prop :=
  ∀ z : Z, ∃ (V : Opens (TopCat.of X)) (_hz : (z : X) ∈ V) (σ : F.presheaf.obj (op V)),
    ∀ (y : Z) (hy : (y : X) ∈ V), F.presheaf.germ V y hy σ = t y

/-- The support of a section of `F|_Z` over `Z` is closed in `Z`. -/
theorem isClosed_support_of_isLocalRestriction (F : VectorSheaf X) (Z : Set X)
    (t : ∀ z : Z, F.presheaf.stalk (z : X)) (ht : IsLocalRestriction F Z t) :
    IsClosed {z : Z | t z ≠ 0} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  have hz0 : t z = 0 := by simpa using hz
  obtain ⟨V, hzV, σ, hσ⟩ := ht z
  have h0 : F.presheaf.germ V z hzV σ = F.presheaf.germ V z hzV 0 := by
    rw [hσ z hzV, hz0, map_zero]
  obtain ⟨W, hzW, iU, iV, hW⟩ := F.presheaf.germ_eq (z : X) hzV hzV σ 0 h0
  have hW0 : F.presheaf.map iU.op σ = 0 := by rw [hW, map_zero]
  have hnhds : (Subtype.val : Z → X) ⁻¹' (W : Set X) ∈ nhds z :=
    (W.isOpen.preimage continuous_subtype_val).mem_nhds hzW
  apply Filter.mem_of_superset hnhds
  intro y hy
  change ¬ t y ≠ 0
  apply not_not.mpr
  rw [← hσ y (iU.le hy), ← F.presheaf.germ_res_apply iU (y : X) hy σ, hW0, map_zero]

/-- `F_c(Z) = (F|_Z)_c(Z)`: sections of `F|_Z` over `Z` with compact support. -/
def closedCompactSections (F : VectorSheaf X) (Z : Set X) :
    Submodule ℂ (∀ z : Z, F.presheaf.stalk (z : X)) where
  carrier := {t | IsLocalRestriction F Z t ∧ IsCompact {z : Z | t z ≠ 0}}
  zero_mem' := by
    refine ⟨fun z => ⟨⊤, trivial, 0, fun y hy => by simp⟩, ?_⟩
    simp
  add_mem' := by
    rintro t t' ⟨ht, hct⟩ ⟨ht', hct'⟩
    have hloc : IsLocalRestriction F Z (t + t') := by
      intro z
      obtain ⟨V, hzV, σ, hσ⟩ := ht z
      obtain ⟨V', hzV', σ', hσ'⟩ := ht' z
      refine ⟨V ⊓ V', ⟨hzV, hzV'⟩,
        F.presheaf.map (homOfLE inf_le_left).op σ +
          F.presheaf.map (homOfLE inf_le_right).op σ', fun y hy => ?_⟩
      rw [map_add, F.presheaf.germ_res_apply, F.presheaf.germ_res_apply, hσ, hσ']
      rfl
    refine ⟨hloc, (hct.union hct').of_isClosed_subset
      (isClosed_support_of_isLocalRestriction F Z _ hloc) ?_⟩
    intro z hz
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hz (by simp [h.1, h.2])
  smul_mem' := by
    rintro c t ⟨ht, hct⟩
    have hloc : IsLocalRestriction F Z (c • t) := by
      intro z
      obtain ⟨V, hzV, σ, hσ⟩ := ht z
      exact ⟨V, hzV, c • σ, fun y hy => by rw [map_smul, hσ]; rfl⟩
    refine ⟨hloc, hct.of_isClosed_subset
      (isClosed_support_of_isLocalRestriction F Z _ hloc) ?_⟩
    intro z hz
    by_contra h
    simp only [Set.mem_ofPred_eq, not_not] at h
    exact hz (by simp [h])

/-- `p_Z : F_c(X) → F_c(Z)`: restriction of a compactly supported global section to a closed
subset `Z`, `φ ↦ (z ↦ φ_z)`. -/
def restrictToClosed (F : VectorSheaf X) (Z : Set X) (hZ : IsClosed Z) :
    CompactSupport.submodule F.presheaf →ₗ[ℂ] closedCompactSections F Z where
  toFun φ := ⟨fun z => F.presheaf.Γgerm (z : X) φ.1,
    ⟨fun _ => ⟨⊤, trivial, φ.1, fun _ _ => rfl⟩,
      Topology.IsInducing.subtypeVal.isCompact_preimage (by simpa using hZ) φ.2⟩⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext z
    simp
  map_smul' c φ := by
    apply Subtype.ext
    funext z
    simp

/-- `φ = i_U(s)`: the global section `φ` restricts to `s` on `U` and has zero germs off `U`. -/
def IsZeroExtension (F : VectorSheaf X) (U : Opens (TopCat.of X))
    (s : (U.isOpenEmbedding.functor.op ⋙ F.presheaf).obj (op ⊤))
    (φ : F.presheaf.obj (op ⊤)) : Prop :=
  F.presheaf.map (homOfLE (le_top : U.isOpenEmbedding.functor.obj ⊤ ≤ ⊤)).op φ = s ∧
    ∀ x : X, x ∉ U → F.presheaf.Γgerm x φ = 0

/-- Renard II.2.5, Proposition: for a sheaf `F` of complex vector spaces on a t.d. space `X`,
an open `U` and its closed complement `Z = X ∖ U`, the sequence
`0 → F_c(U) → F_c(X) → F_c(Z) → 0` of extension by zero `i_U` and restriction `p_Z` is exact,
and so is the dual sequence `0 → F_c(Z)* → F_c(X)* → F_c(U)* → 0`.

The clauses: (1) `i_U` is well defined: every `s ∈ F_c(U)` has a unique extension by zero,
and it lies in `F_c(X)`; (2) a compactly supported section with `p_Z φ = 0` is `i_U(s)` for some
`s ∈ F_c(U)`; (3) `p_Z` is surjective; (4) its transpose is injective; (5) a linear form on
`F_c(X)` vanishing on the image of `i_U` is in the image of the transpose of `p_Z`; (6) every
linear form on `F_c(U)` is `l ∘ i_U` for a linear form `l` on `F_c(X)`. -/
def ClosedRestrictionExactStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X], Langlands.Topology.IsLocallyProfinite X →
    ∀ (F : VectorSheaf X) (U : Opens (TopCat.of X)),
      let pZ := restrictToClosed F ((U : Set X)ᶜ) U.isOpen.isClosed_compl
      (∀ s ∈ openCompactSections F U, ∃ φ ∈ CompactSupport.submodule F.presheaf,
          IsZeroExtension F U s φ ∧ ∀ ψ, IsZeroExtension F U s ψ → ψ = φ) ∧
      (∀ φ : CompactSupport.submodule F.presheaf, pZ φ = 0 →
          ∃ s ∈ openCompactSections F U, IsZeroExtension F U s φ) ∧
      Function.Surjective pZ ∧
      Function.Injective pZ.dualMap ∧
      (∀ l : Module.Dual ℂ (CompactSupport.submodule F.presheaf),
          (∀ (s : openCompactSections F U) (φ : CompactSupport.submodule F.presheaf),
            IsZeroExtension F U s φ → l φ = 0) →
          l ∈ LinearMap.range pZ.dualMap) ∧
      ∀ m : Module.Dual ℂ (openCompactSections F U),
        ∃ l : Module.Dual ℂ (CompactSupport.submodule F.presheaf),
          ∀ (s : openCompactSections F U) (φ : CompactSupport.submodule F.presheaf),
            IsZeroExtension F U s φ → l φ = m s

end Langlands.Sheaf.Renard.ClosedRestriction
