import Langlands.AlgebraicGeometry.Modules.NoetherianVanishing.Induction
import Langlands.AlgebraicGeometry.Modules.ModuleSupport

/-!
# Closed support bounds for scheme modules

The support bound uses actual vanishing on the complement of a closed set and the heights
of its irreducible closed subsets. It packages the hypothesis of the published
support-dimension cohomology vanishing theorem.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order

namespace Langlands.AlgebraicGeometry.Modules

variable {X : Scheme.{u}}

/-- A closed set off which `M` vanishes has all irreducible closed heights less than `e`.
For a nonzero module the usual support-dimension upper bound `d` corresponds to `e = d + 1`.
-/
def HasSupportDimensionLT (M : X.Modules) (e : ℕ) : Prop :=
  ∃ Z : Closeds X, QuasicoherentLocal.VanishesOn M Z.compl ∧
    ∀ T : IrreducibleCloseds X, (T : Set X) ⊆ Z → height T < e

namespace QuasicoherentLocal.VanishesOn

/-- Vanishing on an open excludes every point of that open from the actual stalk support. -/
theorem stalkSupport_subset_compl {M : X.Modules} {O : X.Opens}
    (h : QuasicoherentLocal.VanishesOn M O) : stalkSupport M ⊆ (O : Set X)ᶜ := by
  intro x hx hxO
  have hz := (isZero_iff_forall_isZero_stalk.mp h.isZero_restrict) ⟨x, hxO⟩
  exact hx (hz.of_iso ((Scheme.Modules.restrictStalkNatIso O.ι ⟨x, hxO⟩).app M).symm)

end QuasicoherentLocal.VanishesOn

namespace HasSupportDimensionLT

open QuasicoherentLocal

variable {M N : X.Modules} {e e' : ℕ}

/-- An isomorphism preserves a closed support bound. -/
theorem of_iso (h : HasSupportDimensionLT M e) (i : M ≅ N) :
    HasSupportDimensionLT N e := by
  obtain ⟨Z, hM, hZ⟩ := h
  exact ⟨Z, hM.of_iso i, hZ⟩

/-- Increasing the bound preserves the property. -/
theorem mono (h : HasSupportDimensionLT M e) (he : e ≤ e') :
    HasSupportDimensionLT M e' := by
  obtain ⟨Z, hM, hZ⟩ := h
  exact ⟨Z, hM, fun T hT => (hZ T hT).trans_le (by exact_mod_cast he)⟩

/-- A kernel inherits the support bound of the source. -/
theorem kernel (h : HasSupportDimensionLT M e) (φ : M ⟶ N) :
    HasSupportDimensionLT (Limits.kernel φ) e := by
  obtain ⟨Z, hM, hZ⟩ := h
  exact ⟨Z, hM.kernel φ, hZ⟩

/-- A cokernel inherits the support bound of the target. -/
theorem cokernel (h : HasSupportDimensionLT N e) (φ : M ⟶ N) :
    HasSupportDimensionLT (Limits.cokernel φ) e := by
  obtain ⟨Z, hN, hZ⟩ := h
  exact ⟨Z, VanishesOn.cokernel_of_right φ hN, hZ⟩

/-- A zero module has every closed support bound. -/
theorem of_isZero (h : IsZero M) (e : ℕ) : HasSupportDimensionLT M e := by
  refine ⟨⊥, ?_, ?_⟩
  · intro W _ s
    exact congrArg (fun g : M ⟶ M => g.app W s) (h.eq_of_src (𝟙 M) 0)
  · intro T hT
    obtain ⟨x, hx⟩ := T.isIrreducible.nonempty
    exact (hT hx).elim

/-- Bound zero forces the module to be zero. -/
theorem isZero (h : HasSupportDimensionLT M 0) : IsZero M := by
  obtain ⟨Z, hM, hZ⟩ := h
  have hZe : (Z : Set X) = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
    have := hZ ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
      (closure_minimal (Set.singleton_subset_iff.2 hx) Z.isClosed)
    simp at this
  exact NoetherianVanishing.isZero_of_vanishesOn_top
    (hM.mono (fun x _ hx => by simp only [hZe, Set.mem_empty_iff_false] at hx))

/-- A global topological dimension bound bounds the support of every module. -/
theorem of_topologicalKrullDim_le {d : ℕ} (hX : topologicalKrullDim X ≤ d)
    (M : X.Modules) : HasSupportDimensionLT M (d + 1) := by
  refine ⟨⊤, ?_, fun T _ => ?_⟩
  · apply (NoetherianVanishing.VanishesOn.bot M).mono
    intro x hx
    exact (hx (show x ∈ (⊤ : Closeds X) from Set.mem_univ x)).elim
  ·
    simpa only [Nat.cast_add, Nat.cast_one] using
      (ENat.lt_add_one_iff (ENat.natCast_ne_top d)).2
        (NoetherianVanishing.height_le_of_topologicalKrullDim_le hX T)

/-- Cohomology vanishes in degrees at least the support-height bound. -/
theorem isZero_relativeCohomology [IsNoetherian X] [X.IsSeparated]
    {R : CommRingCat.{u}} (f : X ⟶ Spec R) (h : HasSupportDimensionLT M e)
    (hM : IsAffineLocallyQuasicoherent M) (n : ℕ) (hn : e ≤ n) :
    IsZero ((DerivedSections.relativeCohomology f n).obj M) := by
  obtain ⟨Z, hMZ, hZ⟩ := h
  exact NoetherianVanishing.isZero_relativeCohomology_of_height f e Z M hM hMZ hZ n hn

end HasSupportDimensionLT

/-- Bound zero is equivalent to vanishing of the module. -/
theorem hasSupportDimensionLT_zero_iff (M : X.Modules) :
    HasSupportDimensionLT M 0 ↔ IsZero M :=
  ⟨HasSupportDimensionLT.isZero, fun h => HasSupportDimensionLT.of_isZero h 0⟩

namespace NoetherianVanishing

variable {A : Type*} [TopologicalSpace A]

/-- An irreducible closed subset of height zero in a T0 space is a singleton. -/
theorem exists_singleton_of_height_lt_one [T0Space A] (T : IrreducibleCloseds A)
    (hT : height T < 1) : ∃ x : A, (T : Set A) = {x} := by
  have h0 : height T = 0 := le_antisymm
    ((ENat.lt_add_one_iff (ENat.natCast_ne_top 0)).1 (by simpa using hT)) bot_le
  have hmin : IsMin T := height_eq_zero.1 h0
  have hcl : ∀ x ∈ T, closure ({x} : Set A) = (T : Set A) := by
    intro x hx
    let C : IrreducibleCloseds A :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hCT : C ≤ T := closure_minimal (Set.singleton_subset_iff.2 hx) T.isClosed
    exact congrArg (fun S : IrreducibleCloseds A => (S : Set A)) (hmin.eq_of_le hCT)
  obtain ⟨x, hx⟩ := T.isIrreducible.nonempty
  refine ⟨x, Set.Subset.antisymm (fun y hy => ?_) (Set.singleton_subset_iff.2 hx)⟩
  exact Set.mem_singleton_iff.2 (inseparable_iff_closure_eq.2 ((hcl y hy).trans (hcl x hx).symm)).eq

/-- A closed set in a noetherian T0 space with irreducible heights less than one is a finite
set of closed points. -/
theorem finite_and_closedPoints_of_height_lt_one [NoetherianSpace A] [T0Space A]
    (Z : Closeds A)
    (hZ : ∀ T : IrreducibleCloseds A, (T : Set A) ⊆ Z → height T < 1) :
    (Z : Set A).Finite ∧ ∀ x ∈ Z, IsClosed ({x} : Set A) := by
  classical
  obtain ⟨S, hSf, hSc, hSi, hZS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible Z.isClosed
  have hsing : ∀ T ∈ S, ∃ x : A, T = {x} := by
    intro T hT
    let T' : IrreducibleCloseds A := ⟨T, hSi T hT, hSc T hT⟩
    apply exists_singleton_of_height_lt_one T'
    apply hZ T'
    intro x hx
    rw [hZS]
    exact Set.mem_sUnion.2 ⟨T, hT, hx⟩
  constructor
  · rw [hZS]
    apply hSf.sUnion
    intro T hT
    obtain ⟨x, rfl⟩ := hsing T hT
    exact Set.finite_singleton x
  · intro x hx
    change x ∈ (Z : Set A) at hx
    rw [hZS] at hx
    obtain ⟨T, hT, hx⟩ := Set.mem_sUnion.1 hx
    obtain ⟨y, hy⟩ := hsing T hT
    have hxy : x = y := Set.mem_singleton_iff.1 (hy ▸ hx)
    simpa only [hy, hxy] using hSc T hT

end NoetherianVanishing

/-- Support dimension at most zero gives finite closed stalk support on a noetherian scheme.
No quasi-coherence or finite-generation hypothesis is needed. -/
theorem HasSupportDimensionLT.hasFiniteClosedSupport [IsNoetherian X]
    {M : X.Modules} (h : HasSupportDimensionLT M 1) : HasFiniteClosedSupport M := by
  obtain ⟨Z, hM, hZ⟩ := h
  obtain ⟨hfin, hcl⟩ := NoetherianVanishing.finite_and_closedPoints_of_height_lt_one Z
    (by simpa only [Nat.cast_one] using hZ)
  exact HasFiniteClosedSupport.of_subset hfin hcl (by
    simpa only [Closeds.coe_compl, compl_compl] using hM.stalkSupport_subset_compl)

end Langlands.AlgebraicGeometry.Modules
