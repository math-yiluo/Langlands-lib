import Langlands.Shimura.Coefficients.LatticeTopologyStatement

noncomputable section

universe u v w z

namespace Langlands.Shimura.Coefficients

open Set

private theorem compact_span_sup_fg
    {R : Type u} [CommRing R] {V : Type w} [AddCommGroup V] [Module R V]
    [TopologicalSpace V] [IsTopologicalAddGroup V]
    (Λ : Submodule R V) (hfg : Λ.FG) (hop : IsOpen (Λ : Set V))
    (S : Set V) (hS : IsCompact S) : (Λ ⊔ Submodule.span R S).FG := by
  classical
  let U : S → Set V := fun x => {y | y - x.val ∈ Λ}
  have hU : ∀ x, IsOpen (U x) := fun x => hop.preimage (continuous_id.sub continuous_const)
  have hcover : S ⊆ ⋃ x, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simp [U]⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover U hU hcover
  have heq : Λ ⊔ Submodule.span R S =
      Λ ⊔ Submodule.span R (Subtype.val '' (t : Set S)) := by
    apply le_antisymm
    · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
      intro x hx
      obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
      have hdiff : x - y.val ∈ Λ ⊔ Submodule.span R (Subtype.val '' (t : Set S)) :=
        Submodule.mem_sup_left hxy
      have hy : y.val ∈ Λ ⊔ Submodule.span R (Subtype.val '' (t : Set S)) :=
        Submodule.mem_sup_right (Submodule.subset_span ⟨y, hyt, rfl⟩)
      simpa using (Λ ⊔ Submodule.span R (Subtype.val '' (t : Set S))).add_mem hdiff hy
    · exact sup_le_sup_left (Submodule.span_mono (by rintro _ ⟨x, hx, rfl⟩; exact x.property)) _
  rw [heq]
  exact hfg.sup (Submodule.fg_span (t.finite_toSet.image Subtype.val))

private theorem compact_orbitSpan_fg
    {R : Type u} [CommRing R] {K : Type v} [CommRing K] [Algebra R K]
    {V : Type w} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [TopologicalSpace V] [IsTopologicalAddGroup V]
    {G : Type z} [Group G] [TopologicalSpace G] [CompactSpace G]
    (ρ : G →* (V ≃ₗ[K] V)) (hρ : ∀ x : V, Continuous (fun g : G => ρ g x))
    (Λ : Submodule R V) (hfg : Λ.FG) (hop : IsOpen (Λ : Set V)) :
    (orbitSpan ρ Λ).FG := by
  classical
  obtain ⟨s, hs⟩ := hfg
  let S : Set V := ⋃ x ∈ s, Set.range (fun g : G => ρ g x)
  have hS : IsCompact S := s.isCompact_biUnion fun x hx => isCompact_range (hρ x)
  have heq : orbitSpan ρ Λ = Λ ⊔ Submodule.span R S := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨g, y, hy, rfl⟩
      rw [← hs] at hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        apply Submodule.mem_sup_right
        exact Submodule.subset_span (mem_iUnion₂.mpr ⟨x, hx, ⟨g, rfl⟩⟩)
      | zero => simp
      | add x y hx hy hxx hyy => simpa using (Λ ⊔ Submodule.span R S).add_mem hxx hyy
      | smul r x hx hxx =>
        change (ρ g).restrictScalars R (r • x) ∈ Λ ⊔ Submodule.span R S
        simpa using (Λ ⊔ Submodule.span R S).smul_mem r hxx
    · refine sup_le (le_orbitSpan ρ Λ) (Submodule.span_le.mpr ?_)
      intro x hx
      obtain ⟨y, hy, g, rfl⟩ := mem_iUnion₂.mp hx
      apply Submodule.subset_span
      exact ⟨g, y, hs ▸ Submodule.subset_span hy, rfl⟩
  rw [heq]
  exact compact_span_sup_fg Λ ⟨s, hs⟩ hop S hS

/-- Compact orbit saturation preserves open full lattices. -/
theorem compactLattice : CompactLatticeStatement.{u,v,w,z} := by
  intro R _ K _ _ V _ _ _ _ _ _ G _ _ _ ρ hρ Λ _ hop
  refine ⟨orbitSpan_isLattice ρ Λ (compact_orbitSpan_fg ρ hρ Λ Submodule.IsLattice.fg hop),
    orbitSpan_stable ρ Λ, ?_⟩
  exact AddSubgroup.isOpen_mono (H₁ := Λ.toAddSubgroup)
    (H₂ := (orbitSpan ρ Λ).toAddSubgroup) (le_orbitSpan ρ Λ) hop

private theorem congruenceKernel_isOpen
    {R : Type u} [CommRing R] {G : Type z} [Group G] [TopologicalSpace G]
    (M : Action (ModuleCat.{w} R) G) [Module.Finite R M.V]
    [TopologicalSpace M.V] [IsTopologicalAddGroup M.V]
    (hρ : ∀ x : M.V, Continuous (fun g : G => (M.ρ g).hom x))
    (I : Ideal R) (n : ℕ)
    (hop : IsOpen ((I ^ n • ⊤ : Submodule R M.V) : Set M.V)) :
    IsOpen (congruenceKernel I M n : Set G) := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R M.V).FG)
  have heq : (congruenceKernel I M n : Set G) =
      ⋂ x ∈ s, {g | (M.ρ g).hom x - x ∈ (I ^ n • ⊤ : Submodule R M.V)} := by
    ext g
    change g ∈ congruenceKernel I M n ↔ _
    rw [mem_congruenceKernel]
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h x hx
      exact (Submodule.Quotient.eq _).mp (h x)
    · intro h x
      have he : (Submodule.mkQ (I ^ n • ⊤)).comp (M.ρ g).hom =
          (Submodule.mkQ (I ^ n • ⊤) : M.V →ₗ[R] (torsionAction I M n).V) := by
        apply LinearMap.ext_on hs
        intro y hy
        exact (Submodule.Quotient.eq _).mpr (h y hy)
      exact DFunLike.congr_fun he x
  rw [heq]
  exact isOpen_biInter_finset fun x hx => hop.preimage ((hρ x).sub continuous_const)

/-- Congruence kernels are open and the corresponding compact-group quotients are finite. -/
theorem congruenceKernelTopology : CongruenceKernelTopologyStatement.{u,z,w} := by
  intro R _ G _ _ _ _ M _ _ _ hρ I n hop
  have hopen := congruenceKernel_isOpen M hρ I n hop
  exact ⟨hopen, (congruenceKernel I M n).quotient_finite_of_isOpen hopen⟩

/-- The topological stable-lattice and finite congruence-quotient prerequisites. -/
theorem latticeTopology : LatticeTopologyStatement.{u,v,w,z} :=
  ⟨compactLattice, congruenceKernelTopology⟩

end Langlands.Shimura.Coefficients
