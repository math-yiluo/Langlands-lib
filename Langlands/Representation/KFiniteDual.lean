import Langlands.Representation.CompactFiniteSemisimplicity
import Langlands.Representation.CompactCoefficient.IsotypicSemisimplicityProof
import Langlands.Representation.IsotypicRestriction
import Langlands.Representation.Archimedean.GKModule
import Langlands.Algebra.CanonicalReynolds
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# The `K`-finite dual of an admissible representation of a compact group

For a compact group `K` and a complex representation `ρ` in which every vector is `K`-finite
with continuous coefficients, `ρ` is semisimple over the group algebra.  Its isotypic
components are finite-dimensional when `ρ` is admissible.  This file builds the projections
onto these blocks and studies the `K`-finite algebraic dual.
-/

noncomputable section

open scoped MonoidAlgebra Matrix

set_option autoImplicit false

namespace Langlands.KFiniteDual

universe uK uV

open MeasureTheory

section Blocks

/-! ### Projections onto isotypic components of a semisimple module -/

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
  [IsSemisimpleModule R M]

theorem isCompl_isotypicComponent (c : isotypicComponents R M) :
    IsCompl c.1 (sSup (isotypicComponents R M \ {c.1})) := by
  refine ⟨sSupIndep_isotypicComponents R M c.2, ?_⟩
  rw [codisjoint_iff, ← sSup_insert, Set.insert_sdiff_singleton,
    Set.insert_eq_of_mem c.2, sSup_isotypicComponents]

/-- The projection onto an isotypic component along the sum of the other components. -/
def blockProj (c : isotypicComponents R M) : M →ₗ[R] M :=
  c.1.projection _ (isCompl_isotypicComponent c)

theorem blockProj_mem (c : isotypicComponents R M) (m : M) : blockProj c m ∈ c.1 :=
  Submodule.projection_apply_mem _ m

theorem blockProj_of_mem (c : isotypicComponents R M) {m : M} (hm : m ∈ c.1) :
    blockProj c m = m :=
  Submodule.projection_apply_of_mem_left _ hm

theorem blockProj_of_mem_sSup_other (c : isotypicComponents R M) {m : M}
    (hm : m ∈ sSup (isotypicComponents R M \ {c.1})) : blockProj c m = 0 :=
  Submodule.projection_apply_of_mem_right _ hm

theorem blockProj_of_mem_other (c c' : isotypicComponents R M) (h : c' ≠ c) {m : M}
    (hm : m ∈ c'.1) : blockProj c m = 0 := by
  have hle : c'.1 ≤ sSup (isotypicComponents R M \ {c.1}) :=
    le_sSup ⟨c'.2, fun h' => h (Subtype.ext h')⟩
  exact blockProj_of_mem_sSup_other c (hle hm)

omit [IsSemisimpleModule R M] in
theorem isFullyInvariant_sSup_other (c : isotypicComponents R M) :
    (sSup (isotypicComponents R M \ {c.1})).IsFullyInvariant :=
  fun f => sSup_le fun _ hN =>
    (Submodule.IsFullyInvariant.of_mem_isotypicComponents hN.1 f).trans
      (Submodule.comap_mono (le_sSup hN))

/-- Block projections commute with every module endomorphism. -/
theorem blockProj_comm (c : isotypicComponents R M) (f : Module.End R M) (m : M) :
    blockProj c (f m) = f (blockProj c m) := by
  have hc := isCompl_isotypicComponent c
  obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a ∈ c.1, ∃ b ∈ sSup (isotypicComponents R M \ {c.1}),
      a + b = m := by
    obtain ⟨⟨a, b⟩, h⟩ := (Submodule.prodEquivOfIsCompl _ _ hc).surjective m
    exact ⟨a, a.2, b, b.2, h⟩
  have hfa : f a ∈ c.1 := Submodule.IsFullyInvariant.of_mem_isotypicComponents c.2 f ha
  have hfb : f b ∈ sSup (isotypicComponents R M \ {c.1}) := isFullyInvariant_sSup_other c f hb
  rw [map_add, map_add, map_add, blockProj_of_mem c hfa, blockProj_of_mem_sSup_other c hfb,
    blockProj_of_mem c ha, blockProj_of_mem_sSup_other c hb]
  simp

/-- Block projections preserve every submodule. -/
theorem blockProj_mem_of_mem (c : isotypicComponents R M) (N : Submodule R M) {m : M}
    (hm : m ∈ N) : blockProj c m ∈ N := by
  obtain ⟨N', hN⟩ := exists_isCompl N
  let q : Module.End R M := N.projection N' hN
  have hq : q m = m := Submodule.projection_apply_of_mem_left hN hm
  rw [← hq, blockProj_comm]
  exact Submodule.projection_apply_mem hN _

/-- Every element is the finite sum of its block components. -/
theorem exists_finset_blockProj (m : M) :
    ∃ s : Finset (isotypicComponents R M),
      (∀ c ∉ s, blockProj c m = 0) ∧ ∑ c ∈ s, blockProj c m = m := by
  classical
  have htop : (⨆ c : isotypicComponents R M, c.1) = ⊤ := by
    rw [← sSup_eq_iSup', sSup_isotypicComponents]
  have hm : m ∈ ⨆ c : isotypicComponents R M, c.1 := htop ▸ Submodule.mem_top
  obtain ⟨μ, hμ, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ m).mp hm
  have hproj : ∀ c, blockProj c m = μ c := by
    intro c
    conv_lhs => rw [← hsum, Finsupp.sum, map_sum]
    rw [Finset.sum_eq_single c]
    · exact blockProj_of_mem c (hμ c)
    · intro c' _ hc'
      exact blockProj_of_mem_other c c' hc' (hμ c')
    · intro hc
      rw [Finsupp.notMem_support_iff.mp hc, map_zero]
  refine ⟨μ.support, fun c hc => by rw [hproj, Finsupp.notMem_support_iff.mp hc], ?_⟩
  calc ∑ c ∈ μ.support, blockProj c m = ∑ c ∈ μ.support, μ c :=
        Finset.sum_congr rfl fun c _ => hproj c
    _ = m := hsum

end Blocks

section Coordinates

/-! ### Coordinates on finite-dimensional subrepresentations -/

variable {K : Type uK} [Group K] [TopologicalSpace K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

/-- The matrices of a finite-dimensional subrepresentation in its chosen basis. -/
def subMatrix (S : Subrepresentation ρ) [FiniteDimensional ℂ S.toSubmodule] :
    K →* Matrix (Fin (Module.finrank ℂ S.toSubmodule)) (Fin (Module.finrank ℂ S.toSubmodule))
      ℂ :=
  (LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ S.toSubmodule)).toRingEquiv.toMonoidHom.comp
    S.toRepresentation

omit [TopologicalSpace K] in
theorem subMatrix_mulVec (S : Subrepresentation ρ) [FiniteDimensional ℂ S.toSubmodule] (k : K)
    (s : S.toSubmodule) :
    subMatrix S k *ᵥ (Module.finBasis ℂ S.toSubmodule).repr s =
      (Module.finBasis ℂ S.toSubmodule).repr (S.toRepresentation k s) :=
  LinearMap.toMatrix_mulVec_repr _ _ _ _

omit [TopologicalSpace K] in
theorem subMatrix_apply (S : Subrepresentation ρ) [FiniteDimensional ℂ S.toSubmodule] (k : K)
    (i j : Fin (Module.finrank ℂ S.toSubmodule)) :
    subMatrix S k i j = (Module.finBasis ℂ S.toSubmodule).repr
      (S.toRepresentation k (Module.finBasis ℂ S.toSubmodule j)) i :=
  LinearMap.toMatrixAlgEquiv_apply _ _ _ _

/-- With continuous coefficients, the matrices of a finite-dimensional subrepresentation
depend continuously on the group element. -/
theorem continuous_subMatrix
    (hcont : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v))
    (S : Subrepresentation ρ) [FiniteDimensional ℂ S.toSubmodule] :
    Continuous (subMatrix S) := by
  refine continuous_matrix fun i j => ?_
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.finBasis ℂ S.toSubmodule).coord i)
  have h : (fun k => subMatrix S k i j) =
      fun k => g (ρ k (Module.finBasis ℂ S.toSubmodule j : V)) := by
    funext k
    rw [subMatrix_apply, ← Module.Basis.coord_apply, ← hg]
    rfl
  rw [h]
  exact hcont _ g

/-- The coordinate representation of a finite-dimensional subrepresentation. -/
def coordRep (S : Subrepresentation ρ) [FiniteDimensional ℂ S.toSubmodule] :
    Representation ℂ K (Fin (Module.finrank ℂ S.toSubmodule) → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin (Module.finrank ℂ S.toSubmodule))
    (Fin (Module.finrank ℂ S.toSubmodule)) ℂ ≃ₐ[ℂ] _).toRingEquiv.toMonoidHom.comp
    (subMatrix S)

omit [TopologicalSpace K] in
theorem coordRep_apply (S : Subrepresentation ρ) [FiniteDimensional ℂ S.toSubmodule] (k : K)
    (x : Fin (Module.finrank ℂ S.toSubmodule) → ℂ) : coordRep S k x = subMatrix S k *ᵥ x :=
  rfl

theorem continuous_coordRep
    (hcont : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v))
    (S : Subrepresentation ρ) [FiniteDimensional ℂ S.toSubmodule] :
    Continuous fun p : K × (Fin (Module.finrank ℂ S.toSubmodule) → ℂ) =>
      coordRep S p.1 p.2 :=
  ((continuous_subMatrix hcont S).comp continuous_fst).matrix_mulVec continuous_snd

omit [TopologicalSpace K] in
theorem equivFun_symm_coordRep (S : Subrepresentation ρ) [FiniteDimensional ℂ S.toSubmodule]
    (k : K) (x : Fin (Module.finrank ℂ S.toSubmodule) → ℂ) :
    (Module.finBasis ℂ S.toSubmodule).equivFun.symm (coordRep S k x) =
      S.toRepresentation k ((Module.finBasis ℂ S.toSubmodule).equivFun.symm x) := by
  obtain ⟨s, rfl⟩ := (Module.finBasis ℂ S.toSubmodule).equivFun.surjective x
  rw [LinearEquiv.symm_apply_apply, coordRep_apply, Module.Basis.equivFun_apply,
    subMatrix_mulVec, ← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply]

variable [IsTopologicalGroup K] [CompactSpace K]

/-- A finite-dimensional subrepresentation with continuous coefficients is semisimple. -/
theorem isSemisimple_of_finiteDimensional
    (hcont : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v))
    (S : Subrepresentation ρ) [FiniteDimensional ℂ S.toSubmodule] :
    S.toRepresentation.IsSemisimpleRepresentation := by
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  let C : TopologicalSpace.PositiveCompacts K := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let ν : Measure K := Measure.haarMeasure C
  have : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
  have := Langlands.Representation.CompactFinite.isSemisimple (coordRep S)
    (continuous_coordRep hcont S) ν
  exact Langlands.Algebra.CanonicalReynolds.isSemisimpleRepresentation_of_surjective
    (ρ := coordRep S) (Module.finBasis ℂ S.toSubmodule).equivFun.symm.toLinearMap
    (fun k x => equivFun_symm_coordRep S k x)
    (Module.finBasis ℂ S.toSubmodule).equivFun.symm.surjective

/-- A representation of a compact group in which every vector is finite and all coefficients
are continuous is semisimple over the group algebra. -/
theorem isSemisimpleModule (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v)) :
    IsSemisimpleModule ℂ[K] ρ.asModule := by
  have h : ∀ v : V, IsSemisimpleModule ℂ[K]
      (FiniteVectors.orbitSubrepresentation ρ v).asSubmodule := by
    intro v
    have : FiniteDimensional ℂ (FiniteVectors.orbitSubrepresentation ρ v).toSubmodule := hfin v
    exact (CompactCoefficientClass.isSemisimpleRepresentation_subrepresentation_iff _).mp
      (isSemisimple_of_finiteDimensional hcont _)
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' h ?_
  rw [eq_top_iff]
  intro v _
  exact Submodule.mem_iSup_of_mem (p := fun v : V =>
    (FiniteVectors.orbitSubrepresentation ρ v).asSubmodule) v
    (FiniteVectors.self_mem_orbitSpan ρ v)

end Coordinates

section VBlocks

/-! ### Blocks of a semisimple representation -/

variable {K : Type uK} [Group K] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ K V} [IsSemisimpleModule ℂ[K] ρ.asModule]

variable (ρ) in
/-- The blocks of `ρ`: the isotypic components of `ρ` as a module over the group algebra. -/
abbrev Block := isotypicComponents ℂ[K] ρ.asModule

/-- A block as a subrepresentation. -/
def blockSub (c : Block ρ) : Subrepresentation ρ := Subrepresentation.ofSubmodule' c.1

/-- The projection of `V` onto a block along the other blocks. -/
def proj (c : Block ρ) : V →ₗ[ℂ] V :=
  ρ.asModuleEquiv.toLinearMap ∘ₗ (blockProj c).restrictScalars ℂ ∘ₗ
    ρ.asModuleEquiv.symm.toLinearMap

theorem proj_mem (c : Block ρ) (v : V) : proj c v ∈ blockSub c :=
  blockProj_mem c v

theorem proj_of_mem (c : Block ρ) {v : V} (hv : v ∈ blockSub c) : proj c v = v :=
  blockProj_of_mem c hv

theorem proj_of_mem_other (c c' : Block ρ) (h : c' ≠ c) {v : V} (hv : v ∈ blockSub c') :
    proj c v = 0 :=
  blockProj_of_mem_other c c' h hv

theorem proj_proj_self (c : Block ρ) (v : V) : proj c (proj c v) = proj c v :=
  proj_of_mem c (proj_mem c v)

theorem proj_proj_of_ne (c c' : Block ρ) (h : c' ≠ c) (v : V) : proj c (proj c' v) = 0 :=
  proj_of_mem_other c c' h (proj_mem c' v)

theorem proj_rho (c : Block ρ) (k : K) (v : V) : proj c (ρ k v) = ρ k (proj c v) := by
  change ρ.asModuleEquiv (blockProj c (ρ.asModuleEquiv.symm (ρ k v))) =
    ρ k (ρ.asModuleEquiv (blockProj c (ρ.asModuleEquiv.symm v)))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul,
    Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

/-- Block projections preserve every subrepresentation. -/
theorem proj_mem_of_mem (c : Block ρ) (N : Subrepresentation ρ) {v : V} (hv : v ∈ N) :
    proj c v ∈ N :=
  blockProj_mem_of_mem c N.asSubmodule hv

theorem exists_finset_proj (v : V) :
    ∃ s : Finset (Block ρ), (∀ c ∉ s, proj c v = 0) ∧ ∑ c ∈ s, proj c v = v :=
  exists_finset_blockProj (M := ρ.asModule) v

end VBlocks

section AdmissibleBlocks

/-! ### Admissibility makes the blocks finite-dimensional -/

variable {K : Type uK} [Group K] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ K V}

/-- The sum over `i` of the value at the `i`-th standard basis vector of the `i`-th map of a
family in `H`. Its range contains the ranges of all maps in `H`. -/
def evalSum {d : ℕ} (H : Submodule ℂ ((Fin d → ℂ) →ₗ[ℂ] V)) : (Fin d → H) →ₗ[ℂ] V :=
  ∑ i : Fin d, (LinearMap.applyₗ (R := ℂ) (fun j => if i = j then (1 : ℂ) else 0) ∘ₗ
    H.subtype) ∘ₗ LinearMap.proj i

theorem apply_mem_range_evalSum {d : ℕ} (H : Submodule ℂ ((Fin d → ℂ) →ₗ[ℂ] V))
    {F : (Fin d → ℂ) →ₗ[ℂ] V} (hF : F ∈ H) (x : Fin d → ℂ) :
    F x ∈ LinearMap.range (evalSum H) := by
  refine ⟨fun i => x i • ⟨F, hF⟩, ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ F x]
  simp [evalSum]

/-- A simple submodule of `ρ.asModule` lies in the orbit span of each of its nonzero
vectors. -/
theorem mem_orbitSpan_of_isSimpleModule (S : Submodule ℂ[K] ρ.asModule)
    [IsSimpleModule ℂ[K] S] {s : ρ.asModule} (hs : s ∈ S) (hs0 : s ≠ 0) {v : ρ.asModule}
    (hv : v ∈ S) :
    v ∈ FiniteVectors.orbitSpan ρ s := by
  let O : Submodule ℂ[K] ρ.asModule := (FiniteVectors.orbitSubrepresentation ρ s).asSubmodule
  have hatom : IsAtom S := isSimpleModule_iff_isAtom.mp inferInstance
  have hne : O ⊓ S ≠ ⊥ := by
    intro h
    apply hs0
    have hmem : s ∈ O ⊓ S := Submodule.mem_inf.mpr ⟨FiniteVectors.self_mem_orbitSpan ρ s, hs⟩
    rw [h] at hmem
    exact (Submodule.mem_bot _).mp hmem
  have heq : O ⊓ S = S := (hatom.le_iff_eq hne).mp inf_le_right
  have hmem : v ∈ O ⊓ S := by
    rw [heq]
    exact hv
  exact (Submodule.mem_inf.mp hmem).1

variable [TopologicalSpace K]

/-- For an admissible representation in which every vector is finite with continuous
coefficients, every block is finite-dimensional: it lies in the span of the ranges of the
intertwiners from the matrix representation of one simple submodule. -/
theorem finiteDimensional_block [IsSemisimpleModule ℂ[K] ρ.asModule]
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v))
    (hadm : ∀ (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ), Continuous τ →
      FiniteDimensional ℂ (Archimedean.gkIntertwiners ρ d τ))
    (c : Block ρ) : FiniteDimensional ℂ (blockSub c).toSubmodule := by
  obtain ⟨S, hS, hc⟩ := c.2
  have : Nontrivial S := IsSimpleModule.nontrivial ℂ[K] S
  obtain ⟨⟨s, hsS⟩, hs0⟩ := exists_ne (0 : S)
  have hs0' : s ≠ 0 := fun h => hs0 (Subtype.ext h)
  let T : Subrepresentation ρ := Subrepresentation.ofSubmodule' S
  have hTle : T.toSubmodule ≤ FiniteVectors.orbitSpan ρ s := fun v hv =>
    mem_orbitSpan_of_isSimpleModule S hsS hs0' hv
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ s) := hfin s
  have : FiniteDimensional ℂ T.toSubmodule := Submodule.finiteDimensional_of_le hTle
  let b := Module.finBasis ℂ T.toSubmodule
  let H := Archimedean.gkIntertwiners ρ (Module.finrank ℂ T.toSubmodule) (subMatrix T)
  have : FiniteDimensional ℂ H := hadm _ _ (continuous_subMatrix hcont T)
  let ι : T.toSubmodule →ₗ[ℂ] S :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hB : (blockSub c).toSubmodule ≤ LinearMap.range (evalSum H) := by
    intro v hv
    change v ∈ c.1 at hv
    rw [hc, CompactSplitting.isotypicComponent_eq_iSup_range ℂ[K] ρ.asModule S] at hv
    refine Submodule.iSup_induction _
      (motive := fun v : ρ.asModule => v ∈ LinearMap.range (evalSum H)) hv
      ?_ (Submodule.zero_mem _) fun _ _ => Submodule.add_mem _
    rintro f _ ⟨t, rfl⟩
    let F : (Fin (Module.finrank ℂ T.toSubmodule) → ℂ) →ₗ[ℂ] V :=
      (f.restrictScalars ℂ) ∘ₗ ι ∘ₗ b.equivFun.symm.toLinearMap
    have hF : F ∈ H := by
      intro k x
      change f (ι (b.equivFun.symm (coordRep T k x))) = ρ k (f (ι (b.equivFun.symm x)))
      rw [equivFun_symm_coordRep]
      have hι : ι (T.toRepresentation k (b.equivFun.symm x)) =
          MonoidAlgebra.of ℂ K k • ι (b.equivFun.symm x) :=
        Subtype.ext (Representation.asModuleEquiv_symm_map_rho ρ k _)
      rw [hι, map_smul]
      exact (Representation.asModuleEquiv_symm_map_rho ρ k _).symm
    have ht : f t = F (b.equivFun ⟨t.1, t.2⟩) := by
      change f t = f (ι (b.equivFun.symm (b.equivFun ⟨t.1, t.2⟩)))
      rw [LinearEquiv.symm_apply_apply]
      rfl
    rw [ht]
    exact apply_mem_range_evalSum H hF _
  exact Submodule.finiteDimensional_of_le hB

end AdmissibleBlocks

section DualBlocks

/-! ### Block components of functionals -/

variable {K : Type uK} [Group K] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ K V} [IsSemisimpleModule ℂ[K] ρ.asModule]

/-- The projection onto a block, with values in the block. -/
def projTo (c : Block ρ) : V →ₗ[ℂ] (blockSub c).toSubmodule :=
  (proj c).codRestrict (blockSub c).toSubmodule (proj_mem c)

theorem coe_projTo (c : Block ρ) (v : V) : (projTo c v : V) = proj c v :=
  rfl

theorem projTo_rho (c : Block ρ) (k : K) (v : V) :
    projTo c (ρ k v) = (blockSub c).toRepresentation k (projTo c v) :=
  Subtype.ext (proj_rho c k v)

omit [IsSemisimpleModule ℂ[K] ρ.asModule] in
theorem dual_apply_apply (k : K) (w : Module.Dual ℂ V) (v : V) :
    ρ.dual k w v = w (ρ k⁻¹ v) :=
  rfl

omit [IsSemisimpleModule ℂ[K] ρ.asModule] in
theorem dual_inv_apply_apply (k : K) (w : Module.Dual ℂ V) (v : V) :
    ρ.dual k⁻¹ w v = w (ρ k v) := by
  rw [dual_apply_apply, inv_inv]

/-- A functional factoring through the projection onto a finite-dimensional block is a finite
vector of the dual representation. -/
theorem isFiniteVector_comp_projTo (c : Block ρ)
    [FiniteDimensional ℂ (blockSub c).toSubmodule]
    (φ : Module.Dual ℂ (blockSub c).toSubmodule) :
    FiniteVectors.IsFiniteVector ρ.dual (φ ∘ₗ projTo c) := by
  have hle : FiniteVectors.orbitSpan ρ.dual (φ ∘ₗ projTo c) ≤
      LinearMap.range (projTo c).dualMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨φ ∘ₗ (blockSub c).toRepresentation k⁻¹, LinearMap.ext fun v => ?_⟩
    change φ ((blockSub c).toRepresentation k⁻¹ (projTo c v)) = φ (projTo c (ρ k⁻¹ v))
    rw [projTo_rho]
  exact Submodule.finiteDimensional_of_le hle

theorem comp_proj_eq (c : Block ρ) (w : Module.Dual ℂ V) :
    w ∘ₗ proj c = (w ∘ₗ (blockSub c).toSubmodule.subtype) ∘ₗ projTo c :=
  LinearMap.ext fun _ => rfl

theorem isFiniteVector_comp_proj (c : Block ρ) [FiniteDimensional ℂ (blockSub c).toSubmodule]
    (w : Module.Dual ℂ V) : FiniteVectors.IsFiniteVector ρ.dual (w ∘ₗ proj c) := by
  rw [comp_proj_eq]
  exact isFiniteVector_comp_projTo c _

/-- The common kernel of a subrepresentation of the dual is a subrepresentation. -/
def coannihilator (G : Subrepresentation ρ.dual) : Subrepresentation ρ where
  toSubmodule := G.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule k v hv := by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro g hg
    rw [← dual_inv_apply_apply]
    exact hv _ (G.apply_mem_toSubmodule k⁻¹ hg)

/-- The block component of a finite vector of the dual lies in its orbit span. -/
theorem comp_proj_mem_orbitSpan (c : Block ρ) {w : Module.Dual ℂ V}
    (hw : FiniteVectors.IsFiniteVector ρ.dual w) :
    w ∘ₗ proj c ∈ FiniteVectors.orbitSpan ρ.dual w := by
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ.dual w) := hw
  let G := FiniteVectors.orbitSubrepresentation ρ.dual w
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := FiniteVectors.orbitSpan ρ.dual w),
    Submodule.mem_dualAnnihilator]
  intro v hv
  have hpv : proj c v ∈ coannihilator G := proj_mem_of_mem c (coannihilator G) hv
  exact (Submodule.mem_dualCoannihilator _).mp hpv w (FiniteVectors.self_mem_orbitSpan ρ.dual w)

/-- A finite vector of the dual has only finitely many nonzero block components. -/
theorem finite_comp_proj_ne_zero {ℓ : Module.Dual ℂ V}
    (hℓ : FiniteVectors.IsFiniteVector ρ.dual ℓ) :
    Set.Finite {c : Block ρ | ℓ ∘ₗ proj c ≠ 0} := by
  classical
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ.dual ℓ) := hℓ
  let f : {c : Block ρ | ℓ ∘ₗ proj c ≠ 0} → FiniteVectors.orbitSpan ρ.dual ℓ :=
    fun c => ⟨ℓ ∘ₗ proj c.1, comp_proj_mem_orbitSpan c.1 hℓ⟩
  have hli : LinearIndependent ℂ f := by
    rw [linearIndependent_iff']
    intro t a hsum i hi
    obtain ⟨v, hv⟩ : ∃ v, ℓ (proj i.1 v) ≠ 0 := by
      by_contra h
      push Not at h
      exact i.2 (LinearMap.ext h)
    have h1 := congrArg
      (fun x : FiniteVectors.orbitSpan ρ.dual ℓ => (x : Module.Dual ℂ V) (proj i.1 v)) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, ZeroMemClass.coe_zero, LinearMap.zero_apply, f,
      LinearMap.comp_apply, smul_eq_mul] at h1
    rw [Finset.sum_eq_single i] at h1
    · rw [proj_proj_self] at h1
      exact (mul_eq_zero.mp h1).resolve_right hv
    · intro j _ hji
      rw [proj_proj_of_ne j.1 i.1 (fun h => hji (Subtype.ext h.symm)), map_zero, mul_zero]
    · intro hi'
      exact absurd hi hi'
  exact Set.finite_coe_iff.mp hli.finite_of_isNoetherian

/-- A finite vector of the dual is the sum of its finitely many nonzero block components. -/
theorem eq_sum_comp_proj {ℓ : Module.Dual ℂ V} (hℓ : FiniteVectors.IsFiniteVector ρ.dual ℓ) :
    ℓ = ∑ c ∈ (finite_comp_proj_ne_zero hℓ).toFinset, ℓ ∘ₗ proj c := by
  classical
  ext v
  obtain ⟨t, ht0, htsum⟩ := exists_finset_proj (ρ := ρ) v
  set s := (finite_comp_proj_ne_zero hℓ).toFinset with hs
  have hs0 : ∀ c ∉ s, ℓ (proj c v) = 0 := by
    intro c hc
    have hc' : ℓ ∘ₗ proj c = 0 := by simpa [hs] using hc
    exact LinearMap.congr_fun hc' v
  rw [LinearMap.sum_apply]
  conv_lhs => rw [← htsum, map_sum]
  calc ∑ c ∈ t, ℓ (proj c v) = ∑ c ∈ t ∪ s, ℓ (proj c v) :=
        Finset.sum_subset Finset.subset_union_left fun c hc hct => by
          rcases Finset.mem_union.mp hc with h | h
          · exact absurd h hct
          · rw [ht0 c hct, map_zero]
    _ = ∑ c ∈ s, (ℓ ∘ₗ proj c) v :=
        (Finset.sum_subset Finset.subset_union_right fun c _ hcs => hs0 c hcs).symm

variable (hblock : ∀ c : Block ρ, FiniteDimensional ℂ (blockSub c).toSubmodule)
include hblock

/-- Finite vectors of the dual separate the points of `V`. -/
theorem exists_isFiniteVector_apply_ne_zero {v : V} (hv : v ≠ 0) :
    ∃ ℓ : Module.Dual ℂ V, FiniteVectors.IsFiniteVector ρ.dual ℓ ∧ ℓ v ≠ 0 := by
  obtain ⟨t, -, htsum⟩ := exists_finset_proj (ρ := ρ) v
  obtain ⟨c, -, hc⟩ : ∃ c ∈ t, proj c v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (htsum ▸ Finset.sum_eq_zero h)
  have hc' : projTo c v ≠ 0 := fun h => hc (congrArg Subtype.val h)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (blockSub c).toSubmodule, φ (projTo c v) ≠ 0 := by
    by_contra h
    push Not at h
    exact hc' ((Module.forall_dual_apply_eq_zero_iff ℂ _).mp h)
  have := hblock c
  exact ⟨φ ∘ₗ projTo c, isFiniteVector_comp_projTo c φ, hφ⟩

/-- Restriction to a finite-dimensional block maps a separating space of functionals onto the
dual of the block. -/
theorem exists_mem_comp_proj_eq (W' : Submodule ℂ (Module.Dual ℂ V))
    (hsep : ∀ v : V, (∀ w ∈ W', w v = 0) → v = 0) (c : Block ρ) (ℓ : Module.Dual ℂ V) :
    ∃ w ∈ W', w ∘ₗ proj c = ℓ ∘ₗ proj c := by
  have := hblock c
  let r : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ (blockSub c).toSubmodule :=
    (blockSub c).toSubmodule.subtype.dualMap
  let D := W'.map r
  have h1 : D.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    rw [Submodule.mem_bot]
    exact Subtype.ext (hsep x fun w hw => hx (r w) (Submodule.mem_map_of_mem hw))
  have hD : D = ⊤ := by
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := D)
    rw [h1, Submodule.dualAnnihilator_bot] at h2
    exact h2.symm
  obtain ⟨w, hw, hrw⟩ : r ℓ ∈ D := hD ▸ Submodule.mem_top
  refine ⟨w, hw, LinearMap.ext fun v => ?_⟩
  exact LinearMap.congr_fun hrw (projTo c v)

/-- A subrepresentation of the dual consisting of finite vectors and separating the points of
`V` contains every finite vector of the dual. -/
theorem mem_of_separating (W' : Subrepresentation ρ.dual)
    (hW' : ∀ w ∈ W', FiniteVectors.IsFiniteVector ρ.dual w)
    (hsep : ∀ v : V, (∀ w ∈ W', w v = 0) → v = 0) {ℓ : Module.Dual ℂ V}
    (hℓ : FiniteVectors.IsFiniteVector ρ.dual ℓ) : ℓ ∈ W' := by
  rw [eq_sum_comp_proj hℓ]
  refine Submodule.sum_mem W'.toSubmodule fun c _ => ?_
  obtain ⟨w, hw, hwc⟩ := exists_mem_comp_proj_eq hblock W'.toSubmodule hsep c ℓ
  rw [← hwc]
  exact FiniteVectors.orbitSpan_le ρ.dual w W' hw (comp_proj_mem_orbitSpan c (hW' w hw))

end DualBlocks

section MatrixRep

/-! ### Matrix representations -/

variable {K : Type uK} [Group K] [TopologicalSpace K]

/-- The representation of `K` on column vectors given by a matrix representation. -/
def matrixRep {d : ℕ} (τ : K →* Matrix (Fin d) (Fin d) ℂ) : Representation ℂ K (Fin d → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] _).toRingEquiv.toMonoidHom.comp τ

omit [TopologicalSpace K] in
theorem matrixRep_apply {d : ℕ} (τ : K →* Matrix (Fin d) (Fin d) ℂ) (k : K) (x : Fin d → ℂ) :
    matrixRep τ k x = τ k *ᵥ x :=
  rfl

theorem continuous_matrixRep {d : ℕ} {τ : K →* Matrix (Fin d) (Fin d) ℂ} (hτ : Continuous τ) :
    Continuous fun p : K × (Fin d → ℂ) => matrixRep τ p.1 p.2 :=
  (hτ.comp continuous_fst).matrix_mulVec continuous_snd

/-- The contragredient matrix representation `k ↦ (σ k⁻¹)ᵀ`. -/
def contraMatrix {d : ℕ} (σ : K →* Matrix (Fin d) (Fin d) ℂ) :
    K →* Matrix (Fin d) (Fin d) ℂ where
  toFun k := (σ k⁻¹)ᵀ
  map_one' := by simp
  map_mul' k h := by simp [Matrix.transpose_mul]

omit [TopologicalSpace K] in
theorem contraMatrix_apply {d : ℕ} (σ : K →* Matrix (Fin d) (Fin d) ℂ) (k : K) :
    contraMatrix σ k = (σ k⁻¹)ᵀ :=
  rfl

theorem continuous_contraMatrix [IsTopologicalGroup K] {d : ℕ}
    {σ : K →* Matrix (Fin d) (Fin d) ℂ} (hσ : Continuous σ) : Continuous (contraMatrix σ) :=
  (hσ.comp continuous_inv).matrix_transpose

variable [IsTopologicalGroup K] [CompactSpace K]

/-- An invariant subspace of a continuous matrix representation of a compact group has an
equivariant projection onto it. -/
theorem exists_equivariant_projection_matrix {d : ℕ} {τ : K →* Matrix (Fin d) (Fin d) ℂ}
    (hτ : Continuous τ) (S : Subrepresentation (matrixRep τ)) :
    ∃ P : (matrixRep τ).IntertwiningMap (matrixRep τ), (∀ v, P v ∈ S) ∧ ∀ v ∈ S, P v = v := by
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  let C : TopologicalSpace.PositiveCompacts K := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let ν : Measure K := Measure.haarMeasure C
  have : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
  exact Langlands.Representation.CompactFinite.exists_equivariant_projection (matrixRep τ)
    (continuous_matrixRep hτ) ν S

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

/-- An equivariant map `φ` from a semisimple representation to a continuous matrix
representation has a right inverse on its range given by an intertwiner. -/
theorem exists_mem_gkIntertwiners_comp [IsSemisimpleModule ℂ[K] ρ.asModule] {d : ℕ}
    {τ : K →* Matrix (Fin d) (Fin d) ℂ} (hτ : Continuous τ) (φ : V →ₗ[ℂ] (Fin d → ℂ))
    (hφ : ∀ (k : K) (v : V), φ (ρ k v) = τ k *ᵥ φ v) :
    ∃ ψ ∈ Archimedean.gkIntertwiners ρ d τ, ∀ v : V, φ (ψ (φ v)) = φ v := by
  let R : Subrepresentation (matrixRep τ) :=
    { toSubmodule := LinearMap.range φ
      apply_mem_toSubmodule := by
        rintro k _ ⟨v, rfl⟩
        exact ⟨ρ k v, hφ k v⟩ }
  obtain ⟨P, hPmem, hPid⟩ := exists_equivariant_projection_matrix hτ R
  let N : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker φ
      apply_mem_toSubmodule := by
        intro k v hv
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hφ, hv, Matrix.mulVec_zero] }
  obtain ⟨E', hE'⟩ := exists_isCompl N.asSubmodule
  let E : Subrepresentation ρ := Subrepresentation.ofSubmodule' E'
  let g : E.toSubmodule →ₗ[ℂ] LinearMap.range φ :=
    (φ ∘ₗ E.toSubmodule.subtype).codRestrict _ fun e => LinearMap.mem_range_self φ _
  have hginj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro e he
    rw [LinearMap.mem_ker] at he
    have he' : φ e = 0 := congrArg Subtype.val he
    rw [Submodule.mem_bot]
    exact Subtype.ext (Submodule.disjoint_def.mp hE'.disjoint _ he' e.2)
  have hgsurj : Function.Surjective g := by
    rintro ⟨_, v, rfl⟩
    have hv : (show ρ.asModule from v) ∈ N.asSubmodule ⊔ E' :=
      hE'.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.mp hv
    have ha' : φ (ρ.asModuleEquiv a) = 0 := ha
    have hae' : ρ.asModuleEquiv a + ρ.asModuleEquiv e = v := by
      rw [← map_add]; exact hae
    refine ⟨⟨ρ.asModuleEquiv e, he⟩, Subtype.ext ?_⟩
    change φ (ρ.asModuleEquiv e) = φ v
    rw [← hae', map_add, ha', zero_add]
  let eg := LinearEquiv.ofBijective g ⟨hginj, hgsurj⟩
  let P' : (Fin d → ℂ) →ₗ[ℂ] LinearMap.range φ := P.toLinearMap.codRestrict _ hPmem
  let ψ : (Fin d → ℂ) →ₗ[ℂ] V := E.toSubmodule.subtype ∘ₗ eg.symm.toLinearMap ∘ₗ P'
  refine ⟨ψ, ?_, ?_⟩
  · intro k x
    have hP : P' (τ k *ᵥ x) =
        ⟨τ k *ᵥ (P' x : Fin d → ℂ), R.apply_mem_toSubmodule k (P' x).2⟩ :=
      Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ P k x)
    have hsymm : eg.symm (P' (τ k *ᵥ x)) = E.toRepresentation k (eg.symm (P' x)) := by
      rw [LinearEquiv.symm_apply_eq, hP]
      apply Subtype.ext
      change τ k *ᵥ (P' x : Fin d → ℂ) = φ (ρ k (eg.symm (P' x) : V))
      rw [hφ]
      exact congrArg (fun y => τ k *ᵥ y)
        (congrArg Subtype.val (eg.apply_symm_apply (P' x))).symm
    change ((eg.symm (P' (τ k *ᵥ x)) : V)) = ρ k (eg.symm (P' x) : V)
    rw [hsymm]
    rfl
  · intro v
    have h1 : P' (φ v) = ⟨φ v, LinearMap.mem_range_self φ v⟩ :=
      Subtype.ext (hPid _ ⟨v, rfl⟩)
    have h2 := congrArg Subtype.val (eg.apply_symm_apply (P' (φ v)))
    change φ (eg.symm (P' (φ v)) : V) = (P' (φ v) : Fin d → ℂ) at h2
    change φ (eg.symm (P' (φ v)) : V) = φ v
    rw [h2, h1]

end MatrixRep

section KDual

/-! ### The representation on the finite vectors of the dual -/

variable {K : Type uK} [Group K] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ K V}

variable (ρ) in
/-- The space of finite vectors of the dual representation. -/
abbrev kDual : Submodule ℂ (Module.Dual ℂ V) :=
  (FiniteVectors.subrepresentation ρ.dual).toSubmodule

variable (ρ) in
/-- The representation of `K` on the finite vectors of the dual. -/
abbrev kDualRep : Representation ℂ K (kDual ρ) :=
  FiniteVectors.representation ρ.dual

theorem coe_kDualRep_apply (k : K) (w : kDual ρ) :
    ((kDualRep ρ k w : kDual ρ) : Module.Dual ℂ V) = ρ.dual k w :=
  rfl

theorem isFiniteVector_kDualRep (w : kDual ρ) : FiniteVectors.IsFiniteVector (kDualRep ρ) w :=
  (FiniteVectors.isFiniteVector_map_iff (FiniteVectors.inclusion ρ.dual)
    (FiniteVectors.inclusion_injective ρ.dual) w).mp w.2

/-- If a family of linear functionals `e g` separates the vectors of a finite-dimensional
subspace `S`, every linear functional agrees on `S` with a finite linear combination of them. -/
theorem exists_sum_of_separating_family {G : Type*} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (e : G → M →ₗ[ℂ] ℂ) (S : Submodule ℂ M) [FiniteDimensional ℂ S]
    (he : ∀ s ∈ S, (∀ g, e g s = 0) → s = 0) (ℓ : M →ₗ[ℂ] ℂ) :
    ∃ (m : ℕ) (p : Fin m → G) (a : Fin m → ℂ), ∀ s ∈ S, ℓ s = ∑ i, a i * e (p i) s := by
  let D : Submodule ℂ (Module.Dual ℂ S) :=
    Submodule.span ℂ (Set.range fun g => (e g).domRestrict S)
  have h1 : D.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    rw [Submodule.mem_dualCoannihilator] at hs
    have hs0 : (s : M) = 0 := he s s.2 fun g => hs _ (Submodule.subset_span ⟨g, rfl⟩)
    rw [Submodule.mem_bot]
    exact Subtype.ext hs0
  have hD : D = ⊤ := by
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := D)
    rw [h1, Submodule.dualAnnihilator_bot] at h2
    exact h2.symm
  have hℓ : ℓ.domRestrict S ∈ D := hD ▸ Submodule.mem_top
  obtain ⟨m, c, q, hq⟩ := Submodule.mem_span_set'.mp hℓ
  choose p hp using fun i => (q i).2
  refine ⟨m, p, c, fun s hs => ?_⟩
  have h3 := congrArg (fun L : Module.Dual ℂ S => L ⟨s, hs⟩) hq
  simp only [LinearMap.domRestrict_apply] at h3
  rw [← h3, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, ← hp i, LinearMap.domRestrict_apply, smul_eq_mul]

variable [TopologicalSpace K] [IsTopologicalGroup K]

/-- With continuous coefficients on `V`, the representation on the finite vectors of the dual
has continuous coefficients. -/
theorem continuous_kDualRep (hcont : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v))
    (w : kDual ρ) (ℓ : kDual ρ →ₗ[ℂ] ℂ) : Continuous fun k => ℓ (kDualRep ρ k w) := by
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan (kDualRep ρ) w) :=
    isFiniteVector_kDualRep w
  let e : V → (kDual ρ →ₗ[ℂ] ℂ) := fun v => Module.Dual.eval ℂ V v ∘ₗ (kDual ρ).subtype
  obtain ⟨m, p, a, h⟩ := exists_sum_of_separating_family e
    (FiniteVectors.orbitSpan (kDualRep ρ) w)
    (fun s _ hs => Subtype.ext (LinearMap.ext fun v => hs v)) ℓ
  have heq : (fun k => ℓ (kDualRep ρ k w)) =
      fun k => ∑ i, a i * (w : Module.Dual ℂ V) (ρ k⁻¹ (p i)) := by
    funext k
    rw [h _ (FiniteVectors.action_mem_orbitSpan _ k w)]
    rfl
  rw [heq]
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((hcont (p i) (w : Module.Dual ℂ V)).comp continuous_inv)

end KDual

section KDualAdmissible

/-! ### Admissibility of the finite dual and functionals on it -/

variable {K : Type uK} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

/-- The coefficients of a vector against the functionals `T eᵢ`. -/
def coef {d : ℕ} (T : (Fin d → ℂ) →ₗ[ℂ] kDual ρ) : V →ₗ[ℂ] (Fin d → ℂ) :=
  LinearMap.pi fun i => ((T fun j => if i = j then (1 : ℂ) else 0 : kDual ρ) : Module.Dual ℂ V)

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] in
theorem coef_apply {d : ℕ} (T : (Fin d → ℂ) →ₗ[ℂ] kDual ρ) (v : V) (i : Fin d) :
    coef T v i = ((T fun j => if i = j then (1 : ℂ) else 0 : kDual ρ) : Module.Dual ℂ V) v :=
  rfl

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] in
/-- The coefficient map of an intertwiner into the finite dual is equivariant for the
contragredient matrix representation. -/
theorem coef_rho {d : ℕ} {σ : K →* Matrix (Fin d) (Fin d) ℂ} {T : (Fin d → ℂ) →ₗ[ℂ] kDual ρ}
    (hT : T ∈ Archimedean.gkIntertwiners (kDualRep ρ) d σ) (k : K) (v : V) :
    coef T (ρ k v) = contraMatrix σ k *ᵥ coef T v := by
  funext i
  have h1 : T (σ k⁻¹ *ᵥ fun j => if i = j then (1 : ℂ) else 0) =
      kDualRep ρ k⁻¹ (T fun j => if i = j then (1 : ℂ) else 0) := hT k⁻¹ _
  have h2 : coef T (ρ k v) i =
      ((T (σ k⁻¹ *ᵥ fun j => if i = j then (1 : ℂ) else 0) : kDual ρ) : Module.Dual ℂ V) v := by
    rw [h1, coe_kDualRep_apply, dual_inv_apply_apply]
    rfl
  rw [h2, LinearMap.pi_apply_eq_sum_univ T]
  simp [coef_apply, contraMatrix_apply, Matrix.mulVec, dotProduct, LinearMap.sum_apply]

/-- With every vector finite and continuous coefficients, an admissible representation has an
admissible finite dual. -/
theorem admissible_kDual (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v))
    (hadm : ∀ (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ), Continuous τ →
      FiniteDimensional ℂ (Archimedean.gkIntertwiners ρ d τ)) :
    Archimedean.IsAdmissibleGKModule (kDualRep ρ) := by
  intro d σ hσ
  have : IsSemisimpleModule ℂ[K] ρ.asModule := isSemisimpleModule hfin hcont
  let H := Archimedean.gkIntertwiners ρ d (contraMatrix σ)
  have : FiniteDimensional ℂ H := hadm d _ (continuous_contraMatrix hσ)
  let B := LinearMap.range (evalSum H)
  have : FiniteDimensional ℂ B := LinearMap.finiteDimensional_range _
  have hzero : ∀ D ∈ Archimedean.gkIntertwiners (kDualRep ρ) d σ,
      (∀ b ∈ B, coef D b = 0) → D = 0 := by
    intro D hD hB
    obtain ⟨ψ, hψ, hψφ⟩ := exists_mem_gkIntertwiners_comp (continuous_contraMatrix hσ)
      (coef D) (coef_rho hD)
    have hz : ∀ v, coef D v = 0 := fun v => by
      rw [← hψφ v]
      exact hB _ (apply_mem_range_evalSum H hψ _)
    apply LinearMap.ext
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ D x, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi : D (fun j => if i = j then 1 else 0) = 0 :=
      Subtype.ext (LinearMap.ext fun v => congrFun (hz v) i)
    rw [hi, smul_zero]
  let Φ : Archimedean.gkIntertwiners (kDualRep ρ) d σ →ₗ[ℂ] (B →ₗ[ℂ] (Fin d → ℂ)) :=
    { toFun := fun T => coef T.1 ∘ₗ B.subtype
      map_add' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl
      map_smul' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl }
  have hinj : Function.Injective Φ := by
    intro T T' h
    have hD : T.1 - T'.1 ∈ Archimedean.gkIntertwiners (kDualRep ρ) d σ := by
      intro k x
      rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, T.2 k x, T'.2 k x]
    have h0 := hzero _ hD fun b hb => by
      have hb' := LinearMap.congr_fun h ⟨b, hb⟩
      funext i
      exact sub_eq_zero.mpr (congrFun hb' i)
    exact Subtype.ext (sub_eq_zero.mp h0)
  exact Module.Finite.of_injective Φ hinj

/-- With every vector finite, continuous coefficients and admissibility, every finite linear
functional on the finite dual is evaluation at a vector of `V`. -/
theorem exists_eq_eval (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v))
    (hadm : ∀ (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ), Continuous τ →
      FiniteDimensional ℂ (Archimedean.gkIntertwiners ρ d τ))
    {μ : Module.Dual ℂ (kDual ρ)} (hμ : FiniteVectors.IsFiniteVector (kDualRep ρ).dual μ) :
    ∃ v : V, ∀ w : kDual ρ, μ w = (w : Module.Dual ℂ V) v := by
  have : IsSemisimpleModule ℂ[K] (kDualRep ρ).asModule :=
    isSemisimpleModule isFiniteVector_kDualRep (continuous_kDualRep hcont)
  have hblock : ∀ c : Block (kDualRep ρ), FiniteDimensional ℂ (blockSub c).toSubmodule :=
    finiteDimensional_block isFiniteVector_kDualRep (continuous_kDualRep hcont)
      (admissible_kDual hfin hcont hadm)
  let ev : V →ₗ[ℂ] Module.Dual ℂ (kDual ρ) :=
    (kDual ρ).subtype.dualMap ∘ₗ Module.Dual.eval ℂ V
  have hev_apply : ∀ (v : V) (w : kDual ρ), ev v w = (w : Module.Dual ℂ V) v := fun _ _ => rfl
  have hev : ∀ (k : K) (v : V), ev (ρ k v) = (kDualRep ρ).dual k (ev v) := by
    intro k v
    apply LinearMap.ext
    intro w
    rw [dual_apply_apply, hev_apply, hev_apply, coe_kDualRep_apply, dual_inv_apply_apply]
  let evK : ρ.IntertwiningMap (kDualRep ρ).dual :=
    LinearMap.intertwiningMap_of_isIntertwiningMap (ρ := ρ) (σ := (kDualRep ρ).dual) (f := ev) hev
  let W'' : Subrepresentation (kDualRep ρ).dual :=
    { toSubmodule := LinearMap.range ev
      apply_mem_toSubmodule := by
        rintro k _ ⟨v, rfl⟩
        exact ⟨ρ k v, hev k v⟩ }
  have hW'' : ∀ x ∈ W'', FiniteVectors.IsFiniteVector (kDualRep ρ).dual x := by
    rintro _ ⟨v, rfl⟩
    exact (hfin v).map evK
  have hsep : ∀ w : kDual ρ, (∀ x ∈ W'', x w = 0) → w = 0 := by
    intro w hw
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact hw (ev v) ⟨v, rfl⟩
  obtain ⟨v, hv⟩ := mem_of_separating hblock W'' hW'' hsep hμ
  exact ⟨v, fun w => by rw [← hv, hev_apply]⟩

end KDualAdmissible

end Langlands.KFiniteDual
