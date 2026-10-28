import Langlands.Representation.MatrixCoefficient.HilbertComponentStatement
import Langlands.Representation.MatrixCoefficient.CoefficientL2
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Unitary.AlgebraicToClosedIrreducibilityProof
import Langlands.Representation.Unitary.CompletionIntertwiner
import Langlands.Representation.Unitary.SmoothVectorRecoveryProof

/-!
# A closed coefficient component in the actual central L2 completion

The coefficient map of a square-integrable representation is completed to an
equivariant isometry of Hilbert completions; its range is the component.
-/

noncomputable section

namespace Langlands.CoefficientHilbertComponentAux

universe uG uV uH uK

variable {G : Type uG} [Group G]
  {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]
  {K : Type uK} [NormedAddCommGroup K] [NormedSpace ℂ K]
  {σ : Representation ℂ G H} {τ : Representation ℂ G K}

/-- Transfer closed irreducibility through an equivariant isometry onto an
invariant range. -/
theorem closed_irreducible_range
    (e : H →ₗᵢ[ℂ] K)
    (he : ∀ g x, e (σ g x) = τ g (e x))
    (R : Subrepresentation τ)
    (hrange : Set.range e = (R : Set K))
    (hσ : Nontrivial H ∧ ∀ S : Subrepresentation σ,
      IsClosed (S : Set H) → S = ⊥ ∨ S = ⊤) :
    Nontrivial R.toSubmodule ∧ ∀ S : Subrepresentation R.toRepresentation,
      IsClosed (S : Set R.toSubmodule) → S = ⊥ ∨ S = ⊤ := by
  have hmem (x : H) : e x ∈ R := by
    change e x ∈ (R : Set K)
    rw [← hrange]
    exact ⟨x, rfl⟩
  let q : H →ₗ[ℂ] R.toSubmodule := e.toLinearMap.codRestrict R.toSubmodule hmem
  have hqi : Function.Injective q := by
    intro x y hxy
    exact e.injective (congrArg Subtype.val hxy)
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ : ∃ x, e x = y.val := by
      have hy : y.val ∈ Set.range e := by rw [hrange]; exact y.property
      exact hy
    exact ⟨x, Subtype.ext hx⟩
  have hqc : Continuous q := e.continuous.subtype_mk hmem
  have hq (g : G) (x : H) : q (σ g x) = R.toRepresentation g (q x) :=
    Subtype.ext (he g x)
  have : Nontrivial H := hσ.1
  refine ⟨?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := exists_pair_ne H
    exact ⟨⟨q x, q y, fun h => hxy (hqi h)⟩⟩
  · intro S hS
    let T : Subrepresentation σ :=
      { toSubmodule := S.toSubmodule.comap q
        apply_mem_toSubmodule g x hx := by
          change q (σ g x) ∈ S
          rw [hq]
          exact S.apply_mem_toSubmodule g hx }
    have hTclosed : IsClosed (T : Set H) := hS.preimage hqc
    rcases hσ.2 T hTclosed with hT | hT
    · left
      apply le_antisymm ?_ bot_le
      intro y hy
      obtain ⟨x, hx⟩ := hqs y
      have hxT : x ∈ T := by
        change q x ∈ S
        rwa [hx]
      have hx0 : x = 0 := by
        rw [hT] at hxT
        exact hxT
      change y = 0
      rw [← hx, hx0, map_zero]
    · right
      apply top_unique
      intro y _
      obtain ⟨x, rfl⟩ := hqs y
      have hx : x ∈ T := by rw [hT]; trivial
      exact hx

variable [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

/-- An equivariant isometry transports smooth-vector recovery to its
invariant range. -/
theorem smooth_range_image
    (j : ρ.IntertwiningMap σ)
    (hrecover : ∀ x : H, x ∈ smoothVectors σ ↔ ∃ v : V, j v = x)
    (e : H →ₗᵢ[ℂ] K)
    (he : ∀ g x, e (σ g x) = τ g (e x))
    (R : Subrepresentation τ)
    (hrange : Set.range e = (R : Set K)) :
    ∀ y : K, (y ∈ R ∧ y ∈ smoothVectors τ) ↔
      ∃ v : V, e (j v) = y := by
  let f : σ.IntertwiningMap τ :=
    { e.toLinearMap with
      isIntertwining' g := by
        apply LinearMap.ext
        exact he g }
  have hmem (x : H) : e x ∈ R := by
    change e x ∈ (R : Set K)
    rw [← hrange]
    exact ⟨x, rfl⟩
  intro y
  constructor
  · rintro ⟨hyR, hysmooth⟩
    obtain ⟨x, rfl⟩ : ∃ x, e x = y := by
      have hy : y ∈ Set.range e := by rw [hrange]; exact hyR
      exact hy
    have hx : x ∈ smoothVectors σ :=
      isSmoothVector_of_injective f e.injective hysmooth
    obtain ⟨v, hv⟩ := (hrecover x).mp hx
    exact ⟨v, congrArg e hv⟩
  · rintro ⟨v, rfl⟩
    refine ⟨hmem _, ?_⟩
    exact isSmoothVector_map f ((hrecover (j v)).mpr ⟨v, rfl⟩)

end Langlands.CoefficientHilbertComponentAux

namespace Langlands.CoefficientHilbertComponentAux

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

/-- The canonical map into the Hilbert completion, as an intertwiner. -/
def toHilbertIntertwiner (b : InvariantPositiveForm ρ) :
    ρ.IntertwiningMap b.completedRepresentation where
  toLinearMap := b.toHilbert
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact (b.completedRepresentation_toHilbert g v).symm

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem toHilbertIntertwiner_apply (b : InvariantPositiveForm ρ) (v : V) :
    toHilbertIntertwiner b v = b.toHilbert v := rfl

/-- The proved admissible algebraic-to-closed comparison, applied to the
canonical completion. -/
theorem completion_closed_irreducible
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (hI : Representation.IsIrreducible ρ)
    (b : InvariantPositiveForm ρ) :
    Nontrivial b.HilbertCompletion ∧
      ∀ S : Subrepresentation b.completedRepresentation,
        IsClosed (S : Set b.HilbertCompletion) → S = ⊥ ∨ S = ⊤ := by
  let π : G →* (b.HilbertCompletion →L[ℂ] b.HilbertCompletion) :=
    { toFun := b.completedLinearMap
      map_one' := by
        ext x
        exact b.completedLinearMap_one x
      map_mul' g h := by
        ext x
        exact b.completedLinearMap_mul g h x }
  have hirr := admissibleAlgebraicToClosedIrreducibility.{uG,uV,uV}
    G hcofinal V ρ hρ hI b b.HilbertCompletion
    π b.toHilbert b.denseRange_toHilbert
    (fun g v => (b.completedLinearMap_toHilbert g v).symm)
    b.inner_toHilbert
  refine ⟨hirr.1, ?_⟩
  intro S hS
  rcases hirr.2 S.toSubmodule hS
    (fun g x hx => S.apply_mem_toSubmodule g hx) with hz | ht
  · left
    exact Subrepresentation.toSubmodule_injective hz
  · right
    exact Subrepresentation.toSubmodule_injective ht

/-- The proved smooth-vector recovery, applied to the canonical completion. -/
theorem completion_smooth_recovery
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (b : InvariantPositiveForm ρ) :
    ∀ x : b.HilbertCompletion,
      x ∈ smoothVectors b.completedRepresentation ↔
        ∃ v : V, toHilbertIntertwiner b v = x :=
  admissibleSmoothVectorRecovery.{uG,uV,uV} G hcofinal V ρ hρ b
    b.HilbertCompletion b.completedRepresentation
    (fun g => (b.completedOperator g).continuous) (toHilbertIntertwiner b)
    b.denseRange_toHilbert b.inner_toHilbert

end Langlands.CoefficientHilbertComponentAux

namespace Langlands

universe uG uV

open CoefficientHilbertComponentAux in
/-- An irreducible square-integrable unitarizable representation occurs as a
closed irreducible coefficient component in the actual central L2 completion,
with its original algebraic carrier recovered as the smooth vectors. -/
theorem squareIntegrableCoefficientHilbertComponent :
    SquareIntegrableCoefficientHilbertComponentStatement.{uG,uV} := by
  intro G _ _ _ hcofinal V _ _ ρ _ _ μ _ _ hI hsq hu
  have hemb := hsq.exists_coefficientL2_embedding μ hu
  obtain ⟨c, ℓ, hL2, hℓ, hinj⟩ := hemb
  refine ⟨c, ℓ, hℓ, ?_⟩
  intro σ B
  let j : ρ.IntertwiningMap σ := c.coefficientL2Intertwiner hsq.1.1 ℓ.val μ hL2
  let b : InvariantPositiveForm ρ := c.coefficientL2Form hsq.1.1 ℓ.val μ hL2 hℓ
  have hf : ∀ v w, B.inner (j v) (j w) = b.inner v w := fun _ _ => rfl
  let e := b.completedIsometry B j hf
  let R := b.completedRange B j hf
  have he := b.completedIsometry_completedRepresentation B j hf
  have hrange : Set.range e = (R : Set B.HilbertCompletion) :=
    (b.coe_completedRange B j hf).symm
  refine ⟨j, b, e, R, fun _ => rfl, fun _ _ => rfl, b.completedIsometry_toHilbert B j hf, he,
    hrange, b.isClosed_completedRange B j hf,
    B.continuous_completedOrbit (Induction.centralL2Representation_smooth _ _ _),
    closed_irreducible_range e he R hrange (completion_closed_irreducible hcofinal hsq.1 hI b),
    smooth_range_image (toHilbertIntertwiner b) (completion_smooth_recovery hcofinal hsq.1 b)
      e he R hrange⟩

end Langlands
