import Langlands.TraceFormula.IsotypicTrace.OccurrenceTrace
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.BaseChange.TwistedCharacter.Basic
import Langlands.HarmonicAnalysis.Distribution.RenardEssentialProductsKernels

/-!
# Isotypy and trace factorization from one local occurrence (abstract form)

Let `π` be an inner-product-preserving action of a group `A` on a Hilbert space `E` with no
closed invariant subspaces other than `⊥` and `⊤`, and let `ι : Gv →* A` be a homomorphism
from a totally disconnected locally compact second countable group such that every element of
`A` is `ι y * c` with `c` commuting with the image of `ι`, and such that the local orbits
`y ↦ π (ι y) x` are continuous. Suppose an irreducible admissible representation `ρ` of `Gv`
has a nonzero equivariant linear map `j₀ : V → E`. This module proves:

* every smooth irreducible representation of `Gv` with a nonzero equivariant linear map into
  `E` is isomorphic to `ρ` (`isotypic_of_occurrence`);
* there is one functional `C` such that for every test function `fv` on `Gv` and every
  bounded operator `Y` commuting with `Gv`, if `X ∘ Y` is trace class, where `X` is the Bochner
  integral of `fv` against the local action, its trace is `Character.distribution fv * C Y`
  (`exists_trace_factorization`);
* for an injective bounded operator `I` with `I ∘ π a = π (Θ a) ∘ I`, where `Θ` is an
  automorphism of `A` restricting to a topological automorphism `θv` of `Gv`, there are a
  bijective `Av : V → V` with `Av ∘ ρ y = ρ (θv y) ∘ Av` and one functional `C` with the
  analogous identity for `X ∘ Y ∘ I` and `twistedDistribution Av`
  (`exists_twisted_trace_factorization`).
-/

noncomputable section

open MeasureTheory Langlands.HarmonicAnalysis Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula.IsotypicTrace

universe uA uG uE uV uW

section Schur

variable {Gv : Type uG} [Group Gv] [TopologicalSpace Gv]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Gv V)

/-- Schur's lemma for an admissible irreducible representation, for linear maps. -/
theorem exists_eq_smul_of_commute (hρ : IsAdmissible ρ) (hirr : Representation.IsIrreducible ρ)
    (L : V →ₗ[ℂ] V) (hL : ∀ y x, L (ρ y x) = ρ y (L x)) : ∃ c : ℂ, ∀ x, L x = c • x := by
  obtain ⟨c, hc, -⟩ := admissibleSchur_scalarEndomorphism ρ hρ hirr
    (LinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ L hL)
  exact ⟨c, fun x => congrArg (fun t : ρ.IntertwiningMap ρ => t x) hc⟩

omit [TopologicalSpace Gv] in
/-- An irreducible representation has a nonzero vector. -/
theorem exists_ne_zero_of_isIrreducible (hirr : Representation.IsIrreducible ρ) :
    ∃ v : V, v ≠ 0 := by
  have := hirr
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ Gv) ρ.asModule
  exact exists_ne 0

end Schur

section Total

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- In a family of subspaces whose sum is dense, every nonzero vector has a nonzero inner
product with a vector of some member. -/
theorem exists_inner_ne_zero {ι : Type*} (W : ι → Submodule ℂ E)
    (htop : (⨆ i, W i).topologicalClosure = ⊤) (x : E) (hx : x ≠ 0) :
    ∃ i, ∃ y ∈ W i, inner ℂ y x ≠ 0 := by
  by_contra hnone
  push Not at hnone
  apply hx
  have hle : ⨆ i, W i ≤ (ℂ ∙ x)ᗮ := by
    apply iSup_le
    intro i y hy
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact inner_eq_zero_symm.mp (hnone i y hy)
  have hle' : (⨆ i, W i).topologicalClosure ≤ (ℂ ∙ x)ᗮ :=
    (⨆ i, W i).topologicalClosure_minimal hle (Submodule.isClosed_orthogonal _)
  rw [htop] at hle'
  have hxx := hle' (Submodule.mem_top (x := x))
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hxx
  exact inner_self_eq_zero.mp hxx

end Total

section Lift

variable {Gv : Type uG} [Group Gv] [TopologicalSpace Gv] [IsTopologicalGroup Gv]
  [MeasurableSpace Gv] [BorelSpace Gv] [T2Space Gv] [LocallyCompactSpace Gv]
  [TotallyDisconnectedSpace Gv] [SecondCountableTopology Gv]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (σ : Gv →* (E →L[ℂ] E))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Gv V)
variable {V' : Type uW} [AddCommGroup V'] [Module ℂ V']

/-- **Block lift.** The projection to the closure of an occurrence `j` of a linear map whose
values become fixed by open subgroups after applying `T` factors through `j`. -/
theorem exists_block_lift (μ : Measure Gv) [μ.IsHaarMeasure]
    (hσinner : ∀ y x x', inner ℂ (σ y x) (σ y x') = inner ℂ x x')
    (hσnorm : ∀ y x, ‖σ y x‖ = ‖x‖) (hσcont : ∀ x, Continuous fun y => σ y x)
    (hρ : IsAdmissible ρ) (j : V →ₗ[ℂ] E) (hj : ∀ y x, j (ρ y x) = σ y (j x))
    (hinj : Function.Injective j)
    [((LinearMap.range j).topologicalClosure).HasOrthogonalProjection]
    (k : V' →ₗ[ℂ] E) (T : E →L[ℂ] E)
    (hT : ∀ x, ∃ K : OpenSubgroup Gv, ∀ g ∈ K, σ g (T (k x)) = T (k x)) :
    ∃ Ψ : V' →ₗ[ℂ] V, ∀ x,
      j (Ψ x) = ((LinearMap.range j).topologicalClosure).starProjection (T (k x)) := by
  let W : Submodule ℂ E := (LinearMap.range j).topologicalClosure
  let Φ : V' →ₗ[ℂ] E := W.starProjection.toLinearMap ∘ₗ T.toLinearMap ∘ₗ k
  apply exists_linearMap_lift j hinj Φ
  intro x
  obtain ⟨K, hK⟩ := hT x
  apply mem_range_of_mem_closure_of_fixed σ ρ μ hσnorm hσcont hρ j hj K
  · exact W.starProjection_apply_mem _
  · intro g hg
    change σ g (W.starProjection (T (k x))) = W.starProjection (T (k x))
    rw [← starProjection_closureRange_commute σ ρ hσinner j hj, hK g hg]

omit [TopologicalSpace Gv] [IsTopologicalGroup Gv] [MeasurableSpace Gv] [BorelSpace Gv]
  [T2Space Gv] [LocallyCompactSpace Gv] [TotallyDisconnectedSpace Gv]
  [SecondCountableTopology Gv] [CompleteSpace E] in
/-- A lift through an injective equivariant map inherits (twisted) equivariance. -/
theorem lift_equivariant (j : V →ₗ[ℂ] E) (hj : ∀ y x, j (ρ y x) = σ y (j x))
    (hinj : Function.Injective j) (ρ' : Representation ℂ Gv V') (τ : Gv → Gv)
    (Ψ : V' →ₗ[ℂ] V) (Φ : V' → E) (hΨ : ∀ x, j (Ψ x) = Φ x)
    (hΦ : ∀ y x, Φ (ρ' y x) = σ (τ y) (Φ x)) : ∀ y x, Ψ (ρ' y x) = ρ (τ y) (Ψ x) := by
  intro y x
  apply hinj
  rw [hΨ, hΦ, hj, hΨ]

end Lift

section Integral

variable {Gv : Type uG} [Group Gv] [TopologicalSpace Gv] [IsTopologicalGroup Gv]
  [MeasurableSpace Gv] [BorelSpace Gv]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (σ : Gv →* (E →L[ℂ] E))

omit [IsTopologicalGroup Gv] in
/-- A bounded operator commuting with the local action commutes with its integral against a
test function. -/
theorem integral_commute (μ : Measure Gv) [IsFiniteMeasureOnCompacts μ]
    (hσcont : ∀ x, Continuous fun y => σ y x) (fv : SchwartzBruhat Gv) (X : E →L[ℂ] E)
    (hX : ∀ x, X x = ∫ y, fv y • σ y x ∂μ) (T : E →L[ℂ] E)
    (hT : ∀ y x, T (σ y x) = σ y (T x)) (x : E) : T (X x) = X (T x) := by
  rw [hX, hX, ← T.integral_comp_comm (testFunction_orbit_integrable σ μ hσcont fv x)]
  congr 1
  funext y
  rw [map_smul, hT]

/-- The integral of a left `K`-invariant test function against the local action has values
fixed by `K`. -/
theorem integral_fixed (μ : Measure Gv) [μ.IsHaarMeasure]
    (hσcont : ∀ x, Continuous fun y => σ y x) (fv : SchwartzBruhat Gv) (X : E →L[ℂ] E)
    (hX : ∀ x, X x = ∫ y, fv y • σ y x ∂μ) (K : OpenSubgroup Gv)
    (hfv : ∀ k ∈ K, ∀ y, fv (k * y) = fv y) (x : E) (k : Gv) (hk : k ∈ K) :
    σ k (X x) = X x := by
  rw [hX, ← (σ k).integral_comp_comm (testFunction_orbit_integrable σ μ hσcont fv x)]
  have h1 : (fun y => σ k (fv y • σ y x)) = fun y => fv y • σ (k * y) x := by
    funext y
    rw [map_smul, map_mul]
    rfl
  rw [h1]
  have h2 := integral_mul_left_eq_self (μ := μ) (fun y => fv (k⁻¹ * y) • σ y x) k
  simp only [← mul_assoc, inv_mul_cancel, one_mul] at h2
  rw [h2]
  congr 1
  funext y
  rw [hfv k⁻¹ (K.inv_mem hk) y]

end Integral

section Main

variable {A : Type uA} [Group A]
variable {Gv : Type uG} [Group Gv] [TopologicalSpace Gv] [IsTopologicalGroup Gv]
  [MeasurableSpace Gv] [BorelSpace Gv] [T2Space Gv] [LocallyCompactSpace Gv]
  [TotallyDisconnectedSpace Gv] [SecondCountableTopology Gv]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (π : A →* (E →L[ℂ] E)) (ι : Gv →* A)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Gv V)

omit [TopologicalSpace Gv] [IsTopologicalGroup Gv] [MeasurableSpace Gv] [BorelSpace Gv]
  [T2Space Gv] [LocallyCompactSpace Gv] [TotallyDisconnectedSpace Gv]
  [SecondCountableTopology Gv] in
/-- The data of a decomposition into closures of occurrences, with chosen occurrences. -/
theorem exists_occurrence_decomposition
    (hπinner : ∀ a x y, inner ℂ (π a x) (π a y) = inner ℂ x y)
    (hsplit : ∀ a, ∃ y c, a = ι y * c ∧ ∀ y', ι y' * c = c * ι y')
    (hirr : ∀ Q : Submodule ℂ E, IsClosed (Q : Set E) →
      (∀ a, ∀ x ∈ Q, π a x ∈ Q) → Q = ⊥ ∨ Q = ⊤)
    (hρirr : Representation.IsIrreducible ρ)
    (j₀ : V →ₗ[ℂ] E) (hj₀ : ∀ y x, j₀ (ρ y x) = π (ι y) (j₀ x)) (hj₀0 : j₀ ≠ 0) :
    ∃ (𝒜 : Set (Submodule ℂ E)) (J : 𝒜 → V →ₗ[ℂ] E),
      (∀ P : 𝒜, (∀ y x, J P (ρ y x) = π (ι y) (J P x)) ∧ Function.Injective (J P)) ∧
      IsHilbertSum ℂ (fun P : 𝒜 => (LinearMap.range (J P)).topologicalClosure)
        (fun P : 𝒜 => ((LinearMap.range (J P)).topologicalClosure).subtypeₗᵢ) ∧
      (⨆ P : 𝒜, (LinearMap.range (J P)).topologicalClosure).topologicalClosure = ⊤ := by
  obtain ⟨𝒜, hgood, hortho, htop⟩ :=
    exists_occurrence_hilbertSum π ρ hπinner ι hsplit hirr j₀ hj₀ hj₀0
  choose J hJ0 hJ hJP using fun P : 𝒜 => hgood P.1 P.2
  have hsup : (⨆ P : 𝒜, (LinearMap.range (J P)).topologicalClosure) = sSup 𝒜 := by
    rw [sSup_eq_iSup']
    exact iSup_congr fun P => (hJP P).symm
  refine ⟨𝒜, J, fun P => ⟨hJ P, injective_of_isIrreducible (π.comp ι) ρ hρirr (J P) (hJ P)
    (hJ0 P)⟩, ?_, by rw [hsup, htop]⟩
  refine IsHilbertSum.mkInternal _ ?_ ?_
  · rw [orthogonalFamily_iff_pairwise]
    intro P Q hPQ
    change (LinearMap.range (J P)).topologicalClosure ⟂ (LinearMap.range (J Q)).topologicalClosure
    rw [← hJP P, ← hJP Q]
    exact hortho P.2 Q.2 (fun h => hPQ (Subtype.ext h))
  · rw [hsup, htop]

/-- **Isotypy.** Every smooth irreducible representation of `Gv` with a nonzero equivariant
linear map into `E` is isomorphic to `ρ`. -/
theorem isotypic_of_occurrence (μ : Measure Gv) [μ.IsHaarMeasure]
    (hπinner : ∀ a x y, inner ℂ (π a x) (π a y) = inner ℂ x y)
    (hcont : ∀ x, Continuous fun y => π (ι y) x)
    (hsplit : ∀ a, ∃ y c, a = ι y * c ∧ ∀ y', ι y' * c = c * ι y')
    (hirr : ∀ Q : Submodule ℂ E, IsClosed (Q : Set E) →
      (∀ a, ∀ x ∈ Q, π a x ∈ Q) → Q = ⊥ ∨ Q = ⊤)
    (hρ : IsAdmissible ρ) (hρirr : Representation.IsIrreducible ρ)
    (j₀ : V →ₗ[ℂ] E) (hj₀ : ∀ y x, j₀ (ρ y x) = π (ι y) (j₀ x)) (hj₀0 : j₀ ≠ 0)
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V'] (ρ' : Representation ℂ Gv V')
    (hρ' : IsSmooth ρ') (hρ'irr : Representation.IsIrreducible ρ')
    (j : V' →ₗ[ℂ] E) (hj : ∀ y x, j (ρ' y x) = π (ι y) (j x)) (hj0 : j ≠ 0) :
    ∃ e : V' ≃ₗ[ℂ] V, ∀ y x, e (ρ' y x) = ρ y (e x) := by
  let σ : Gv →* (E →L[ℂ] E) := π.comp ι
  have hσinner : ∀ y x x', inner ℂ (σ y x) (σ y x') = inner ℂ x x' :=
    fun y => hπinner (ι y)
  have hσnorm : ∀ y x, ‖σ y x‖ = ‖x‖ :=
    fun y => (LinearMap.norm_map_iff_inner_map_map (σ y)).2 (hσinner y)
  obtain ⟨𝒜, J, hJ, -, htop⟩ :=
    exists_occurrence_decomposition π ι ρ hπinner hsplit hirr hρirr j₀ hj₀ hj₀0
  obtain ⟨x₀, hx₀⟩ : ∃ x, j x ≠ 0 := by
    by_contra h
    push Not at h
    exact hj0 (LinearMap.ext h)
  obtain ⟨P, z, hz, hzx⟩ := exists_inner_ne_zero _ htop (j x₀) hx₀
  obtain ⟨hJeq, hJinj⟩ := hJ P
  let jP := J P
  let W : Submodule ℂ E := (LinearMap.range jP).topologicalClosure
  have : CompleteSpace W := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hPx : W.starProjection (j x₀) ≠ 0 := by
    intro h0
    rw [Submodule.starProjection_apply_eq_zero_iff] at h0
    exact hzx (h0 z hz)
  obtain ⟨Ψ, hΨ⟩ := exists_block_lift σ ρ μ hσinner hσnorm hcont hρ jP hJeq hJinj j
    (ContinuousLinearMap.id ℂ E) (by
      intro x
      obtain ⟨K, hK⟩ := hρ' x
      refine ⟨K, fun g hg => ?_⟩
      change π (ι g) (j x) = j x
      rw [← hj]
      exact congrArg j (hK ⟨g, hg⟩))
  have hΨeq : ∀ y x, Ψ (ρ' y x) = ρ y (Ψ x) :=
    lift_equivariant σ ρ jP hJeq hJinj ρ' id Ψ
      (fun x => ((LinearMap.range jP).topologicalClosure).starProjection (j x))
      (fun x => by simpa using hΨ x) (by
        intro y x
        change _ = σ y _
        rw [hj, ← starProjection_closureRange_commute σ ρ hσinner jP hJeq]
        rfl)
  have hΨ0 : Ψ ≠ 0 := by
    intro h
    apply hPx
    have := hΨ x₀
    simp only [h, LinearMap.zero_apply, map_zero, ContinuousLinearMap.id_apply] at this
    exact this.symm
  have := hρirr
  have := hρ'irr
  let f : ρ'.IntertwiningMap ρ := LinearMap.intertwiningMap_of_isIntertwiningMap ρ' ρ Ψ hΨeq
  have hf0 : f ≠ 0 := by
    intro h
    apply hΨ0
    ext x
    exact congrArg (fun t : ρ'.IntertwiningMap ρ => t x) h
  have hbij := (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf0
  exact ⟨LinearEquiv.ofBijective Ψ hbij, hΨeq⟩

/-- **Trace factorization.** One functional `C` computes the traces of all trace-class
products `X ∘ Y`, where `X` integrates a test function against the local action and `Y`
commutes with the local action. -/
theorem exists_trace_factorization (μ : Measure Gv) [μ.IsHaarMeasure]
    (hπinner : ∀ a x y, inner ℂ (π a x) (π a y) = inner ℂ x y)
    (hcont : ∀ x, Continuous fun y => π (ι y) x)
    (hsplit : ∀ a, ∃ y c, a = ι y * c ∧ ∀ y', ι y' * c = c * ι y')
    (hirr : ∀ Q : Submodule ℂ E, IsClosed (Q : Set E) →
      (∀ a, ∀ x ∈ Q, π a x ∈ Q) → Q = ⊥ ∨ Q = ⊤)
    (hρ : IsAdmissible ρ) (hρirr : Representation.IsIrreducible ρ)
    (j₀ : V →ₗ[ℂ] E) (hj₀ : ∀ y x, j₀ (ρ y x) = π (ι y) (j₀ x)) (hj₀0 : j₀ ≠ 0) :
    ∃ C : (E →L[ℂ] E) → ℂ, ∀ (fv : SchwartzBruhat Gv) (X Y : E →L[ℂ] E),
      (∀ x, X x = ∫ y, fv y • π (ι y) x ∂μ) →
      (∀ y x, Y (π (ι y) x) = π (ι y) (Y x)) →
      IsTraceClass (X ∘L Y) →
      operatorTrace (X ∘L Y) = Character.distribution μ ρ hρ fv * C Y := by
  classical
  let σ : Gv →* (E →L[ℂ] E) := π.comp ι
  have hσinner : ∀ y x x', inner ℂ (σ y x) (σ y x') = inner ℂ x x' :=
    fun y => hπinner (ι y)
  have hσnorm : ∀ y x, ‖σ y x‖ = ‖x‖ :=
    fun y => (LinearMap.norm_map_iff_inner_map_map (σ y)).2 (hσinner y)
  obtain ⟨𝒜, J, hJ, hW, -⟩ :=
    exists_occurrence_decomposition π ι ρ hπinner hsplit hirr hρirr j₀ hj₀ hj₀0
  let W : 𝒜 → Submodule ℂ E := fun P => (LinearMap.range (J P)).topologicalClosure
  have hWc : ∀ P, CompleteSpace (W P) :=
    fun P => (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let coef : (E →L[ℂ] E) → 𝒜 → ℂ := fun Y P =>
    if h : ∃ c : ℂ, ∀ v, (W P).starProjection (Y (J P v)) = c • J P v then h.choose else 0
  refine ⟨fun Y => ∑' P, coef Y P, ?_⟩
  intro fv X Y hX hY hB
  obtain ⟨K, -, -, hKf⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance Gv {fv} ⊤
  have hfvK : fv ∈ Hecke.TestFunction.biInvariant K.toSubgroup K.toSubgroup :=
    hKf fv (by simp)
  have : Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  let H : Module.End ℂ V := Hecke.integratedAction μ ρ hρ.1 fv
  have hHK : LinearMap.range H ≤ fixedVectors ρ K.toSubgroup :=
    Hecke.integratedAction_range_le_fixedVectors μ ρ hρ.1 hfvK
  have hXj : ∀ (j : V →ₗ[ℂ] E), (∀ y x, j (ρ y x) = σ y (j x)) → ∀ v, X (j v) = j (H v) := by
    intro j hj v
    rw [hX, map_integratedAction σ ρ μ hcont hρ.1 j hj fv v]
    rfl
  apply operatorTrace_eq_mul_tsum W hW (X ∘L Y) hB (coef Y)
  intro P
  obtain ⟨hJeq, hJinj⟩ := hJ P
  obtain ⟨Ψ, hΨ⟩ := exists_block_lift σ ρ μ hσinner hσnorm hcont hρ (J P) hJeq hJinj (J P) Y
    (by
      intro x
      obtain ⟨L, hL⟩ := hρ.1 x
      refine ⟨L, fun g hg => ?_⟩
      change π (ι g) (Y (J P x)) = Y (J P x)
      rw [← hY, ← hJeq]
      exact congrArg (fun z => Y (J P z)) (hL ⟨g, hg⟩))
  have hΨeq : ∀ y x, Ψ (ρ y x) = ρ y (Ψ x) :=
    lift_equivariant σ ρ (J P) hJeq hJinj ρ id Ψ
      (fun x => (W P).starProjection (Y (J P x))) hΨ (by
        intro y x
        change _ = σ y _
        rw [hJeq, ← starProjection_closureRange_commute σ ρ hσinner (J P) hJeq]
        rw [hY]
        rfl)
  obtain ⟨c, hc⟩ := exists_eq_smul_of_commute ρ hρ hρirr Ψ hΨeq
  have hblock : ∀ v, (W P).starProjection (Y (J P v)) = c • J P v := by
    intro v
    rw [← hΨ, hc, map_smul]
  have hcoef : coef Y P = c := by
    have h : ∃ c : ℂ, ∀ v, (W P).starProjection (Y (J P v)) = c • J P v := ⟨c, hblock⟩
    simp only [coef]
    split_ifs
    obtain ⟨v₀, hv₀⟩ := exists_ne_zero_of_isIrreducible ρ hρirr
    have h1 := h.choose_spec v₀
    rw [hblock v₀] at h1
    have hne : J P v₀ ≠ 0 := fun h0 => hv₀ (hJinj (h0.trans (map_zero _).symm))
    exact (smul_left_injective ℂ hne h1).symm
  rw [hcoef]
  have hLK : LinearMap.range (c • H) ≤ fixedVectors ρ K.toSubgroup := by
    rintro _ ⟨v, rfl⟩
    exact Submodule.smul_mem _ c (hHK ⟨v, rfl⟩)
  rw [operatorTrace_compression_occurrence σ ρ μ hσinner hσnorm hcont hρ (J P) hJeq hJinj K
    (X ∘L Y) hB
    (fun x k hk => integral_fixed σ μ hcont fv X hX K (fun k hk y => hfvK.1 ⟨k, hk⟩ y) (Y x) k hk)
    (c • H) hLK (by
      intro v
      change (W P).starProjection (X (Y (J P v))) = J P (c • H v)
      rw [integral_commute σ μ hcont fv X hX (W P).starProjection
        (starProjection_closureRange_commute σ ρ hσinner (J P) hJeq), hblock, map_smul,
        hXj (J P) hJeq, map_smul])]
  have hon : FiniteRankEnd.onSubspace (c • H) (fixedVectors ρ K.toSubgroup) hLK =
      c • FiniteRankEnd.onSubspace H (fixedVectors ρ K.toSubgroup) hHK := by
    ext v
    rfl
  rw [hon, map_smul, smul_eq_mul, Character.distribution_eq_subspace μ ρ hρ fv _ hHK]

/-- **Twisted trace factorization.** For an injective bounded operator `I` with
`I ∘ π a = π (Θ a) ∘ I`, where `Θ ∘ ι = ι ∘ θv`, there are a bijective twisted intertwiner
`Av` of `ρ` and one functional `C` computing the traces of all trace-class products
`X ∘ Y ∘ I`. -/
theorem exists_twisted_trace_factorization (μ : Measure Gv) [μ.IsHaarMeasure]
    (hπinner : ∀ a x y, inner ℂ (π a x) (π a y) = inner ℂ x y)
    (hcont : ∀ x, Continuous fun y => π (ι y) x)
    (hsplit : ∀ a, ∃ y c, a = ι y * c ∧ ∀ y', ι y' * c = c * ι y')
    (hirr : ∀ Q : Submodule ℂ E, IsClosed (Q : Set E) →
      (∀ a, ∀ x ∈ Q, π a x ∈ Q) → Q = ⊥ ∨ Q = ⊤)
    (hρ : IsAdmissible ρ) (hρirr : Representation.IsIrreducible ρ)
    (j₀ : V →ₗ[ℂ] E) (hj₀ : ∀ y x, j₀ (ρ y x) = π (ι y) (j₀ x)) (hj₀0 : j₀ ≠ 0)
    (Θ : A →* A) (θv : Gv ≃ₜ* Gv) (hΘι : ∀ y, Θ (ι y) = ι (θv y))
    (I : E →L[ℂ] E) (hIinj : Function.Injective I) (hIcov : ∀ a x, I (π a x) = π (Θ a) (I x)) :
    ∃ Av : V →ₗ[ℂ] V, Function.Bijective Av ∧ (∀ y w, Av (ρ y w) = ρ (θv y) (Av w)) ∧
      ∃ C : (E →L[ℂ] E) → ℂ, ∀ (fv : SchwartzBruhat Gv) (X Y : E →L[ℂ] E),
        (∀ x, X x = ∫ y, fv y • π (ι y) x ∂μ) →
        (∀ y x, Y (π (ι y) x) = π (ι y) (Y x)) →
        IsTraceClass (X ∘L Y ∘L I) →
        operatorTrace (X ∘L Y ∘L I) =
          Langlands.BaseChange.twistedDistribution μ ρ hρ Av fv * C Y := by
  classical
  let σ : Gv →* (E →L[ℂ] E) := π.comp ι
  have hσinner : ∀ y x x', inner ℂ (σ y x) (σ y x') = inner ℂ x x' :=
    fun y => hπinner (ι y)
  have hσnorm : ∀ y x, ‖σ y x‖ = ‖x‖ :=
    fun y => (LinearMap.norm_map_iff_inner_map_map (σ y)).2 (hσinner y)
  obtain ⟨𝒜, J, hJ, hW, htop⟩ :=
    exists_occurrence_decomposition π ι ρ hπinner hsplit hirr hρirr j₀ hj₀ hj₀0
  let W : 𝒜 → Submodule ℂ E := fun P => (LinearMap.range (J P)).topologicalClosure
  have hWc : ∀ P, CompleteSpace (W P) :=
    fun P => (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  -- `I` carries vectors fixed by `K` to vectors fixed by `θv K`.
  have hIfix : ∀ (K : OpenSubgroup Gv) (z : E), (∀ g ∈ K, σ g z = z) →
      ∀ g ∈ K.comap θv.symm.toMonoidHom θv.symm.continuous, σ g (I z) = I z := by
    intro K z hz g hg
    have hg' : θv.symm g ∈ K := hg
    change π (ι g) (I z) = I z
    have h1 : ι g = Θ (ι (θv.symm g)) := by rw [hΘι, θv.apply_symm_apply]
    rw [h1, ← hIcov]
    exact congrArg I (hz _ hg')
  have hjfix : ∀ (j : V →ₗ[ℂ] E), (∀ y x, j (ρ y x) = σ y (j x)) →
      ∀ x, ∃ K : OpenSubgroup Gv, ∀ g ∈ K, σ g (j x) = j x := by
    intro j hj x
    obtain ⟨L, hL⟩ := hρ.1 x
    exact ⟨L, fun g hg => by rw [← hj]; exact congrArg j (hL ⟨g, hg⟩)⟩
  have hinj₀ := injective_of_isIrreducible σ ρ hρirr j₀ hj₀ hj₀0
  -- The twisted intertwiner `Av` from a nonzero block of `I`.
  obtain ⟨v₀, hv₀⟩ := exists_ne_zero_of_isIrreducible ρ hρirr
  have hIj : I (j₀ v₀) ≠ 0 := fun h => hv₀ (hinj₀ (hIinj (h.trans (map_zero I).symm) |>.trans
    (map_zero j₀).symm))
  obtain ⟨P₀, z, hz, hzx⟩ := exists_inner_ne_zero _ htop (I (j₀ v₀)) hIj
  obtain ⟨hJeq₀, hJinj₀⟩ := hJ P₀
  obtain ⟨α, hα⟩ := exists_block_lift σ ρ μ hσinner hσnorm hcont hρ (J P₀) hJeq₀ hJinj₀ j₀ I
    (by
      intro x
      obtain ⟨K, hK⟩ := hjfix j₀ hj₀ x
      exact ⟨_, hIfix K _ hK⟩)
  have hαeq : ∀ y x, α (ρ y x) = ρ (θv y) (α x) :=
    lift_equivariant σ ρ (J P₀) hJeq₀ hJinj₀ ρ θv α
      (fun x => (W P₀).starProjection (I (j₀ x))) hα (by
        intro y x
        rw [← starProjection_closureRange_commute σ ρ hσinner (J P₀) hJeq₀, hj₀]
        rw [hIcov, hΘι]
        rfl)
  have hα0 : α v₀ ≠ 0 := by
    intro h
    apply hzx
    have h1 := hα v₀
    rw [h, map_zero] at h1
    have h2 : I (j₀ v₀) ∈ (W P₀)ᗮ := by
      rw [← Submodule.starProjection_apply_eq_zero_iff]
      exact h1.symm
    exact h2 z hz
  have := hρirr
  have hαinj : Function.Injective α := by
    let N : Subrepresentation ρ := ⟨LinearMap.ker α, fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hαeq, hv, map_zero]⟩
    rcases eq_bot_or_eq_top N with hN | hN
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro v hv
      have : v ∈ N := hv
      rw [hN] at this
      exact this
    · exfalso
      apply hα0
      have : v₀ ∈ N := by rw [hN]; trivial
      exact this
  have hαsurj : Function.Surjective α := by
    let N : Subrepresentation ρ := ⟨LinearMap.range α, fun g v hv => by
      obtain ⟨x, rfl⟩ := hv
      exact ⟨ρ (θv.symm g) x, by rw [hαeq, θv.apply_symm_apply]⟩⟩
    rcases eq_bot_or_eq_top N with hN | hN
    · exfalso
      apply hα0
      have : α v₀ ∈ N := ⟨v₀, rfl⟩
      rw [hN] at this
      exact this
    · intro v
      have : v ∈ N := by rw [hN]; trivial
      exact this
  have hαbij : Function.Bijective α := ⟨hαinj, hαsurj⟩
  let αe : V ≃ₗ[ℂ] V := LinearEquiv.ofBijective α hαbij
  have hαe_symm : ∀ z x, αe.symm (ρ z x) = ρ (θv.symm z) (αe.symm x) := by
    intro z x
    apply hαinj
    change αe (αe.symm (ρ z x)) = α (ρ (θv.symm z) (αe.symm x))
    rw [hαeq, θv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact congrArg (ρ z) (αe.apply_symm_apply x).symm
  refine ⟨α, hαbij, hαeq, ?_⟩
  -- The functional.
  let coef : (E →L[ℂ] E) → 𝒜 → ℂ := fun Y P =>
    if h : ∃ c : ℂ, ∀ v, (W P).starProjection (Y (I (J P v))) = c • J P (α v)
    then h.choose else 0
  refine ⟨fun Y => ∑' P, coef Y P, ?_⟩
  intro fv X Y hX hY hB
  obtain ⟨K, -, -, hKf⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance Gv {fv} ⊤
  have hfvK : fv ∈ Hecke.TestFunction.biInvariant K.toSubgroup K.toSubgroup :=
    hKf fv (by simp)
  have : Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  let H : Module.End ℂ V := Hecke.integratedAction μ ρ hρ.1 fv
  have hHK : LinearMap.range H ≤ fixedVectors ρ K.toSubgroup :=
    Hecke.integratedAction_range_le_fixedVectors μ ρ hρ.1 hfvK
  have hHαK : LinearMap.range (H ∘ₗ α) ≤ fixedVectors ρ K.toSubgroup := by
    rintro _ ⟨v, rfl⟩
    exact hHK ⟨α v, rfl⟩
  have hXj : ∀ (j : V →ₗ[ℂ] E), (∀ y x, j (ρ y x) = σ y (j x)) → ∀ v, X (j v) = j (H v) := by
    intro j hj v
    rw [hX, map_integratedAction σ ρ μ hcont hρ.1 j hj fv v]
    rfl
  apply operatorTrace_eq_mul_tsum W hW (X ∘L Y ∘L I) hB (coef Y)
  intro P
  obtain ⟨hJeq, hJinj⟩ := hJ P
  obtain ⟨β, hβ⟩ := exists_block_lift σ ρ μ hσinner hσnorm hcont hρ (J P) hJeq hJinj (J P)
    (Y ∘L I) (by
      intro x
      obtain ⟨K', hK'⟩ := hjfix (J P) hJeq x
      refine ⟨K'.comap θv.symm.toMonoidHom θv.symm.continuous, fun g hg => ?_⟩
      change π (ι g) (Y (I (J P x))) = Y (I (J P x))
      rw [← hY]
      exact congrArg Y (hIfix K' _ hK' g hg))
  have hβeq : ∀ y x, β (ρ y x) = ρ (θv y) (β x) :=
    lift_equivariant σ ρ (J P) hJeq hJinj ρ θv β
      (fun x => (W P).starProjection ((Y ∘L I) (J P x))) hβ (by
        intro y x
        rw [← starProjection_closureRange_commute σ ρ hσinner (J P) hJeq, hJeq]
        change (W P).starProjection (Y (I (π (ι y) (J P x)))) =
          (W P).starProjection (π (ι (θv y)) (Y (I (J P x))))
        rw [hIcov, hΘι, hY])
  let L : V →ₗ[ℂ] V := β ∘ₗ αe.symm.toLinearMap
  have hLeq : ∀ y x, L (ρ y x) = ρ y (L x) := by
    intro y x
    change β (αe.symm (ρ y x)) = ρ y (β (αe.symm x))
    rw [hαe_symm, hβeq, θv.apply_symm_apply]
  obtain ⟨c, hc⟩ := exists_eq_smul_of_commute ρ hρ hρirr L hLeq
  have hβc : ∀ v, β v = c • α v := by
    intro v
    have h := hc (α v)
    change β (αe.symm (αe v)) = c • α v at h
    rwa [LinearEquiv.symm_apply_apply] at h
  have hblock : ∀ v, (W P).starProjection (Y (I (J P v))) = c • J P (α v) := by
    intro v
    have h := hβ v
    change J P (β v) = (W P).starProjection (Y (I (J P v))) at h
    rw [← h, hβc, map_smul]
  have hcoef : coef Y P = c := by
    have h : ∃ c : ℂ, ∀ v, (W P).starProjection (Y (I (J P v))) = c • J P (α v) :=
      ⟨c, hblock⟩
    simp only [coef]
    split_ifs
    have h1 := h.choose_spec v₀
    rw [hblock v₀] at h1
    have hne : J P (α v₀) ≠ 0 := fun h0 => hα0 (hJinj (h0.trans (map_zero _).symm))
    exact (smul_left_injective ℂ hne h1).symm
  rw [hcoef]
  have hLK : LinearMap.range (c • (H ∘ₗ α)) ≤ fixedVectors ρ K.toSubgroup := by
    rintro _ ⟨v, rfl⟩
    exact Submodule.smul_mem _ c (hHαK ⟨v, rfl⟩)
  rw [operatorTrace_compression_occurrence σ ρ μ hσinner hσnorm hcont hρ (J P) hJeq hJinj K
    (X ∘L Y ∘L I) hB
    (fun x k hk => integral_fixed σ μ hcont fv X hX K (fun k hk y => hfvK.1 ⟨k, hk⟩ y)
      (Y (I x)) k hk)
    (c • (H ∘ₗ α)) hLK (by
      intro v
      change (W P).starProjection (X (Y (I (J P v)))) = J P (c • H (α v))
      rw [integral_commute σ μ hcont fv X hX (W P).starProjection
        (starProjection_closureRange_commute σ ρ hσinner (J P) hJeq), hblock, map_smul,
        hXj (J P) hJeq, map_smul])]
  have hon : FiniteRankEnd.onSubspace (c • (H ∘ₗ α)) (fixedVectors ρ K.toSubgroup) hLK =
      c • FiniteRankEnd.onSubspace (H ∘ₗ α) (fixedVectors ρ K.toSubgroup) hHαK := by
    ext v
    rfl
  rw [hon, map_smul, smul_eq_mul, Langlands.BaseChange.twistedDistribution_apply,
    FiniteRankEnd.trace_eq_subspace _ (fixedVectors ρ K.toSubgroup) hHαK]
  rfl

end Main

end Langlands.TraceFormula.IsotypicTrace
