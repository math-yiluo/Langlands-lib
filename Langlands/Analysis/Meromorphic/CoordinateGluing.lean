import Langlands.Analysis.Meromorphic.ContinuationUniqueness
import Langlands.Analysis.Meromorphic.LinearCoordinates
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

/-! # Gluing and restricting meromorphic functions in linear coordinates

Elementary facts about the meromorphic functions of `Langlands.Analysis.Meromorphic`
(Bernstein–Lapid §3.1):

* meromorphy on `ℂᵐ` is preserved by complex linear changes of coordinates, so meromorphy in
  one linear coordinate system of a finite-dimensional space is meromorphy in coordinates;
* a function that agrees with a meromorphic function on an open dense part of its domain of
  holomorphy is meromorphic with that smaller domain;
* entire functions are meromorphic with domain the whole space;
* a family of scalar functions on `ℂᵐ` which near every point is meromorphic with some local
  domain of holomorphy (and local denominators independent of the member of the family) is
  meromorphic with one global domain of holomorphy, namely the set of points near which every
  member is holomorphic;
* local data of this kind are obtained by evaluating a meromorphic function on an open subset
  of `ℂᵐ` with values in a topological vector space at continuous linear forms. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open scoped Manifold Topology
open Set

section Flat

variable {m : ℕ}

/-- On `ℂᵐ`, scalar differentiability gives holomorphy in the weak sense. -/
theorem isHolomorphicOn_of_differentiableOn {f : (Fin m → ℂ) → ℂ} {U : Set (Fin m → ℂ)}
    (h : DifferentiableOn ℂ f U) : IsHolomorphicOn 𝓘(ℂ, Fin m → ℂ) f U := fun μ =>
  mdifferentiableOn_iff_differentiableOn.2 (μ.differentiable.comp_differentiableOn h)

/-- A scalar holomorphic function on `ℂᵐ` is differentiable. -/
theorem differentiableOn_of_isHolomorphicOn {f : (Fin m → ℂ) → ℂ} {U : Set (Fin m → ℂ)}
    (h : IsHolomorphicOn 𝓘(ℂ, Fin m → ℂ) f U) : DifferentiableOn ℂ f U :=
  mdifferentiableOn_iff_differentiableOn.1 (h (ContinuousLinearMap.id ℂ ℂ))

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- Meromorphy on `ℂᵐ` is preserved by complex linear changes of coordinates. -/
theorem IsMeromorphicOn.comp_continuousLinearEquiv {n : ℕ} {f : (Fin m → ℂ) → V}
    {U : Set (Fin m → ℂ)} (hf : IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) f U)
    (T : (Fin n → ℂ) ≃L[ℂ] (Fin m → ℂ)) :
    IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (f ∘ T) (T ⁻¹' U) := by
  obtain ⟨hUo, hUd, hhol, hloc⟩ := hf
  refine ⟨hUo.preimage T.continuous, hUd.preimage T.toHomeomorph.isOpenMap, fun μ => ?_,
    fun s₀ => ?_⟩
  · have h := mdifferentiableOn_iff_differentiableOn.1 (hhol μ)
    exact mdifferentiableOn_iff_differentiableOn.2
      (h.comp T.differentiable.differentiableOn (mapsTo_preimage _ _))
  · obtain ⟨W, hWo, hWc, hsW, g, h, hg, ⟨s₁, hs₁W, hs₁⟩, hh, hgh⟩ := hloc (T s₀)
    refine ⟨T ⁻¹' W, hWo.preimage T.continuous, ?_, hsW, g ∘ T, h ∘ T, ?_,
      ⟨T.symm s₁, by simpa using hs₁W, by simpa using hs₁⟩, fun μ => ?_, fun s hs => hgh _ hs⟩
    · rw [← T.image_symm_eq_preimage]
      exact hWc.image _ T.symm.continuous.continuousOn
    · exact mdifferentiableOn_iff_differentiableOn.2
        ((mdifferentiableOn_iff_differentiableOn.1 hg).comp T.differentiable.differentiableOn
          (mapsTo_preimage _ _))
    · exact mdifferentiableOn_iff_differentiableOn.2
        ((mdifferentiableOn_iff_differentiableOn.1 (hh μ)).comp
          T.differentiable.differentiableOn (mapsTo_preimage _ _))

/-- A function that agrees with a meromorphic function on an open dense part `U` of its domain
of holomorphy is meromorphic with domain of holomorphy `U`. -/
theorem IsMeromorphicOn.congr_mono {f f' : (Fin m → ℂ) → V} {U U' : Set (Fin m → ℂ)}
    (hf' : IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) f' U') (hUo : IsOpen U) (hUd : Dense U)
    (hUU' : U ⊆ U') (heq : EqOn f f' U) : IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) f U := by
  obtain ⟨-, -, hhol, hloc⟩ := hf'
  refine ⟨hUo, hUd, fun μ => ((hhol μ).mono hUU').congr fun s hs => by rw [heq hs], fun s₀ => ?_⟩
  obtain ⟨W, hWo, hWc, hsW, g, h, hg, hg0, hh, hgh⟩ := hloc s₀
  exact ⟨W, hWo, hWc, hsW, g, h, hg, hg0, hh, fun s hs => by
    rw [heq hs.1]
    exact hgh s ⟨hUU' hs.1, hs.2⟩⟩

end Flat

section Coordinates

variable {X : Type*} [AddCommGroup X] [Module ℂ X]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- A subset of a complex vector space is open and dense in linear coordinates when its preimage
under every complex linear isomorphism `ℂⁿ ≃ X` is open and dense. -/
def IsOpenDenseInCoordinates (U : Set X) : Prop :=
  ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X), IsOpen (e ⁻¹' U) ∧ Dense (e ⁻¹' U)

/-- A domain of holomorphy in coordinates is open and dense in coordinates. -/
theorem IsMeromorphicInCoordinatesOn.isOpenDenseInCoordinates {f : X → V} {U : Set X}
    (hf : IsMeromorphicInCoordinatesOn f U) : IsOpenDenseInCoordinates U := fun n e =>
  ⟨(hf.2 n e).1, (hf.2 n e).2.1⟩

/-- The intersection of two sets open and dense in coordinates. -/
theorem IsOpenDenseInCoordinates.inter {U U' : Set X} (hU : IsOpenDenseInCoordinates U)
    (hU' : IsOpenDenseInCoordinates U') : IsOpenDenseInCoordinates (U ∩ U') := fun n e => by
  rw [preimage_inter]
  exact ⟨(hU n e).1.inter (hU' n e).1, (hU n e).2.inter_of_isOpen_left (hU' n e).2 (hU n e).1⟩

/-- The union of a set open and dense in coordinates with a set open in coordinates. -/
theorem IsOpenDenseInCoordinates.union_isOpen {U O : Set X} (hU : IsOpenDenseInCoordinates U)
    (hO : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X), IsOpen (e ⁻¹' O)) :
    IsOpenDenseInCoordinates (U ∪ O) := fun n e => by
  rw [preimage_union]
  exact ⟨(hU n e).1.union (hO n e), (hU n e).2.mono subset_union_left⟩

/-- A finite intersection of sets open and dense in coordinates. -/
theorem isOpenDenseInCoordinates_iInter {k : ℕ} {U : Fin k → Set X}
    (hU : ∀ j, IsOpenDenseInCoordinates (U j)) : IsOpenDenseInCoordinates (⋂ j, U j) :=
  fun n e => by
    rw [preimage_iInter]
    exact ⟨isOpen_iInter_of_finite fun j => (hU j n e).1,
      dense_iInter_of_isOpen (fun j => (hU j n e).1) fun j => (hU j n e).2⟩

/-- Meromorphy in one linear coordinate system of a finite-dimensional space is meromorphy in
coordinates. -/
theorem isMeromorphicInCoordinatesOn_of_coordinates [FiniteDimensional ℂ X] {m : ℕ}
    (e₀ : (Fin m → ℂ) ≃ₗ[ℂ] X) {f : X → V} {U : Set X}
    (h : IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (f ∘ e₀) (e₀ ⁻¹' U)) :
    IsMeromorphicInCoordinatesOn f U := by
  refine ⟨inferInstance, fun n e => ?_⟩
  let T : (Fin n → ℂ) ≃L[ℂ] (Fin m → ℂ) := (e.trans e₀.symm).toContinuousLinearEquiv
  have h1 : f ∘ e = (f ∘ e₀) ∘ T := by
    funext s
    simp [T]
  have h2 : e ⁻¹' U = T ⁻¹' (e₀ ⁻¹' U) := by
    ext s
    simp [T]
  rw [h1, h2]
  exact h.comp_continuousLinearEquiv T

/-- A function that agrees with a function meromorphic in coordinates on a part `U` of its
domain of holomorphy that is open and dense in coordinates is meromorphic in coordinates with
domain `U`. -/
theorem IsMeromorphicInCoordinatesOn.congr_mono {f f' : X → V} {U U' : Set X}
    (hf' : IsMeromorphicInCoordinatesOn f' U') (hU : IsOpenDenseInCoordinates U)
    (hUU' : U ⊆ U') (heq : EqOn f f' U) : IsMeromorphicInCoordinatesOn f U :=
  ⟨hf'.1, fun n e => (hf'.2 n e).congr_mono (hU n e).1 (hU n e).2 (preimage_mono hUU')
    fun _ hs => heq hs⟩

/-- Entire functions are meromorphic in coordinates with domain the whole space. -/
theorem isMeromorphicInCoordinatesOn_univ [FiniteDimensional ℂ X] {f : X → ℂ}
    (hf : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X), Differentiable ℂ (f ∘ e)) :
    IsMeromorphicInCoordinatesOn f univ := by
  refine ⟨inferInstance, fun n e => ?_⟩
  rw [preimage_univ]
  refine ⟨isOpen_univ, dense_univ, isHolomorphicOn_of_differentiableOn (hf n e).differentiableOn,
    fun s₀ => ⟨univ, isOpen_univ, isConnected_univ, mem_univ _, fun _ => 1, f ∘ e,
      mdifferentiableOn_const, ⟨s₀, mem_univ _, one_ne_zero⟩,
      isHolomorphicOn_of_differentiableOn (hf n e).differentiableOn, fun s _ => one_smul ℂ _⟩⟩

end Coordinates

section Gluing

variable {m : ℕ} {ι : Type*}

/-- Local meromorphic data at `s₀` for a family `φ i` of functions on `ℂᵐ`: an open set `D` on
which every `φ i` is holomorphic, and an open connected neighbourhood `W` of `s₀` in the closure
of `D` with a holomorphic scalar `q`, not identically zero on `W`, such that every `q φ i`
agrees on `D ∩ W` with a function holomorphic on `W`. -/
def HasLocalMeromorphicData (φ : ι → (Fin m → ℂ) → ℂ) (s₀ : Fin m → ℂ) : Prop :=
  ∃ D W : Set (Fin m → ℂ), IsOpen D ∧ (∀ i, DifferentiableOn ℂ (φ i) D) ∧ IsOpen W ∧
    IsConnected W ∧ s₀ ∈ W ∧ W ⊆ closure D ∧
    ∃ q : (Fin m → ℂ) → ℂ, DifferentiableOn ℂ q W ∧ (∃ s ∈ W, q s ≠ 0) ∧
      ∀ i, ∃ h : (Fin m → ℂ) → ℂ, DifferentiableOn ℂ h W ∧ ∀ s ∈ D ∩ W, q s * φ i s = h s

/-- Gluing: a family with local meromorphic data at every point is meromorphic with one domain
of holomorphy, the set of points near which every member of the family is holomorphic. -/
theorem exists_isMeromorphicOn_of_local {φ : ι → (Fin m → ℂ) → ℂ}
    (hφ : ∀ s₀, HasLocalMeromorphicData φ s₀) :
    ∃ U : Set (Fin m → ℂ), ∀ i, IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (φ i) U := by
  set U : Set (Fin m → ℂ) :=
    {s | ∃ O : Set (Fin m → ℂ), IsOpen O ∧ s ∈ O ∧ ∀ i, DifferentiableOn ℂ (φ i) O} with hU
  have hUo : IsOpen U := by
    rw [isOpen_iff_forall_mem_open]
    rintro s ⟨O, hOo, hsO, hO⟩
    exact ⟨O, fun t ht => ⟨O, hOo, ht, hO⟩, hOo, hsO⟩
  have hsub : ∀ {D : Set (Fin m → ℂ)}, IsOpen D → (∀ i, DifferentiableOn ℂ (φ i) D) → D ⊆ U :=
    fun hDo hD s hs => ⟨_, hDo, hs, hD⟩
  have hdiff : ∀ i, DifferentiableOn ℂ (φ i) U := by
    rintro i s ⟨O, hOo, hsO, hO⟩
    exact ((hO i).differentiableAt (hOo.mem_nhds hsO)).differentiableWithinAt
  have hUd : Dense U := by
    intro s₀
    obtain ⟨D, W, hDo, hD, -, -, hs₀W, hWD, -⟩ := hφ s₀
    exact closure_mono (hsub hDo hD) (hWD hs₀W)
  refine ⟨U, fun i => ⟨hUo, hUd, isHolomorphicOn_of_differentiableOn (hdiff i), fun s₀ => ?_⟩⟩
  obtain ⟨D, W, hDo, hD, hWo, hWc, hs₀W, hWD, q, hq, hq0, hqh⟩ := hφ s₀
  obtain ⟨h, hh, hqφ⟩ := hqh i
  refine ⟨W, hWo, hWc, hs₀W, q, h, mdifferentiableOn_iff_differentiableOn.2 hq, hq0,
    isHolomorphicOn_of_differentiableOn hh, ?_⟩
  have hcl : U ∩ W ⊆ closure (D ∩ W) := by
    intro s hs
    have := hWo.inter_closure ⟨hs.2, hWD hs.2⟩
    rwa [inter_comm] at this
  intro s hs
  refine EqOn.of_subset_closure (s := D ∩ W) (t := U ∩ W) (f := fun s => q s * φ i s) (g := h)
    (fun t ht => hqφ t ht) ?_ ?_ (fun t ht => ⟨hsub hDo hD ht.1, ht.2⟩) hcl hs
  · exact ((hq.mono inter_subset_right).continuousOn).mul
      ((hdiff i).mono inter_subset_left).continuousOn
  · exact (hh.mono inter_subset_right).continuousOn

end Gluing

section Evaluation

variable {m : ℕ} {ι : Type*} {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

open Classical in
theorem extendOpens_val (W : TopologicalSpace.Opens (Fin m → ℂ)) (f : W → ℂ) (t : W) :
    extendOpens (B := W) f t = f t := by
  simp [extendOpens]

/-- Holomorphy on an open subset of `ℂᵐ`, as a manifold, gives differentiability of the
extension by zero. -/
theorem differentiableAt_extendOpens {W : TopologicalSpace.Opens (Fin m → ℂ)} {f : W → ℂ}
    {t : W} (h : MDifferentiableAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, ℂ) f t) :
    DifferentiableAt ℂ (extendOpens (B := W) f) t := by
  have hf : f = extendOpens (B := W) f ∘ Subtype.val := funext fun t => (extendOpens_val W f t).symm
  rw [hf] at h
  rw [← mdifferentiableAt_iff_differentiableAt]
  exact (differentiableWithinAt_localInvariantProp.liftPropAt_iff_comp_subtype_val _ t).2 h

/-- Evaluating a meromorphic function on an open subset `W` of `ℂᵐ` with values in a
topological vector space at continuous linear forms gives local meromorphic data at every point
of `W` for every family of scalar functions that agree with these evaluations on the domain of
holomorphy. -/
theorem hasLocalMeromorphicData_of_isMeromorphicOn {W : TopologicalSpace.Opens (Fin m → ℂ)}
    {f : W → V} {D : Set W} (hf : IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) f D) (ev : ι → V →L[ℂ] ℂ)
    {φ : ι → (Fin m → ℂ) → ℂ} (hφ : ∀ t ∈ D, ∀ i, ev i (f t) = φ i t) {s₀ : Fin m → ℂ}
    (hs₀ : s₀ ∈ W) : HasLocalMeromorphicData φ s₀ := by
  obtain ⟨hDo, hDd, hhol, hloc⟩ := hf
  have hopen : ∀ {S : Set W}, IsOpen S → IsOpen (Subtype.val '' S) := fun hS =>
    W.isOpen.isOpenMap_subtype_val _ hS
  have hφD : ∀ i, DifferentiableOn ℂ (φ i) (Subtype.val '' D) := by
    intro i
    have h := differentiableOn_extendOpens hDo (hhol (ev i))
    rintro _ ⟨t, ht, rfl⟩
    refine ((h _ ⟨t, ht, rfl⟩).differentiableAt ((hopen hDo).mem_nhds ⟨t, ht, rfl⟩)).congr_of_eventuallyEq
      ?_ |>.differentiableWithinAt
    filter_upwards [(hopen hDo).mem_nhds ⟨t, ht, rfl⟩]
    rintro _ ⟨t', ht', rfl⟩
    rw [extendOpens_val, hφ t' ht' i]
  obtain ⟨W', hW'o, hW'c, hsW', g, h, hg, ⟨t₁, ht₁, hg₁⟩, hh, hgh⟩ := hloc ⟨s₀, hs₀⟩
  refine ⟨Subtype.val '' D, Subtype.val '' W', hopen hDo, hφD, hopen hW'o,
    hW'c.image _ continuous_subtype_val.continuousOn, ⟨_, hsW', rfl⟩, ?_, extendOpens (B := W) g,
    differentiableOn_extendOpens hW'o hg, ⟨t₁, ⟨t₁, ht₁, rfl⟩, by rwa [extendOpens_val]⟩,
    fun i => ⟨extendOpens (B := W) (fun t => ev i (h t)), differentiableOn_extendOpens hW'o (hh (ev i)),
      ?_⟩⟩
  · rintro _ ⟨t, -, rfl⟩
    exact image_closure_subset_closure_image continuous_subtype_val ⟨t, hDd t, rfl⟩
  · rintro _ ⟨⟨t, ht, rfl⟩, ⟨t', ht', htt'⟩⟩
    obtain rfl : t' = t := Subtype.ext htt'
    rw [extendOpens_val, extendOpens_val, ← hφ t' ht i, ← hgh t' ⟨ht, ht'⟩, map_smul, smul_eq_mul]

end Evaluation

end Langlands.Analysis.Meromorphic

namespace Langlands.Global

open Langlands.Analysis.Meromorphic

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- The whole space is open and dense in coordinates. -/
theorem isOpenDenseInCoordinates_univ : IsOpenDenseInCoordinates (Set.univ : Set X) :=
  fun n e => by
    rw [Set.preimage_univ]
    exact ⟨isOpen_univ, dense_univ⟩

/-- A finite intersection of sets open and dense in coordinates, over any finite index type. -/
theorem isOpenDenseInCoordinates_iInter_of_finite {κ : Type*} [Finite κ] {U : κ → Set X}
    (hU : ∀ j, IsOpenDenseInCoordinates (U j)) : IsOpenDenseInCoordinates (⋂ j, U j) :=
  fun n e => by
    rw [Set.preimage_iInter]
    exact ⟨isOpen_iInter_of_finite fun j => (hU j n e).1,
      dense_iInter_of_isOpen (fun j => (hU j n e).1) fun j => (hU j n e).2⟩

end Langlands.Global
