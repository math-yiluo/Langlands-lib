import Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction
import Langlands.ClassField.Global.IdeleArchimedean

/-! # Weak approximation at finitely many finite places and all infinite places -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open Langlands.ClassField.Global
open scoped NumberField

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The absolute values of `K` at the finite places in `S` and at all infinite places. -/
def mixedAbv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    S ⊕ InfinitePlace K → AbsoluteValue K ℝ :=
  Sum.elim (fun p => NumberField.HeightOneSpectrum.adicAbv K p.1) (fun w => w.1)

theorem mixedAbv_isNontrivial (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : S ⊕ InfinitePlace K) : (mixedAbv S i).IsNontrivial := by
  rcases i with p | w
  · exact finiteAdicAbv_isNontrivial p.1
  · exact w.isNontrivial

/-- A finite absolute value is never equivalent to an infinite one: they differ at `2`. -/
theorem finiteAdicAbv_not_isEquiv_infinitePlace (p : HeightOneSpectrum (𝓞 K))
    (w : InfinitePlace K) :
    ¬(NumberField.HeightOneSpectrum.adicAbv K p).IsEquiv w.1 := by
  intro h
  have h1 := NumberField.HeightOneSpectrum.adicAbv_natCast_le_one K p 2
  rw [h.le_one_iff] at h1
  have h2 := w.map_natCast 2
  change w ((2 : ℕ) : K) ≤ 1 at h1
  rw [h2] at h1
  norm_num at h1

theorem mixedAbv_pairwise_not_isEquiv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Pairwise fun i j => ¬(mixedAbv S i).IsEquiv (mixedAbv S j) := by
  rintro (p | w) (q | w') hne h
  · exact hne (congrArg Sum.inl (Subtype.ext ((finiteAdicAbv_isEquiv_iff p.1 q.1).mp h)))
  · exact finiteAdicAbv_not_isEquiv_infinitePlace p.1 w' h
  · exact finiteAdicAbv_not_isEquiv_infinitePlace q.1 w h.symm
  · exact hne (congrArg Sum.inr (InfinitePlace.eq_iff_isEquiv.mpr h))

/-- Abstract weak approximation for the places in `S` together with all infinite places. -/
theorem denseRange_algebraMap_mixedAbv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (algebraMap K ((i : S ⊕ InfinitePlace K) → WithAbs (mixedAbv S i))) :=
  AbsoluteValue.denseRange_algebraMap_pi (mixedAbv_isNontrivial S)
    (mixedAbv_pairwise_not_isEquiv S)

/-- Weak approximation in the completions: an element of `K` lies in prescribed nonempty open
sets of the completions at the finite places in `S` and at every infinite place. -/
theorem exists_algebraMap_mem_open (S : Finset (HeightOneSpectrum (𝓞 K)))
    (A : ∀ p : S, Set (p.1.adicCompletion K)) (hA : ∀ p, IsOpen (A p))
    (hA' : ∀ p, (A p).Nonempty)
    (B : ∀ w : InfinitePlace K, Set w.Completion) (hB : ∀ w, IsOpen (B w))
    (hB' : ∀ w, (B w).Nonempty) :
    ∃ x : K, (∀ p, algebraMap K (p.1.adicCompletion K) x ∈ A p) ∧
      ∀ w, algebraMap K w.Completion x ∈ B w := by
  let O : ∀ i : S ⊕ InfinitePlace K, Set (WithAbs (mixedAbv S i)) := fun i =>
    match i with
    | .inl p => finiteWithAbsEmbedding p.1 ⁻¹' A p
    | .inr w => (fun y : WithAbs w.1 => (y : w.Completion)) ⁻¹' B w
  have hO : IsOpen (Set.pi Set.univ O) := by
    apply isOpen_set_pi Set.finite_univ
    rintro (p | w) -
    · exact (hA p).preimage (finiteWithAbsEmbedding_isometry p.1).continuous
    · exact (hB w).preimage (InfinitePlace.Completion.continuous_coe w)
  have hO' : (Set.pi Set.univ O).Nonempty := by
    apply Set.univ_pi_nonempty_iff.mpr
    rintro (p | w)
    · exact (finiteWithAbsEmbedding_denseRange p.1).exists_mem_open (hA p) (hA' p)
    · exact (InfinitePlace.Completion.denseRange_coe w).exists_mem_open (hB w) (hB' w)
  obtain ⟨x, hx⟩ := (denseRange_algebraMap_mixedAbv S).exists_mem_open hO hO'
  exact ⟨x, fun p => hx (.inl p) (Set.mem_univ _), fun w => hx (.inr w) (Set.mem_univ _)⟩

/-- In a topological field, the nonzero `z` with `z⁻¹ c` in the interior of `U` form an open
set; it contains `c` when `U` is a neighbourhood of `1`. -/
theorem isOpen_image_val_inv_mul_mem {F : Type*} [Field F] [TopologicalSpace F]
    [IsTopologicalDivisionRing F] [T1Space F] (c : Fˣ) (U : Set Fˣ) :
    IsOpen (Units.val '' {u : Fˣ | u⁻¹ * c ∈ interior U}) := by
  have hrange : Set.range (Units.val : Fˣ → F) = {0}ᶜ := by
    ext z
    rw [Set.mem_compl_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hz => ⟨Units.mk0 z hz, rfl⟩⟩
  have he : IsOpenEmbedding (Units.val : Fˣ → F) :=
    ⟨Units.isEmbedding_val₀, hrange ▸ isOpen_compl_singleton⟩
  exact he.isOpenMap _ (isOpen_interior.preimage (continuous_inv.mul continuous_const))

theorem mem_image_val_inv_mul_mem {F : Type*} [Field F] [TopologicalSpace F]
    (c : Fˣ) {U : Set Fˣ} (hU : U ∈ 𝓝 1) :
    (c : F) ∈ Units.val '' {u : Fˣ | u⁻¹ * c ∈ interior U} :=
  ⟨c, show c⁻¹ * c ∈ interior U by
    rw [inv_mul_cancel]
    exact mem_interior_iff_mem_nhds.mpr hU, rfl⟩

/-- Weak approximation for ideles: up to a principal idele, an idele lies in prescribed
neighbourhoods of `1` at the finite places in `S` and at every infinite place. -/
theorem exists_principal_inv_mul_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : IdeleGroup (𝓞 K) K) (U : ∀ p : HeightOneSpectrum (𝓞 K), Set (p.adicCompletion K)ˣ)
    (hU : ∀ p ∈ S, U p ∈ 𝓝 1) (V : ∀ w : InfinitePlace K, Set w.Completionˣ)
    (hV : ∀ w, V w ∈ 𝓝 1) :
    ∃ α : Kˣ,
      (∀ p ∈ S, ideleCoordinate p ((IdeleGroup.unitEmbedding (𝓞 K) K α)⁻¹ * a) ∈ U p) ∧
      ∀ w, ideleInfiniteCoordinate w ((IdeleGroup.unitEmbedding (𝓞 K) K α)⁻¹ * a) ∈ V w := by
  obtain ⟨x, hxA, hxB⟩ := exists_algebraMap_mem_open S
    (fun p => Units.val '' {u | u⁻¹ * ideleCoordinate p.1 a ∈ interior (U p.1)})
    (fun p => isOpen_image_val_inv_mul_mem _ _)
    (fun p => ⟨_, mem_image_val_inv_mul_mem _ (hU p.1 p.2)⟩)
    (fun w => Units.val '' {u | u⁻¹ * ideleInfiniteCoordinate w a ∈ interior (V w)})
    (fun w => isOpen_image_val_inv_mul_mem _ _)
    (fun w => ⟨_, mem_image_val_inv_mul_mem _ (hV w)⟩)
  have hx0 : x ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    obtain ⟨u, -, hu⟩ := hxB w
    rintro rfl
    exact u.ne_zero (hu.trans (map_zero _))
  refine ⟨Units.mk0 x hx0, fun p hp => ?_, fun w => ?_⟩
  · obtain ⟨u, hu, hux⟩ := hxA ⟨p, hp⟩
    have hcoord : ideleCoordinate p (IdeleGroup.unitEmbedding (𝓞 K) K (Units.mk0 x hx0)) = u :=
      Units.ext (hux.symm)
    rw [map_mul, map_inv, hcoord]
    exact interior_subset hu
  · obtain ⟨u, hu, hux⟩ := hxB w
    have hcoord :
        ideleInfiniteCoordinate w (IdeleGroup.unitEmbedding (𝓞 K) K (Units.mk0 x hx0)) = u :=
      Units.ext (hux.symm)
    rw [map_mul, map_inv, hcoord]
    exact interior_subset hu

end Langlands.Global.AdelicFunctoriality
