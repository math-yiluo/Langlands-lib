module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.RingTheory.RelativeDimension.Defs
public import StacksFrontier.Topology.Dimension.LocalKrullDim

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Basic properties of the relative dimension

Let `R → S` be a ring map and let `𝔮` be a prime of `S` lying over `𝔭`. The relative dimension
`dim_𝔮(S/R)` is the dimension at `𝔮` of the fibre of `Spec(S) → Spec(R)` over `𝔭`. This file
computes it on the fibre ring `κ(𝔭) ⊗_R S`, shows that it is unchanged by principal localization,
and computes the relative dimension of an algebra all of whose fibres have the same dimension.

## Main results

* `Algebra.relativeDimensionAt_eq_localKrullDim`: `dim_𝔮(S/R)` is the local dimension of
  `Spec(κ(𝔭) ⊗_R S)` at the prime corresponding to `𝔮`.
* `Algebra.relativeDimensionAt_comap_eq`: the relative dimension is unchanged by passing to a
  principal localization `S_g`.
* `Algebra.relativeDimension_eq_of_forall_topologicalKrullDim_fiber`: an algebra all of whose
  fibres have dimension `d` has relative dimension `d`.
-/

@[expose] public section

open Algebra.TensorProduct

/-- A prime `𝔔` of the fibre `κ(𝔭) ⊗_R S` corresponds to a prime `𝔮` of `S` over `𝔭` under
`PrimeSpectrum.preimageHomeomorphFiber` exactly when `𝔔 ∩ S = 𝔮`. -/
private theorem preimageHomeomorphFiber_eq_iff_comap_includeRight_eq {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] {p : PrimeSpectrum R}
    (x : ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})) (Q : PrimeSpectrum (p.asIdeal.Fiber S)) :
    PrimeSpectrum.preimageHomeomorphFiber R S p x = Q ↔
      Q.asIdeal.comap (includeRight : S →ₐ[R] p.asIdeal.Fiber S) = x.1.asIdeal := by
  rw [eq_comm, ← (PrimeSpectrum.preimageHomeomorphFiber R S p).symm_apply_eq, Subtype.ext_iff,
    PrimeSpectrum.ext_iff]
  rfl

/-- For a prime `𝔮` of `S` over `𝔭` and the prime `𝔔` of `κ(𝔭) ⊗_R S` with `𝔔 ∩ S = 𝔮`,
`dim_𝔮(S/R)` is the local dimension of `Spec(κ(𝔭) ⊗_R S)` at `𝔔`. -/
theorem Algebra.relativeDimensionAt_eq_localKrullDim {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] (p : Ideal R) [p.IsPrime] (hp : q.under R = p)
    (Q : Ideal (p.Fiber S)) [Q.IsPrime] (hQ : Q.comap (includeRight : S →ₐ[R] p.Fiber S) = q) :
    Algebra.relativeDimensionAt R q =
      TopologicalSpace.localKrullDim (PrimeSpectrum (p.Fiber S)) ⟨Q, ‹_›⟩ := by
  subst hp
  set e := PrimeSpectrum.preimageHomeomorphFiber R S
    (PrimeSpectrum.comap (algebraMap R S) ⟨q, ‹_›⟩)
  have he : e ⟨⟨q, ‹_›⟩, rfl⟩ = ⟨Q, ‹_›⟩ :=
    (preimageHomeomorphFiber_eq_iff_comap_includeRight_eq _ _).2 hQ
  rw [Algebra.relativeDimensionAt, topologicalKrullDimAt_eq_of_homeomorph e, he,
    TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  rfl

/-- For a localization `S_g` of `S` away from `g` and a prime `𝔔` of `S_g`,
`dim_{𝔔 ∩ S}(S/R) = dim_𝔔(S_g/R)`. -/
theorem Algebra.relativeDimensionAt_comap_eq {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (g : S) (Sg : Type*) [CommRing Sg] [Algebra S Sg] [IsLocalization.Away g Sg]
    [Algebra R Sg] [IsScalarTower R S Sg] (Q : Ideal Sg) [Q.IsPrime] :
    Algebra.relativeDimensionAt R (Q.comap (algebraMap S Sg)) =
      Algebra.relativeDimensionAt R Q := by
  have hoe : Topology.IsOpenEmbedding (PrimeSpectrum.comap (algebraMap S Sg)) :=
    PrimeSpectrum.localization_away_isOpenEmbedding Sg g
  set x : PrimeSpectrum Sg := ⟨Q, ‹_›⟩
  set F := PrimeSpectrum.comap (algebraMap R S) ⁻¹'
    {PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap (algebraMap S Sg) x)}
  have hcomp : PrimeSpectrum.comap (algebraMap R Sg) =
      PrimeSpectrum.comap (algebraMap R S) ∘ PrimeSpectrum.comap (algebraMap S Sg) := by
    rw [IsScalarTower.algebraMap_eq R S Sg, PrimeSpectrum.comap_comp]
  have hB : PrimeSpectrum.comap (algebraMap S Sg) ⁻¹' F =
      PrimeSpectrum.comap (algebraMap R Sg) ⁻¹' {PrimeSpectrum.comap (algebraMap R Sg) x} := by
    rw [hcomp, Set.preimage_comp]
    rfl
  calc Algebra.relativeDimensionAt R (Q.comap (algebraMap S Sg))
      = stacksTopologicalKrullDimAt F (F.restrictPreimage (PrimeSpectrum.comap (algebraMap S Sg))
          ⟨x, rfl⟩) := rfl
    _ = stacksTopologicalKrullDimAt (PrimeSpectrum.comap (algebraMap S Sg) ⁻¹' F) ⟨x, rfl⟩ :=
        (hoe.restrictPreimage F).topologicalKrullDimAt_eq _
    _ = Algebra.relativeDimensionAt R Q :=
        topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.setCongr hB) _

/-! ### Primes of the fibre -/

/-- Every prime `𝔮` of `S` over `𝔭` is `𝔔 ∩ S` for a prime `𝔔` of the fibre `κ(𝔭) ⊗_R S`. -/
theorem Ideal.Fiber.exists_comap_includeRight_eq {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] (p : Ideal R) [p.IsPrime] (hp : q.under R = p) :
    ∃ Q : Ideal (p.Fiber S), Q.IsPrime ∧ Q.comap (includeRight : S →ₐ[R] p.Fiber S) = q := by
  subst hp
  set e := PrimeSpectrum.preimageHomeomorphFiber R S
    (PrimeSpectrum.comap (algebraMap R S) ⟨q, ‹_›⟩)
  exact ⟨_, (e ⟨⟨q, ‹_›⟩, rfl⟩).isPrime,
    (preimageHomeomorphFiber_eq_iff_comap_includeRight_eq ⟨⟨q, ‹_›⟩, rfl⟩ _).1 rfl⟩

/-! ### The relative dimension of an algebra all of whose fibres have one dimension -/

end
