import Langlands.Representation.Jacquet.StablePairingUniformAsymptotics

/-! # Stable-pairing asymptotics with a threshold controlled by a dimension

For stable pairing data `D`, a smooth representation `ρ` admitted by `D`, a stable pairing `b`
and a good subgroup `K` whose fixed vectors have dimension at most `d`, the asymptotic formula
`ℓ(ρ(a) v) = b [ℓ] [ρ(a) v]` holds for every `K`-fixed `v` and `ℓ` and every `a` such that
`a⁻¹ (K ∩ N) a ⊆ K`, the compression of `a` on the `K`-fixed vectors of `ρ` commutes with the
compression by `g⁻¹`, and it is a left multiple of the `d`-th power of that compression.

The commutation and factorization hypotheses are conditions on the compressions of the given
representation `ρ`; in general they depend on `ρ`, even with `D`, `a`, `K` and `d` fixed. What
this lemma removes, compared with `exists_finset_asymptotics_of_commute`, is the finite set of
conjugation conditions produced from the particular `v`: the exponent `d` is fixed in advance.
In the standard specialization (`StandardCasselmanDimensionThreshold`), the two operator
hypotheses are derived from group-level facts (the Iwahori factorization of `K` and the
dominant-lattice factorization `ϖ^λ = ϖ^{λ - d z} g^d`), so they hold for every admissible `ρ`
with `dim V^K ≤ d` at once; that is how the uniformity of Waldspurger's Proposition I.4.3 and
I.5 is obtained.
-/

noncomputable section

namespace Langlands.Jacquet

universe uG uV

namespace StablePairingData

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {D : StablePairingData G}
variable {ρ : Representation ℂ G V} {hρ : IsSmooth ρ}
variable {b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ] Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ}

/-- On a finite-dimensional space of fixed vectors, the power kernels of the compression by
`g⁻¹` are killed by its `d`-th power as soon as `d` bounds the dimension. -/
theorem powerKernelSup_le_ker_pow (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    [FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)] {d : ℕ}
    (hd : Module.finrank ℂ (fixedVectors ρ K.toSubgroup) ≤ d) :
    powerKernelSup ρ hρ K hK g ≤ LinearMap.ker (compressedAction ρ hρ K hK g ^ d) := by
  refine iSup_le fun r => ?_
  rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le hd]
  exact Module.End.ker_pow_le_ker_pow_finrank _ r

/-- **Asymptotics with a dimension-controlled threshold.** Let `K` be a good subgroup whose
fixed vectors have dimension at most `d`, and `v`, `ℓ` be fixed by `K`. For every `a` whose
inverse conjugates `K ∩ N` into `K`, whose compression on `K`-fixed vectors commutes with the
compression by `g⁻¹` and is a left multiple of the `d`-th power of that compression,
`ℓ(ρ(a) v) = b [ℓ] [ρ(a) v]`. -/
theorem IsStablePairing.asymptotics_of_finrank_le (hA : D.Admits ρ hρ)
    (hb : D.IsStablePairing ρ hρ b) (K : OpenSubgroup G) (hK : D.Good K)
    [FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)] {d : ℕ}
    (hd : Module.finrank ℂ (fixedVectors ρ K.toSubgroup) ≤ d)
    {v : V} (hv : v ∈ fixedVectors ρ K.toSubgroup)
    {ℓ : SmoothDual ρ} (hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup)
    (a : G) (hup : ∀ u ∈ K, u ∈ D.N → a⁻¹ * u * a ∈ K)
    (hc : Commute (compressedAction ρ hρ K (D.isCompact K hK) a)
      (compressedAction ρ hρ K (D.isCompact K hK) D.g⁻¹))
    (X : Module.End ℂ (fixedVectors ρ K.toSubgroup))
    (hX : compressedAction ρ hρ K (D.isCompact K hK) a =
      X * compressedAction ρ hρ K (D.isCompact K hK) D.g⁻¹ ^ d) :
    smoothDualPairing ρ ℓ (ρ a v) =
      b (Jacquet.mk (smoothContragredient ρ) D.N ℓ) (Jacquet.mk ρ D.Nbar (ρ a v)) := by
  obtain ⟨t, ht, hmk⟩ := D.exists_stable_mk_eq hA hK ⟨v, hv⟩
  have hker : (⟨v, hv⟩ - t : fixedVectors ρ K.toSubgroup) ∈
      LinearMap.ker (fixedJacquetMap ρ D.Nbar D.M D.hMNbar K.toSubgroup) := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    rw [map_sub, Submodule.coe_sub, fixedJacquetMap_apply, fixedJacquetMap_apply, hmk, sub_self]
    rfl
  have hpow : (compressedAction ρ hρ K (D.isCompact K hK) D.g⁻¹ ^ d) (⟨v, hv⟩ - t) = 0 :=
    LinearMap.mem_ker.mp
      (powerKernelSup_le_ker_pow K (D.isCompact K hK) D.g⁻¹ hd (hA.lower_kernel K hK hker))
  have hzero : compressedAction ρ hρ K (D.isCompact K hK) a (⟨v, hv⟩ - t) = 0 := by
    rw [hX, Module.End.mul_apply, hpow, map_zero]
  have havg : Compact.averageMap ρ hρ K (D.isCompact K hK) (ρ a v) =
      (compressedAction ρ hρ K (D.isCompact K hK) a t : V) := by
    have h := congrArg Subtype.val hzero
    rw [map_sub, Submodule.coe_sub, compressedAction_apply, compressedAction_apply,
      ZeroMemClass.coe_zero, sub_eq_zero] at h
    rw [compressedAction_apply]
    exact h
  have hst := mem_stableImage_of_commute ρ hρ K (D.isCompact K hK) D.g⁻¹ hc ht
  have e := hb K hK ⟨ℓ, hℓ⟩ _ hst
  have hu : ∀ x ∈ K, x ∈ D.N → ρ x (ρ a v) = ρ a v := by
    intro x hx hxN
    calc ρ x (ρ a v) = ρ a (ρ (a⁻¹ * x * a) v) := by
          simp only [← Module.End.mul_apply, ← map_mul]
          congr 1
          group
      _ = ρ a v := by rw [apply_eq_of_mem_fixedVectors ρ hv (hup x hx hxN)]
  rw [← smoothDualPairing_averageMap ρ hρ K (D.isCompact K hK) hℓ (ρ a v),
    ← hb.apply_mk_averageMap hA K hK hℓ hu, havg]
  exact e.symm

end StablePairingData

end Langlands.Jacquet
