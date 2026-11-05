import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Jacquet.StablePairingProof
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Exact eigen-coefficients from supplied Iwahori contraction data

These internal constructions use the actual stable-image Jacquet map. All
factorization and contraction hypotheses are supplied, not asserted to exist.
-/

noncomputable section

namespace Langlands.Jacquet

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual stable-image quotient map as a linear equivalence, using the
published bijectivity theorem for the supplied Iwahori contraction. -/
def iwahoriStableImageJacquetEquiv
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (g : G)
    (h : IsIwahoriContraction K N M Nbar g)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)) :
    stableImage ρ hρ K hK g ≃ₗ[ℂ]
      fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype) :=
  LinearEquiv.ofBijective (stableImageJacquetMap ρ hρ K hK g N M hMN)
    (stableImageJacquetMap_bijective_of_iwahoriContraction ρ hρ hK h hMN hfin)

@[simp]
theorem iwahoriStableImageJacquetEquiv_apply
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (g : G)
    (h : IsIwahoriContraction K N M Nbar g)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (x : stableImage ρ hρ K hK g) :
    (iwahoriStableImageJacquetEquiv ρ hρ K hK N M Nbar hMN g h hfin x :
      Coinvariants ρ N) = mk ρ N ((x : fixedVectors ρ K.toSubgroup) : V) := rfl

/-- An ordinary Jacquet eigenvector fixed by `K ∩ M` has a nonzero `K`-fixed
lift which is an eigenvector of compression with the same eigenvalue. -/
theorem exists_compressedAction_eigenvector_of_jacquet_eigenvector
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (g : G)
    (h : IsIwahoriContraction K N M Nbar g)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (μ : ℂ) (w : Coinvariants ρ N) (hw0 : w ≠ 0)
    (hwK : w ∈ fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype))
    (hw : action ρ N M hMN ⟨g, h.mem_levi⟩ w = μ • w) :
    ∃ x : fixedVectors ρ K.toSubgroup,
      x ≠ 0 ∧ mk ρ N (x : V) = w ∧
        compressedAction ρ hρ K hK g x = μ • x := by
  let e := iwahoriStableImageJacquetEquiv ρ hρ K hK N M Nbar hMN g h hfin
  let x' := e.symm ⟨w, hwK⟩
  have hxw : mk ρ N ((x' : fixedVectors ρ K.toSubgroup) : V) = w := by
    change (e x' : Coinvariants ρ N) = w
    rw [LinearEquiv.apply_symm_apply]
  have hx0 : (x' : fixedVectors ρ K.toSubgroup) ≠ 0 := by
    intro hx
    apply hw0
    rw [← hxw, hx]
    simp
  have heq : stableImageAction ρ hρ K hK g x' = μ • x' := by
    apply e.injective
    apply Subtype.ext
    change mk ρ N
        ((compressedAction ρ hρ K hK g (x' : fixedVectors ρ K.toSubgroup)) : V) =
      μ • mk ρ N ((x' : fixedVectors ρ K.toSubgroup) : V)
    rw [mk_compressedAction_of_iwahoriContraction ρ hρ hK h hMN, hxw, hw]
  exact ⟨x', hx0, hxw, congrArg Subtype.val heq⟩

/-- A nonzero compression eigenvector supplies an exact smooth matrix
coefficient when compression respects powers of the given element. -/
theorem exists_eigen_coefficient_of_compressedAction_eigenvector
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hpow : ∀ n : ℕ, compressedAction ρ hρ K hK (g ^ n) =
      compressedAction ρ hρ K hK g ^ n)
    (μ : ℂ) (x : fixedVectors ρ K.toSubgroup) (hx0 : x ≠ 0)
    (hx : compressedAction ρ hρ K hK g x = μ • x) :
    ∃ ℓ : SmoothDual ρ,
      (ℓ : Module.Dual ℂ V) x ≠ 0 ∧
      (∀ k ∈ K, ∀ y, (ℓ : Module.Dual ℂ V) (ρ k y) = (ℓ : Module.Dual ℂ V) y) ∧
      ∀ n : ℕ, (ℓ : Module.Dual ℂ V) (ρ (g ^ n) x) =
        μ ^ n * (ℓ : Module.Dual ℂ V) x := by
  have hxV : (x : V) ≠ 0 := fun hx => hx0 (Subtype.ext hx)
  obtain ⟨ℓ0, hℓ0⟩ : ∃ ℓ0 : Module.Dual ℂ V, ℓ0 x ≠ 0 := by
    simpa using mt (Module.forall_dual_apply_eq_zero_iff ℂ (x : V)).mp hxV
  let avg := Compact.averageMap ρ hρ K hK
  let ℓ : Module.Dual ℂ V := ℓ0 ∘ₗ avg
  have hℓinv : ∀ k ∈ K, ∀ y, ℓ (ρ k y) = ℓ y := by
    intro k hk y
    change ℓ0 (avg (ρ k y)) = ℓ0 (avg y)
    rw [averageMap_apply_of_mem ρ hρ K hK hk]
  have hℓsmooth : ℓ ∈ smoothVectors ρ.dual := by
    refine ⟨K, ?_⟩
    intro k
    change ρ.dual k ℓ = ℓ
    ext y
    rw [Representation.dual_apply, Module.Dual.transpose_apply]
    exact hℓinv _ (K.inv_mem k.property) y
  have hℓx : ℓ x = ℓ0 x := by
    change ℓ0 (avg x) = ℓ0 x
    rw [Compact.averageMap_id ρ hρ K hK x x.property]
  have hAn : ∀ n : ℕ, (compressedAction ρ hρ K hK g ^ n) x = μ ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]
  refine ⟨⟨ℓ, hℓsmooth⟩, ?_, hℓinv, fun n => ?_⟩
  · change ℓ x ≠ 0
    rw [hℓx]
    exact hℓ0
  · change ℓ (ρ (g ^ n) x) = μ ^ n * ℓ x
    have hn : avg (ρ (g ^ n) x) =
        ((compressedAction ρ hρ K hK g ^ n) x : V) := by
      rw [← hpow]
      rfl
    change ℓ0 (avg _) = _
    rw [hn, hAn, Submodule.coe_smul, map_smul, smul_eq_mul, hℓx]

/-- The exact eigen-coefficient attached to a fixed Jacquet eigenvector for a
supplied contracting element. No existence of contraction data is concluded. -/
theorem exists_eigen_coefficient_of_jacquet_eigenvector
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (g : G)
    (h : IsIwahoriContraction K N M Nbar g)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (μ : ℂ) (w : Coinvariants ρ N) (hw0 : w ≠ 0)
    (hwK : w ∈ fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype))
    (hw : action ρ N M hMN ⟨g, h.mem_levi⟩ w = μ • w) :
    ∃ (x : fixedVectors ρ K.toSubgroup) (ℓ : SmoothDual ρ),
      mk ρ N (x : V) = w ∧ (ℓ : Module.Dual ℂ V) x ≠ 0 ∧
      (∀ k ∈ K, ∀ y, (ℓ : Module.Dual ℂ V) (ρ k y) = (ℓ : Module.Dual ℂ V) y) ∧
      ∀ n : ℕ, (ℓ : Module.Dual ℂ V) (ρ (g ^ n) x) =
        μ ^ n * (ℓ : Module.Dual ℂ V) x := by
  obtain ⟨x, hx0, hxw, hx⟩ :=
    exists_compressedAction_eigenvector_of_jacquet_eigenvector
      ρ hρ K hK N M Nbar hMN g h hfin μ w hw0 hwK hw
  obtain ⟨ℓ, hℓx, hℓK, hℓn⟩ :=
    exists_eigen_coefficient_of_compressedAction_eigenvector
      ρ hρ K hK g (h.compressedAction_pow ρ hρ hK) μ x hx0 hx
  exact ⟨x, ℓ, hxw, hℓx, hℓK, hℓn⟩

end Langlands.Jacquet
