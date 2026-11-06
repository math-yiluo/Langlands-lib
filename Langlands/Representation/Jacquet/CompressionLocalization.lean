import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Algebra.RenardLocalizationExtensionProof
import Langlands.Algebra.RenardEndomorphismLocalizationKernelProof

/-! # The actual localization of compact compression and Jacquet fixed vectors -/

noncomputable section

namespace Langlands

universe uR uG uV uW

namespace Renard.EndomorphismLocalization

section KernelExhaustion

variable {R : Type uR} [CommRing R]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module R W]

/-- Local nilpotence of the kernel suffices for injectivity of the actual
localization factor; the original map need not be injective. -/
theorem extensionFactor_injective_of_kernel_nilpotent
    (a : Module.End R V) (β : W ≃ₗ[R] W) (j : V →ₗ[R] W)
    (hj : ∀ x, j (a x) = β (j x))
    (hnil : ∀ x, j x = 0 → ∃ n : ℕ, (a ^ n) x = 0) :
    Function.Injective (extensionFactor a β j hj) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨x, n, rfl⟩ := frac_surjective a z
  rw [extensionFactor_frac] at hz
  have hinj : Function.Injective (β.symm.toLinearMap ^ n) := by
    rw [Module.End.coe_pow]
    exact β.symm.injective.iterate n
  have hx : j x = 0 := hinj (hz.trans (map_zero _).symm)
  rw [frac_eq_localizedInv_pow, (iota_eq_zero_iff a x).mpr (hnil x hx), map_zero]

/-- Forward-power exhaustion supplies surjectivity of the actual factor. -/
theorem extensionFactor_surjective_of_power_exhaustion
    (a : Module.End R V) (β : W ≃ₗ[R] W) (j : V →ₗ[R] W)
    (hj : ∀ x, j (a x) = β (j x))
    (hex : ∀ y : W, ∃ (n : ℕ) (x : V), (β ^ n) y = j x) :
    Function.Surjective (extensionFactor a β j hj) := by
  intro y
  obtain ⟨n, x, hx⟩ := hex y
  refine ⟨frac a x n, ?_⟩
  have hinj : Function.Injective (β.toLinearMap ^ n) := by
    rw [Module.End.coe_pow]
    exact β.injective.iterate n
  apply hinj
  have h := pow_apply_frac a β.toLinearMap (extensionFactor a β j hj)
    (factor_intertwines a β.toLinearMap ((Module.End.isUnit_iff _).mpr β.bijective) j hj)
    x n
  have hi := LinearMap.congr_fun
    (factor_comp_iota a β.toLinearMap ((Module.End.isUnit_iff _).mpr β.bijective) j hj) x
  exact h.trans (hi.trans (by
    simpa only [Module.End.pow_apply, LinearEquiv.pow_apply, LinearEquiv.coe_coe] using hx.symm))

/-- Compare the actual localized module with an invertible target using only
local nilpotence of the kernel and power exhaustion. -/
def localizationEquivOfKernelExhaustion
    (a : Module.End R V) (β : W ≃ₗ[R] W) (j : V →ₗ[R] W)
    (hj : ∀ x, j (a x) = β (j x))
    (hnil : ∀ x, j x = 0 → ∃ n : ℕ, (a ^ n) x = 0)
    (hex : ∀ y : W, ∃ (n : ℕ) (x : V), (β ^ n) y = j x) :
    Localized a ≃ₗ[R] W :=
  LinearEquiv.ofBijective (extensionFactor a β j hj)
    ⟨extensionFactor_injective_of_kernel_nilpotent a β j hj hnil,
      extensionFactor_surjective_of_power_exhaustion a β j hj hex⟩

@[simp]
theorem localizationEquivOfKernelExhaustion_iota
    (a : Module.End R V) (β : W ≃ₗ[R] W) (j : V →ₗ[R] W)
    (hj : ∀ x, j (a x) = β (j x))
    (hnil : ∀ x, j x = 0 → ∃ n : ℕ, (a ^ n) x = 0)
    (hex : ∀ y : W, ∃ (n : ℕ) (x : V), (β ^ n) y = j x) (x : V) :
    localizationEquivOfKernelExhaustion a β j hj hnil hex (iota a x) = j x :=
  LinearMap.congr_fun
    (factor_comp_iota a β.toLinearMap ((Module.End.isUnit_iff _).mpr β.bijective) j hj) x

theorem localizationEquivOfKernelExhaustion_intertwines
    (a : Module.End R V) (β : W ≃ₗ[R] W) (j : V →ₗ[R] W)
    (hj : ∀ x, j (a x) = β (j x))
    (hnil : ∀ x, j x = 0 → ∃ n : ℕ, (a ^ n) x = 0)
    (hex : ∀ y : W, ∃ (n : ℕ) (x : V), (β ^ n) y = j x) (z : Localized a) :
    localizationEquivOfKernelExhaustion a β j hj hnil hex (localizedEnd a z) =
      β (localizationEquivOfKernelExhaustion a β j hj hnil hex z) :=
  factor_intertwines a β.toLinearMap ((Module.End.isUnit_iff _).mpr β.bijective) j hj z

end KernelExhaustion

end Renard.EndomorphismLocalization

section CentralFixedVectors

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module R V]

/-- A central group element acts invertibly on the actual fixed-vector space. -/
def centralFixedVectorsEquiv (ρ : Representation R G V) (H : Subgroup G)
    (g : G) (hg : ∀ x : G, g * x = x * g) :
    fixedVectors ρ H ≃ₗ[R] fixedVectors ρ H :=
  fixedVectorsEquiv
    (Representation.IntertwiningMap.ofBijective
      ({ toLinearMap := ρ g
         isIntertwining' x := by
           ext v
           change ρ g (ρ x v) = ρ x (ρ g v)
           rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hg x] } :
        ρ.IntertwiningMap ρ)
      (Representation.apply_bijective ρ g)) H

@[simp]
theorem centralFixedVectorsEquiv_apply (ρ : Representation R G V) (H : Subgroup G)
    (g : G) (hg : ∀ x : G, g * x = x * g) (v : fixedVectors ρ H) :
    (centralFixedVectorsEquiv ρ H g hg v).val = ρ g v.val := rfl

@[simp]
theorem centralFixedVectorsEquiv_pow_apply (ρ : Representation R G V) (H : Subgroup G)
    (g : G) (hg : ∀ x : G, g * x = x * g) (n : ℕ) (v : fixedVectors ρ H) :
    ((centralFixedVectorsEquiv ρ H g hg ^ n) v).val = ρ (g ^ n) v.val := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, centralFixedVectorsEquiv_apply, ih,
        pow_succ', map_mul, Module.End.mul_apply]

end CentralFixedVectors

namespace Jacquet

section GeometricComparison

open Renard.EndomorphismLocalization

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable {K : OpenSubgroup G} (hK : IsCompact (K : Set G))
variable {N M Nbar : Subgroup G} {g : G}

/-- The kernel of the actual fixed Jacquet quotient is locally killed by
powers of the actual compressed action, without any finiteness premise. -/
theorem fixedJacquetMap_kernel_locally_nilpotent
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (x : fixedVectors ρ K.toSubgroup)
    (hx : fixedJacquetMap ρ N M hMN K.toSubgroup x = 0) :
    ∃ n : ℕ, (compressedAction ρ hρ K hK g ^ n) x = 0 := by
  have hx' : x ∈ powerKernelSup ρ hρ K hK g := by
    rw [powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK h hMN]
    exact hx
  exact (Submodule.mem_iSup_of_directed _
    (ker_pow_monotone (compressedAction ρ hρ K hK g)).directed_le).mp hx'

include hρ hK in
/-- Every Jacquet fixed vector is carried into the range of the actual fixed
quotient by some power of the contracting element. -/
theorem fixedJacquetMap_power_exhaustion
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (y : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)) :
    ∃ (s : ℕ) (x : fixedVectors ρ K.toSubgroup),
      action ρ N M hMN (⟨g, h.mem_levi⟩ ^ s) y.val =
        (fixedJacquetMap ρ N M hMN K.toSubgroup x).val := by
  let gM : M := ⟨g, h.mem_levi⟩
  obtain ⟨v, hv⟩ := mk_surjective ρ N y.val
  obtain ⟨s, hs⟩ := h.exists_pow_lower_fixed ρ hρ v
  have hgs : ((gM ^ s : M) : G) = g ^ s := by simp [gM]
  have hlevi : ∀ m ∈ K.toSubgroup ⊓ M,
      mk ρ N (ρ m (ρ (g ^ s) v)) = action ρ N M hMN (gM ^ s) y.val := by
    intro m hm
    have hm' := h.levi_pow s m hm
    have hyfix := y.property ⟨⟨_, hm'.2⟩, hm'.1⟩
    calc
      mk ρ N (ρ m (ρ (g ^ s) v)) =
          mk ρ N (ρ (gM ^ s : M) (ρ ((g ^ s)⁻¹ * m * g ^ s) v)) := by
        rw [hgs]
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        congr 2
        group
      _ = action ρ N M hMN (gM ^ s)
          (action ρ N M hMN ⟨_, hm'.2⟩ (mk ρ N v)) := by
        rw [action_mk, action_mk]
      _ = _ := by
        rw [hv]
        exact congrArg _ hyfix
  have hconst : ∀ k : K,
      mk ρ N (ρ k.val (ρ (g ^ s) v)) = action ρ N M hMN (gM ^ s) y.val := by
    intro k
    obtain ⟨l, hl, m, hm, u, hu, hprod⟩ := h.factor k.val⁻¹ (K.inv_mem k.property)
    have heq : k.val = u⁻¹ * (m⁻¹ * l⁻¹) := by
      rw [← inv_inv k.val, hprod]
      group
    rw [heq, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hs _ ((K.toSubgroup ⊓ Nbar).inv_mem hl)]
    rw [mk_apply_subgroup ρ N ⟨u⁻¹, N.inv_mem hu.2⟩]
    exact hlevi _ ((K.toSubgroup ⊓ M).inv_mem hm)
  refine ⟨s, ⟨Compact.averageMap ρ hρ K hK (ρ (g ^ s) v),
    Compact.averageMap_mem_fixedVectors ρ hρ K hK _⟩, ?_⟩
  exact (map_averageMap_of_forall_eq ρ hρ K hK (mk ρ N) _ _ hconst).symm

/-- The actual unnormalized action of a Levi-central contracting element on
the Jacquet fixed-vector space, with its genuine inverse. -/
def fixedJacquetCentralEquiv
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (hcentral : ∀ m ∈ M, m * g = g * m) :
    fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype) ≃ₗ[ℂ]
      fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype) :=
  centralFixedVectorsEquiv (action ρ N M hMN) (K.toSubgroup.comap M.subtype)
    ⟨g, h.mem_levi⟩ (fun m => Subtype.ext (hcentral m.val m.property).symm)

theorem fixedJacquetMap_intertwines_centralEquiv
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (hcentral : ∀ m ∈ M, m * g = g * m) (x : fixedVectors ρ K.toSubgroup) :
    fixedJacquetMap ρ N M hMN K.toSubgroup (compressedAction ρ hρ K hK g x) =
      fixedJacquetCentralEquiv ρ h hMN hcentral
        (fixedJacquetMap ρ N M hMN K.toSubgroup x) := by
  apply Subtype.ext
  exact mk_compressedAction_of_iwahoriContraction ρ hρ hK h hMN x

include hρ hK in
theorem fixedJacquetCentralEquiv_power_exhaustion
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (hcentral : ∀ m ∈ M, m * g = g * m)
    (y : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)) :
    ∃ (s : ℕ) (x : fixedVectors ρ K.toSubgroup),
      (fixedJacquetCentralEquiv ρ h hMN hcentral ^ s) y =
        fixedJacquetMap ρ N M hMN K.toSubgroup x := by
  obtain ⟨s, x, hx⟩ := fixedJacquetMap_power_exhaustion ρ hρ hK h hMN y
  refine ⟨s, x, Subtype.ext ?_⟩
  rw [fixedJacquetCentralEquiv, centralFixedVectorsEquiv_pow_apply]
  exact hx

/-- The actual endomorphism localization of compact compression is the actual
Jacquet fixed-vector space. No dimension or admissibility assumption is used. -/
def compressionJacquetLocalizationEquiv
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (hcentral : ∀ m ∈ M, m * g = g * m) :
    Localized (compressedAction ρ hρ K hK g) ≃ₗ[ℂ]
      fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype) :=
  localizationEquivOfKernelExhaustion (compressedAction ρ hρ K hK g)
    (fixedJacquetCentralEquiv ρ h hMN hcentral)
    (fixedJacquetMap ρ N M hMN K.toSubgroup)
    (fixedJacquetMap_intertwines_centralEquiv ρ hρ hK h hMN hcentral)
    (fixedJacquetMap_kernel_locally_nilpotent ρ hρ hK h hMN)
    (fixedJacquetCentralEquiv_power_exhaustion ρ hρ hK h hMN hcentral)

@[simp]
theorem compressionJacquetLocalizationEquiv_iota
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (hcentral : ∀ m ∈ M, m * g = g * m) (x : fixedVectors ρ K.toSubgroup) :
    compressionJacquetLocalizationEquiv ρ hρ hK h hMN hcentral
        (iota (compressedAction ρ hρ K hK g) x) =
      fixedJacquetMap ρ N M hMN K.toSubgroup x :=
  localizationEquivOfKernelExhaustion_iota _ _ _ _ _ _ x

theorem compressionJacquetLocalizationEquiv_intertwines
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (hcentral : ∀ m ∈ M, m * g = g * m)
    (z : Localized (compressedAction ρ hρ K hK g)) :
    compressionJacquetLocalizationEquiv ρ hρ hK h hMN hcentral
        (localizedEnd (compressedAction ρ hρ K hK g) z) =
      fixedJacquetCentralEquiv ρ h hMN hcentral
        (compressionJacquetLocalizationEquiv ρ hρ hK h hMN hcentral z) :=
  localizationEquivOfKernelExhaustion_intertwines _ _ _ _ _ _ z

end GeometricComparison

end Jacquet

end Langlands
