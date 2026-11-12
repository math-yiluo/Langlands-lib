import Langlands.ClassField.Global.RelativeWeilTransfer
import Langlands.ClassField.Global.H1VanishingProof
import Langlands.Global.AdelicFunctoriality.IdeleNormOpen

/-! # Weil maps between relative global Weil groups

For number fields `F ⊆ K ⊆ L` with `K / F` and `L / F` Galois, a Weil map
`W_{L/F} → W_{K/F}` in the sense of Artin–Tate, Chapter XV, printed p.177.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField Topology
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

universe u

namespace RelativeWeilGroup

attribute [local instance] relativeIdeleClassAction relativeGaloisTopology

section Conjugation

variable {c : FundamentalClass.ClassFamily.{u}} {F K : Type u}
  [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] [IsGalois F K]
  {G : Type*} [Group G] [TopologicalSpace G]

/-- A continuous homomorphism into `W_{K/F}` followed by conjugation by `x`. -/
def conjMap (x : RelativeWeilGroup c F K) (φ : G →ₜ* RelativeWeilGroup c F K) :
    G →ₜ* RelativeWeilGroup c F K where
  toMonoidHom := (MulAut.conj x).toMonoidHom.comp φ.toMonoidHom
  continuous_toFun := (continuous_const.mul φ.continuous).mul continuous_const

@[simp]
theorem conjMap_apply (x : RelativeWeilGroup c F K) (φ : G →ₜ* RelativeWeilGroup c F K)
    (g : G) : conjMap x φ g = x * φ g * x⁻¹ :=
  rfl

end Conjugation

section Cocycle

variable {F K : Type u} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [IsGalois F K]

/-- Every multiplicative `1`-cocycle of `Gal(K/F)` in `C_K` is a coboundary, by the
published vanishing of `H¹(Gal(K/F), C_K)`. -/
theorem exists_eq_div_of_cocycle (g : (K ≃ₐ[F] K) → IdeleClassGroup (𝓞 K) K)
    (hg : ∀ σ τ, g (σ * τ) = g σ * relativeIdeleClassAut F K σ (g τ)) :
    ∃ b : IdeleClassGroup (𝓞 K) K, ∀ σ, g σ = relativeIdeleClassAut F K σ b / b := by
  have hsub := ideleClassH1Vanishing.{u} F K
  let B := relativeIdeleClassRepresentation F K
  let ψ : (K ≃ₐ[F] K) → B := fun σ => Additive.ofMul (g σ)
  have hmem : ψ ∈ groupCohomology.cocycles₁ B := by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro σ τ
    exact congrArg Additive.ofMul
      ((hg σ τ).trans (mul_comm (g σ) (relativeIdeleClassAut F K σ (g τ))))
  have hzero : groupCohomology.H1π B ⟨_, hmem⟩ = 0 := Subsingleton.elim _ _
  rw [groupCohomology.H1π_eq_zero_iff] at hzero
  obtain ⟨d, hd⟩ := hzero
  refine ⟨Additive.toMul (α := IdeleClassGroup (𝓞 K) K) d, fun σ => ?_⟩
  exact (congrArg (Additive.toMul (α := IdeleClassGroup (𝓞 K) K)) (congrFun hd σ)).symm

end Cocycle

section Level

variable (F K L : Type u) [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra F L] [Algebra K L] [IsScalarTower F K L]

/-- In a tower `F ⊆ K ⊆ L` with `K / F` normal, the `F`-automorphisms of `L` which are
`K`-linear are exactly those restricting to the identity on `K`. -/
theorem range_restrictScalarsHom_eq_ker [Normal F K] [Normal F L] :
    (AlgEquiv.restrictScalarsHom F : (L ≃ₐ[K] L) →* (L ≃ₐ[F] L)).range =
      (AlgEquiv.restrictNormalHom K : (L ≃ₐ[F] L) →* (K ≃ₐ[F] K)).ker := by
  ext σ
  rw [MonoidHom.mem_ker]
  constructor
  · rintro ⟨τ, rfl⟩
    ext y
    apply (algebraMap K L).injective
    rw [AlgEquiv.one_apply]
    exact (AlgEquiv.restrictNormal_commutes _ K y).trans (τ.commutes y)
  · intro hσ
    refine ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun y => ?_, AlgEquiv.ext fun x => rfl⟩
    have h := AlgEquiv.restrictNormal_commutes σ K y
    change σ.restrictNormal K = 1 at hσ
    rw [hσ, AlgEquiv.one_apply] at h
    exact h.symm

end Level

section LevelSubgroup

variable (c : FundamentalClass.ClassFamily.{u}) (F K L : Type u)
  [Field F] [NumberField F] [Field K] [Field L] [NumberField L]
  [Algebra F K] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [IsGalois F L]

/-- The subgroup `U^L_K` of `W_{L/F}`: the inverse image of `Gal(L/K)`. -/
def levelSubgroup : Subgroup (RelativeWeilGroup c F L) :=
  (AlgEquiv.restrictScalarsHom F : (L ≃ₐ[K] L) →* (L ≃ₐ[F] L)).range.comap (projection c F L)

theorem mem_levelSubgroup_iff (t : RelativeWeilGroup c F L) :
    t ∈ levelSubgroup c F K L ↔
      ∃ σ : L ≃ₐ[K] L, AlgEquiv.restrictScalarsHom F σ = projection c F L t :=
  Iff.rfl

theorem inclusion_mem_levelSubgroup (a : IdeleClassGroup (𝓞 L) L) :
    inclusion c F L a ∈ levelSubgroup c F K L := by
  refine ⟨1, ?_⟩
  rw [map_one]
  exact ((MonoidHom.mem_ker).mp ((exact c F L).le ⟨a, rfl⟩)).symm

/-- The closure `(U^L_K)^c` of the commutator subgroup of `U^L_K`. -/
def levelCommutatorClosure : Subgroup (RelativeWeilGroup c F L) :=
  (⁅levelSubgroup c F K L, levelSubgroup c F K L⁆).topologicalClosure

theorem range_restrictionInclusion_eq_levelSubgroup [NumberField K]
    (h : FundamentalClass.Restriction c) :
    haveI : IsGalois K L := IsGalois.tower_top_of_isGalois F K L
    (restrictionInclusion c F L K h).toMonoidHom.range = levelSubgroup c F K L :=
  range_restrictionInclusion c F L K h

variable [Normal F K]

/-- `U^L_K` is the kernel of the composite `W_{L/F} → Gal(L/F) → Gal(K/F)`. -/
theorem levelSubgroup_eq_ker :
    levelSubgroup c F K L =
      ((AlgEquiv.restrictNormalHom K).comp (projection c F L)).ker := by
  rw [levelSubgroup, range_restrictScalarsHom_eq_ker, MonoidHom.comap_ker]

theorem mem_levelSubgroup_iff_restrictNormalHom (t : RelativeWeilGroup c F L) :
    t ∈ levelSubgroup c F K L ↔ AlgEquiv.restrictNormalHom K (projection c F L t) = 1 := by
  rw [levelSubgroup_eq_ker]
  rfl

instance levelSubgroup_normal : (levelSubgroup c F K L).Normal := by
  rw [levelSubgroup_eq_ker]
  exact MonoidHom.normal_ker _

instance levelCommutatorClosure_normal : (levelCommutatorClosure c F K L).Normal :=
  Subgroup.is_normal_topologicalClosure _

theorem levelCommutatorClosure_le_levelSubgroup :
    levelCommutatorClosure c F K L ≤ levelSubgroup c F K L := by
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.commutator_le_left _ _) ?_
  rw [levelSubgroup_eq_ker]
  have hc : Continuous ((AlgEquiv.restrictNormalHom K).comp (projection c F L)) :=
    (continuous_of_discreteTopology
      (f := ⇑(AlgEquiv.restrictNormalHom K : (L ≃ₐ[F] L) →* (K ≃ₐ[F] K)))).comp
      (ClassExtension.continuous_projection (c F L))
  exact (isClosed_discrete ({1} : Set (K ≃ₐ[F] K))).preimage hc

end LevelSubgroup

variable (c : FundamentalClass.ClassFamily.{u}) (F K L : Type u)
  [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra F K] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
  [IsGalois F K] [IsGalois F L]

variable (h : FundamentalClass.Restriction c)

/-- A Weil map `W_{L/F} → W_{K/F}` (Artin–Tate XV, printed p.177): a continuous
surjective homomorphism over the restriction `Gal(L/F) → Gal(K/F)`, equal on
`U^L_K ≅ W_{L/K}` to the transfer to `C_K`, with kernel `(U^L_K)^c`. -/
structure IsWeilMap (φ : RelativeWeilGroup c F L →ₜ* RelativeWeilGroup c F K) : Prop where
  surjective : Function.Surjective φ
  projection_map : ∀ t : RelativeWeilGroup c F L,
    projection c F K (φ t) = AlgEquiv.restrictNormalHom K (projection c F L t)
  map_restrictionInclusion :
    haveI : IsGalois K L := IsGalois.tower_top_of_isGalois F K L
    ∀ t : RelativeWeilGroup c K L,
      φ (restrictionInclusion c F L K h t) = inclusion c F K (transfer c K L t)
  ker_eq : φ.toMonoidHom.ker = levelCommutatorClosure c F K L

namespace IsWeilMap

variable {c F K L h} {φ ψ : RelativeWeilGroup c F L →ₜ* RelativeWeilGroup c F K}

/-- On `C_L`, a Weil map is the idele-class norm `C_L → C_K`. -/
theorem map_inclusion (hφ : IsWeilMap c F K L h φ) (a : IdeleClassGroup (𝓞 L) L) :
    φ (inclusion c F L a) = inclusion c F K (ideleClassNorm (K := K) (L := L) a) := by
  have : IsGalois K L := IsGalois.tower_top_of_isGalois F K L
  rw [← restrictionInclusion_inclusion c F L K h a, hφ.map_restrictionInclusion,
    transfer_inclusion]

/-- A Weil map sends `U^L_K` into `C_K`. -/
theorem map_mem_range_inclusion (hφ : IsWeilMap c F K L h φ) {t : RelativeWeilGroup c F L}
    (ht : t ∈ levelSubgroup c F K L) : φ t ∈ (inclusion c F K).range := by
  have : IsGalois K L := IsGalois.tower_top_of_isGalois F K L
  rw [← range_restrictionInclusion_eq_levelSubgroup c F K L h] at ht
  obtain ⟨s, rfl⟩ := ht
  exact ⟨_, (hφ.map_restrictionInclusion s).symm⟩

/-- `U^L_K` is the inverse image of `C_K` under a Weil map. -/
theorem levelSubgroup_eq_comap (hφ : IsWeilMap c F K L h φ) :
    levelSubgroup c F K L = (inclusion c F K).range.comap φ.toMonoidHom := by
  ext t
  rw [Subgroup.mem_comap, exact, MonoidHom.mem_ker, mem_levelSubgroup_iff_restrictNormalHom]
  exact (hφ.projection_map t ▸ Iff.rfl)

theorem commutator_le_ker (hφ : IsWeilMap c F K L h φ) :
    ⁅levelSubgroup c F K L, levelSubgroup c F K L⁆ ≤ φ.toMonoidHom.ker := by
  rw [hφ.ker_eq]
  exact Subgroup.le_topologicalClosure _

/-- Weil maps are open maps, since the idele-class norm is open. -/
theorem isOpenMap (hφ : IsWeilMap c F K L h φ) : IsOpenMap φ := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨t, ht, rfl⟩
  let V : Set (IdeleClassGroup (𝓞 L) L) := (fun a => inclusion c F L a * t) ⁻¹' U
  have hV : IsOpen V :=
    hU.preimage ((ClassExtension.continuous_inclusion (c F L)).mul continuous_const)
  refine ⟨(fun b => inclusion c F K b * φ t) '' (ideleClassNorm (K := K) (L := L) '' V),
    ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨inclusion c F L a * t, ha, by rw [map_mul, hφ.map_inclusion]⟩
  · exact ((isOpenMap_mul_right (φ t)).comp (isOpenEmbedding_inclusion c F K).isOpenMap) _
      ((isOpenMap_ideleClassNorm (K := K) (L := L)) V hV)
  · exact ⟨1, ⟨1, by simpa [V] using ht, map_one _⟩, by simp⟩

/-- Artin–Tate's Weil isomorphism `W_{L/F} / (U^L_K)^c ≃ W_{K/F}` induced by a Weil map. -/
def quotientEquiv (hφ : IsWeilMap c F K L h φ) :
    RelativeWeilGroup c F L ⧸ levelCommutatorClosure c F K L ≃ₜ*
      RelativeWeilGroup c F K :=
  let e : RelativeWeilGroup c F L ⧸ levelCommutatorClosure c F K L ≃*
      RelativeWeilGroup c F K :=
    (QuotientGroup.quotientMulEquivOfEq hφ.ker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ.toMonoidHom hφ.surjective)
  have hcont : Continuous e :=
    QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr φ.continuous
  have hopen : IsOpenMap e := by
    intro V hV
    have himage : e '' V = φ '' (QuotientGroup.mk ⁻¹' V) := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
        exact ⟨t, hq, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨QuotientGroup.mk t, ht, rfl⟩
    rw [himage]
    exact hφ.isOpenMap _ (hV.preimage QuotientGroup.continuous_mk)
  { toMulEquiv := e
    continuous_toFun := hcont
    continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen).continuous_symm }

@[simp]
theorem quotientEquiv_mk (hφ : IsWeilMap c F K L h φ) (t : RelativeWeilGroup c F L) :
    hφ.quotientEquiv (QuotientGroup.mk t) = φ t :=
  rfl

/-- Conjugating a Weil map by an element of `C_K` gives a Weil map. -/
theorem conj (hφ : IsWeilMap c F K L h φ) (a : IdeleClassGroup (𝓞 K) K) :
    IsWeilMap c F K L h (conjMap (inclusion c F K a) φ) where
  surjective y := by
    obtain ⟨t, ht⟩ := hφ.surjective ((inclusion c F K a)⁻¹ * y * inclusion c F K a)
    exact ⟨t, by simp [ht, mul_assoc]⟩
  projection_map t := by
    have ha : projection c F K (inclusion c F K a) = 1 :=
      (MonoidHom.mem_ker).mp ((exact c F K).le ⟨a, rfl⟩)
    rw [conjMap_apply, map_mul, map_mul, map_inv, ha, one_mul, inv_one, mul_one,
      hφ.projection_map]
  map_restrictionInclusion t := by
    rw [conjMap_apply, hφ.map_restrictionInclusion, ← map_inv, ← map_mul, ← map_mul,
      mul_comm a, mul_inv_cancel_right]
  ker_eq := by
    rw [← hφ.ker_eq]
    ext t
    simp only [MonoidHom.mem_ker]
    change inclusion c F K a * φ t * (inclusion c F K a)⁻¹ = 1 ↔ φ t = 1
    rw [mul_inv_eq_one, mul_eq_left]

/-- Two Weil maps agree on `U^L_K`. -/
theorem eq_of_mem_levelSubgroup (hφ : IsWeilMap c F K L h φ) (hψ : IsWeilMap c F K L h ψ)
    {t : RelativeWeilGroup c F L} (ht : t ∈ levelSubgroup c F K L) : ψ t = φ t := by
  have : IsGalois K L := IsGalois.tower_top_of_isGalois F K L
  rw [← range_restrictionInclusion_eq_levelSubgroup c F K L h] at ht
  obtain ⟨s, rfl⟩ := ht
  exact (hψ.map_restrictionInclusion s).trans (hφ.map_restrictionInclusion s).symm

/-- Artin–Tate XV, Theorem 2, uniqueness part, for Weil maps: two Weil maps
`W_{L/F} → W_{K/F}` differ by an inner automorphism of `W_{K/F}` by an element of `C_K`.
The proof uses the published vanishing of `H¹(Gal(K/F), C_K)`. -/
theorem exists_eq_conjMap (hφ : IsWeilMap c F K L h φ) (hψ : IsWeilMap c F K L h ψ) :
    ∃ a : IdeleClassGroup (𝓞 K) K, ψ = conjMap (inclusion c F K a) φ := by
  let r : RelativeWeilGroup c F L →* (K ≃ₐ[F] K) :=
    (AlgEquiv.restrictNormalHom K).comp (projection c F L)
  have hr : Function.Surjective r :=
    (AlgEquiv.restrictNormalHom_surjective L).comp (projection_surjective c F L)
  have hprojφ : ∀ t, projection c F K (φ t) = r t := hφ.projection_map
  have hprojψ : ∀ t, projection c F K (ψ t) = r t := hψ.projection_map
  have hmem : ∀ t, ∃ b, inclusion c F K b = ψ t * (φ t)⁻¹ := by
    intro t
    have : ψ t * (φ t)⁻¹ ∈ (inclusion c F K).range := by
      rw [exact, MonoidHom.mem_ker, map_mul, map_inv, hprojφ, hprojψ, mul_inv_cancel]
    exact this
  choose d hd using hmem
  have hinj := inclusion_injective c F K
  have hconj : ∀ (s : RelativeWeilGroup c F K) (b : IdeleClassGroup (𝓞 K) K),
      s * inclusion c F K b * s⁻¹ =
        inclusion c F K (relativeIdeleClassAut F K (projection c F K s) b) :=
    fun s b => conjugation c F K s b
  -- the difference is a cocycle along `r`
  have hdmul : ∀ s t, d (s * t) = d s * relativeIdeleClassAut F K (r s) (d t) := by
    intro s t
    apply hinj
    rw [mul_comm (d s), map_mul, ← hprojψ s, ← hconj, hd, hd, hd, map_mul, map_mul]
    group
  have hdright : ∀ s u, u ∈ levelSubgroup c F K L → d (s * u) = d s := by
    intro s u hu
    apply hinj
    rw [hd, hd, map_mul, map_mul, eq_of_mem_levelSubgroup hφ hψ hu]
    group
  choose ℓ hℓ using hr
  have hfactor : ∀ t, d t = d (ℓ (r t)) := by
    intro t
    have hu : (ℓ (r t))⁻¹ * t ∈ levelSubgroup c F K L := by
      rw [levelSubgroup_eq_ker, MonoidHom.mem_ker, map_mul, map_inv, hℓ, inv_mul_cancel]
    have := hdright (ℓ (r t)) _ hu
    rwa [mul_inv_cancel_left] at this
  let g : (K ≃ₐ[F] K) → IdeleClassGroup (𝓞 K) K := fun σ => d (ℓ σ)
  have hg : ∀ σ τ, g (σ * τ) = g σ * relativeIdeleClassAut F K σ (g τ) := by
    intro σ τ
    have h1 := hfactor (ℓ σ * ℓ τ)
    rw [map_mul, hℓ, hℓ] at h1
    change d (ℓ (σ * τ)) = _
    rw [← h1, hdmul, hℓ]
  obtain ⟨b, hb⟩ := exists_eq_div_of_cocycle g hg
  refine ⟨b⁻¹, ContinuousMonoidHom.ext fun t => ?_⟩
  have h1 : ψ t = inclusion c F K (d t) * φ t := by rw [hd t, inv_mul_cancel_right]
  have h2 : φ t * inclusion c F K b =
      inclusion c F K (relativeIdeleClassAut F K (r t) b) * φ t := by
    rw [← hprojφ t, ← hconj, inv_mul_cancel_right]
  rw [conjMap_apply, h1, hfactor t, show d (ℓ (r t)) = g (r t) from rfl, hb, map_inv, inv_inv,
    mul_assoc, h2, ← mul_assoc, ← map_inv (inclusion c F K) b, ← map_mul, div_eq_mul_inv,
    mul_comm (relativeIdeleClassAut F K (r t) b)]

end IsWeilMap

end RelativeWeilGroup

end Langlands.ClassField.Global
