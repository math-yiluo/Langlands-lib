import Langlands.BruhatTits.IntegralModels.GeneralLinearDepthZero
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction
import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.Group.GL.SingletonBlocks
import Langlands.Group.GL.BlockUnipotentCoordinates
import Langlands.Group.GL.Transvection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The standard Iwahori subgroup of `GL_N` and the hyperspecial `GL_N(𝒪)`

For a nonarchimedean local field `F` with valuation ring `𝒪[F]` and residue field `𝓀[F]`,
every subgroup `H` of `GL_N(𝓀[F])` has a preimage in `G^0(𝒪) = GL_N(𝒪[F])`, the integral
points of the standard model of `GL_N`. These preimages lie between `G(F)^{0+}` (the
preimage of `1`) and `G^0(𝒪)` (the preimage of everything), and their relative indices are
those of the subgroups of `GL_N(𝓀[F])`. Reduction identifies the preimage of `H` modulo
`G(F)^{0+}` with `H`.

The standard Iwahori subgroup `I` is the preimage of the upper triangular group `B(𝓀[F])`,
and `I^+` is the preimage of the upper unipotent group `U(𝓀[F])`. We compare them with the
hyperspecial pair `G(F)^{0+} ⊆ G^0(𝒪)`: `[G^0(𝒪) : I] = [GL_N(𝓀[F]) : B(𝓀[F])]`
(`q + 1` for `N = 2`), `[I : I^+] = (q - 1)^N`, `[I^+ : G(F)^{0+}] = q^(N choose 2)`, and
`I/I^+` is the diagonal torus `(GL_1(𝓀[F]))^N`, the Levi factor of the singleton block shape.
For `N ≥ 2`, `I` is a proper subgroup of `G^0(𝒪)`; for `N ≤ 1`, `I = G^0(𝒪)` and
`I^+ = G(F)^{0+}`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : ℕ)

/-- Reduction modulo the maximal ideal on invertible matrices over `𝒪[F]`. -/
abbrev glResidueMap : GL (Fin N) 𝒪[F] →* GL (Fin N) 𝓀[F] :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F])

/-- The inclusion of invertible matrices over `𝒪[F]` into `GL_N(F)`. -/
abbrev glIntegralInclusion : GL (Fin N) 𝒪[F] →* GL (Fin N) F :=
  Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem glIntegralInclusion_injective : Function.Injective (glIntegralInclusion F N) := by
  intro u v h
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact (IsFractionRing.injective 𝒪[F] F)
    (congrArg (fun g : GL (Fin N) F => (g : Matrix (Fin N) (Fin N) F) i j) h)

/-- Every invertible matrix over the residue field lifts to an invertible matrix over
`𝒪[F]`. This is the smooth Henselian lifting of the published
`IntegralModel.reduction_surjective`, applied to the standard model of `GL_N`. -/
theorem glResidueMap_surjective : Function.Surjective (glResidueMap F N) := by
  let : HenselianLocalRing 𝒪[F] := henselianLocalRing_integer
  intro g
  obtain ⟨x, hx⟩ := IntegralModel.reduction_surjective (generalLinearModelData F N).neutral
    (GeneralLinear.standardIntegralModel_isSmooth 𝒪[F] F (Fin N))
    ((generalLinearSpecialFibrePointsEquiv F N).symm g)
  refine ⟨GeneralLinear.standardSectionsEquiv 𝒪[F] F N x, ?_⟩
  rw [← generalLinearSpecialFibrePointsEquiv_reduction, hx, MulEquiv.apply_symm_apply]

/-- The preimage of `H ≤ GL_N(𝓀[F])` in `G^0(𝒪) = GL_N(𝒪[F])`, as a subgroup of the
rational points `G(F)` of the actual group scheme `GL_N`. -/
def generalLinearReductionPreimage (H : Subgroup (GL (Fin N) 𝓀[F])) :
    Subgroup (rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :=
  ((H.comap (glResidueMap F N)).map (glIntegralInclusion F N)).comap
    (GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)).toMonoidHom

variable {F N}

theorem mem_generalLinearReductionPreimage (H : Subgroup (GL (Fin N) 𝓀[F]))
    (g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :
    g ∈ generalLinearReductionPreimage F N H ↔
      ∃ u : GL (Fin N) 𝒪[F], glResidueMap F N u ∈ H ∧
        GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) g = glIntegralInclusion F N u := by
  simp only [generalLinearReductionPreimage, Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, h⟩
    exact ⟨u, hu, h.symm⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨u, hu, h.symm⟩

/-- Membership read off from any integral matrix of the point. -/
theorem mem_generalLinearReductionPreimage_of_eq (H : Subgroup (GL (Fin N) 𝓀[F]))
    {g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))}
    {u : GL (Fin N) 𝒪[F]}
    (hg : GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) g = glIntegralInclusion F N u) :
    g ∈ generalLinearReductionPreimage F N H ↔ glResidueMap F N u ∈ H := by
  rw [mem_generalLinearReductionPreimage]
  constructor
  · rintro ⟨v, hv, h⟩
    rwa [glIntegralInclusion_injective F N (hg.symm.trans h)]
  · intro hu
    exact ⟨u, hu, hg⟩

theorem generalLinearReductionPreimage_mono {H H' : Subgroup (GL (Fin N) 𝓀[F])}
    (h : H ≤ H') : generalLinearReductionPreimage F N H ≤ generalLinearReductionPreimage F N H' :=
  Subgroup.comap_mono (Subgroup.map_mono (Subgroup.comap_mono h))

variable (F N)

/-- The preimage of the whole group is `G^0(𝒪) = GL_N(𝒪[F])`. -/
theorem generalLinearReductionPreimage_top :
    generalLinearReductionPreimage F N ⊤ = (generalLinearModelData F N).neutral.integralPoints := by
  ext g
  rw [mem_generalLinearReductionPreimage, mem_generalLinear_integralPoints]
  simp only [Subgroup.mem_top, true_and]

/-- The preimage of the trivial group is `G(F)^{0+}`, the kernel of reduction. -/
theorem generalLinearReductionPreimage_bot :
    generalLinearReductionPreimage F N ⊥ = (generalLinearQuotientData F N).positivePoints := by
  ext g
  rw [mem_generalLinearReductionPreimage, mem_generalLinear_positivePoints]
  simp only [Subgroup.mem_bot]

/-- Relative indices of preimages are relative indices in `GL_N(𝓀[F])`. -/
theorem generalLinearReductionPreimage_relIndex (H H' : Subgroup (GL (Fin N) 𝓀[F])) :
    (generalLinearReductionPreimage F N H).relIndex (generalLinearReductionPreimage F N H') =
      H.relIndex H' := by
  rw [generalLinearReductionPreimage, generalLinearReductionPreimage, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective
      (GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)).surjective,
    Subgroup.relIndex_map_map_of_injective _ _ (glIntegralInclusion_injective F N),
    Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (glResidueMap_surjective F N)]

variable {F N}

/-- Normality transports to preimages. -/
theorem generalLinearReductionPreimage_normal {H H' : Subgroup (GL (Fin N) 𝓀[F])}
    (h : (H.subgroupOf H').Normal) :
    ((generalLinearReductionPreimage F N H).subgroupOf
      (generalLinearReductionPreimage F N H')).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨u, hu, hgu⟩ := (mem_generalLinearReductionPreimage H' (g : _)).mp g.2
  obtain ⟨v, hv, hnv⟩ := (mem_generalLinearReductionPreimage H (n : _)).mp hn
  have hv' : glResidueMap F N v ∈ H' :=
    (mem_generalLinearReductionPreimage_of_eq H' hnv).mp n.2
  have he : GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) ((g * n * g⁻¹ : _) : _) =
      glIntegralInclusion F N (u * v * u⁻¹) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hgu, hnv]
  rw [mem_generalLinearReductionPreimage_of_eq H he]
  have := h.conj_mem ⟨glResidueMap F N v, hv'⟩ (by rwa [Subgroup.mem_subgroupOf])
    ⟨glResidueMap F N u, hu⟩
  rw [Subgroup.mem_subgroupOf] at this
  simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using this

/-- `G(F)^{0+}` is normal in every preimage. -/
instance positivePoints_subgroupOf_generalLinearReductionPreimage_normal
    (H : Subgroup (GL (Fin N) 𝓀[F])) :
    ((generalLinearQuotientData F N).positivePoints.subgroupOf
      (generalLinearReductionPreimage F N H)).Normal := by
  rw [← generalLinearReductionPreimage_bot]
  exact generalLinearReductionPreimage_normal (by
    rw [Subgroup.bot_subgroupOf]
    infer_instance)

variable (F N) in
/-- Reduction on the preimage of `H`: a point goes to the residue of its (unique) integral
matrix. -/
def generalLinearReductionPreimageResidue (H : Subgroup (GL (Fin N) 𝓀[F])) :
    generalLinearReductionPreimage F N H →* H :=
  ((glResidueMap F N).subgroupComap H).comp
    ((((H.comap (glResidueMap F N)).equivMapOfInjective (glIntegralInclusion F N)
      (glIntegralInclusion_injective F N)).symm.toMonoidHom).comp
    ((GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)).toMonoidHom.subgroupComap _))

/-- The residue of a point is the reduction of any integral matrix of it. -/
theorem generalLinearReductionPreimageResidue_apply {H : Subgroup (GL (Fin N) 𝓀[F])}
    (g : generalLinearReductionPreimage F N H) {u : GL (Fin N) 𝒪[F]}
    (hg : GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) g = glIntegralInclusion F N u) :
    (generalLinearReductionPreimageResidue F N H g : GL (Fin N) 𝓀[F]) = glResidueMap F N u := by
  let E := (H.comap (glResidueMap F N)).equivMapOfInjective (glIntegralInclusion F N)
    (glIntegralInclusion_injective F N)
  have h1 : glIntegralInclusion F N
      ((E.symm ⟨GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) g, g.2⟩ :
        H.comap (glResidueMap F N)) : GL (Fin N) 𝒪[F]) = glIntegralInclusion F N u := by
    rw [← hg]
    exact congrArg Subtype.val (E.apply_symm_apply _)
  exact congrArg (glResidueMap F N) (glIntegralInclusion_injective F N h1)

theorem generalLinearReductionPreimageResidue_surjective (H : Subgroup (GL (Fin N) 𝓀[F])) :
    Function.Surjective (generalLinearReductionPreimageResidue F N H) := by
  intro h
  obtain ⟨u, hu⟩ := glResidueMap_surjective F N (h : GL (Fin N) 𝓀[F])
  obtain ⟨g, hg⟩ := (GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)).surjective
    (glIntegralInclusion F N u)
  have hmem : g ∈ generalLinearReductionPreimage F N H :=
    (mem_generalLinearReductionPreimage_of_eq H hg).mpr (hu ▸ h.2)
  refine ⟨⟨g, hmem⟩, Subtype.ext ?_⟩
  rw [generalLinearReductionPreimageResidue_apply ⟨g, hmem⟩ hg, hu]

/-- The kernel of the residue map on the preimage of `H` is `G(F)^{0+}`. -/
theorem generalLinearReductionPreimageResidue_ker (H : Subgroup (GL (Fin N) 𝓀[F])) :
    (generalLinearReductionPreimageResidue F N H).ker =
      (generalLinearQuotientData F N).positivePoints.subgroupOf
        (generalLinearReductionPreimage F N H) := by
  ext g
  obtain ⟨u, -, hgu⟩ := (mem_generalLinearReductionPreimage H (g : _)).mp g.2
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← generalLinearReductionPreimage_bot,
    mem_generalLinearReductionPreimage_of_eq ⊥ hgu, Subgroup.mem_bot, Subtype.ext_iff,
    generalLinearReductionPreimageResidue_apply g hgu, OneMemClass.coe_one]

variable (F N) in
/-- The preimage of `H` modulo `G(F)^{0+}` is `H`. -/
def generalLinearReductionPreimageQuotientEquiv (H : Subgroup (GL (Fin N) 𝓀[F])) :
    generalLinearReductionPreimage F N H ⧸
        (generalLinearQuotientData F N).positivePoints.subgroupOf
          (generalLinearReductionPreimage F N H) ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq (generalLinearReductionPreimageResidue_ker H).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (generalLinearReductionPreimageResidue_surjective H))

/-- Entries of the reduction of an integral matrix are residues of its entries. -/
theorem glResidueMap_apply (u : GL (Fin N) 𝒪[F]) (i j : Fin N) :
    (glResidueMap F N u : Matrix (Fin N) (Fin N) 𝓀[F]) i j =
      IsLocalRing.residue 𝒪[F] ((u : Matrix (Fin N) (Fin N) 𝒪[F]) i j) :=
  rfl

/-- The reduction is upper triangular exactly when the strictly lower entries lie in the
maximal ideal. -/
theorem glResidueMap_isUpperTriangular_iff (u : GL (Fin N) 𝒪[F]) :
    (glResidueMap F N u : Matrix (Fin N) (Fin N) 𝓀[F]).IsUpperTriangular ↔
      ∀ i j : Fin N, j < i →
        (u : Matrix (Fin N) (Fin N) 𝒪[F]) i j ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
  constructor
  · intro h i j hij
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact h hij
  · intro h i j hij
    rw [glResidueMap_apply, IsLocalRing.residue_eq_zero_iff]
    exact h i j hij

/-- A diagonal entry of the reduction is `1` exactly when the entry is `1` modulo the
maximal ideal. -/
theorem glResidueMap_apply_eq_one_iff (u : GL (Fin N) 𝒪[F]) (i : Fin N) :
    (glResidueMap F N u : Matrix (Fin N) (Fin N) 𝓀[F]) i i = 1 ↔
      (u : Matrix (Fin N) (Fin N) 𝒪[F]) i i - 1 ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
  rw [glResidueMap_apply, ← sub_eq_zero, ← map_one (IsLocalRing.residue 𝒪[F]), ← map_sub,
    IsLocalRing.residue_eq_zero_iff]

end Langlands.BruhatTits.IntegralModels

/-! ### The singleton shape over a finite field -/

namespace Langlands.GeneralLinear.BlockShape

variable {n : ℕ} (K : Type u) [Field K] [Finite K]

/-- `GL_1` over a finite field with `q` elements has `q - 1` elements. -/
theorem card_generalLinear_one_of_finite :
    Nat.card (Langlands.GeneralLinear 1 K) = Nat.card K - 1 := by
  let : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_GL_field, Fin.prod_univ_one, Nat.card_eq_fintype_card]
  simp

/-- Over a finite field with `q` elements, the Levi factor of the singleton shape, `n`
copies of `GL_1`, has `(q - 1)^n` elements. -/
theorem card_singletons_levi : Nat.card ((singletons n).Levi K) = (Nat.card K - 1) ^ n := by
  rw [Nat.card_pi]
  simp only [card_generalLinear_one_of_finite, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, singletons_length]

/-- The radical of the singleton shape (the upper unipotent group) over a commutative ring
`R` has `|R|^(n choose 2)` elements, as natural-number cardinalities: its coordinates are one
entry for every pair `i < j`. Over a finite field with `q` elements this is `q^(n choose 2)`. -/
theorem card_singletons_unipotentRadical (R : Type u) [CommRing R] :
    Nat.card ((singletons n).unipotentRadical R) = Nat.card R ^ n.choose 2 := by
  rw [Nat.card_congr ((singletons n).radicalCoordinates R), RadicalCoordinates, Nat.card_pi]
  simp only [Matrix.card_matrix, Nat.card_unique, mul_one, pow_one, Finset.prod_const,
    Finset.card_univ]
  congr 1
  rw [Fintype.card_subtype]
  simpa using Fintype.card_product_filter_lt (α := Fin n)

/-- Over a finite field with `q` elements, the upper triangular group has
`q^(n choose 2) (q - 1)^n` elements, by the factorization `g = u m` of the published
`decomposition`. -/
theorem card_singletons_parabolic :
    Nat.card ((singletons n).parabolic K) = Nat.card K ^ n.choose 2 * (Nat.card K - 1) ^ n := by
  rw [Nat.card_congr ((singletons n).decomposition K), Nat.card_prod,
    card_singletons_unipotentRadical K, card_singletons_levi]

/-- The singleton radical has index `(q - 1)^n` in the upper triangular group: it is the
kernel of the surjective projection to the Levi factor. -/
theorem index_singletons_unipotentRadical :
    ((singletons n).unipotentRadical K).index = (Nat.card K - 1) ^ n := by
  rw [unipotentRadical, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr fun m => ⟨_, leviProjection_section _ K m⟩, Subgroup.card_top,
    card_singletons_levi]

/-- The upper unipotent matrix subgroup, viewed inside the upper triangular group, is the
singleton radical. -/
theorem singletons_unipotentSubgroup_subgroupOf (R : Type u) [CommRing R] :
    ((singletons n).unipotentSubgroup R).subgroupOf ((singletons n).parabolic R) =
      (singletons n).unipotentRadical R :=
  Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _

theorem singletons_unipotentSubgroup_le (R : Type u) [CommRing R] :
    (singletons n).unipotentSubgroup R ≤ (singletons n).parabolic R :=
  Subgroup.map_subtype_le _

/-- The upper unipotent matrix subgroup over `R` has `|R|^(n choose 2)` elements, as
natural-number cardinalities; `q^(n choose 2)` over a finite field with `q` elements. -/
theorem card_singletons_unipotentSubgroup (R : Type u) [CommRing R] :
    Nat.card ((singletons n).unipotentSubgroup R) = Nat.card R ^ n.choose 2 := by
  rw [unipotentSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    card_singletons_unipotentRadical]

end Langlands.GeneralLinear.BlockShape

/-! ### The standard Iwahori subgroup -/

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme
open Langlands.GeneralLinear.BlockShape (singletons)

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : ℕ)

/-- The standard Iwahori subgroup `I` of `GL_N(F)`: the preimage in `GL_N(𝒪[F])` of the
upper triangular group `B(𝓀[F])`. -/
def generalLinearIwahoriPoints :
    Subgroup (rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :=
  generalLinearReductionPreimage F N ((singletons N).parabolic 𝓀[F])

/-- The subgroup `I^+`: the preimage in `GL_N(𝒪[F])` of the upper unipotent group
`U(𝓀[F])`. -/
def generalLinearIwahoriPositivePoints :
    Subgroup (rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :=
  generalLinearReductionPreimage F N ((singletons N).unipotentSubgroup 𝓀[F])

variable {F N}

/-- `I` consists of the points whose matrix is an invertible integral matrix with strictly
lower entries in the maximal ideal. -/
theorem mem_generalLinearIwahoriPoints
    (g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :
    g ∈ generalLinearIwahoriPoints F N ↔
      ∃ u : GL (Fin N) 𝒪[F],
        (∀ i j : Fin N, j < i →
          (u : Matrix (Fin N) (Fin N) 𝒪[F]) i j ∈ IsLocalRing.maximalIdeal 𝒪[F]) ∧
        GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) g = glIntegralInclusion F N u := by
  rw [generalLinearIwahoriPoints, mem_generalLinearReductionPreimage]
  simp only [Langlands.GeneralLinear.BlockShape.singletons_mem_parabolic_iff,
    glResidueMap_isUpperTriangular_iff]

/-- `I^+` consists of the points whose matrix is an invertible integral matrix with strictly
lower entries in the maximal ideal and diagonal entries congruent to `1`. -/
theorem mem_generalLinearIwahoriPositivePoints
    (g : rationalPoints (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))) :
    g ∈ generalLinearIwahoriPositivePoints F N ↔
      ∃ u : GL (Fin N) 𝒪[F],
        ((∀ i j : Fin N, j < i →
          (u : Matrix (Fin N) (Fin N) 𝒪[F]) i j ∈ IsLocalRing.maximalIdeal 𝒪[F]) ∧
          ∀ i : Fin N,
            (u : Matrix (Fin N) (Fin N) 𝒪[F]) i i - 1 ∈ IsLocalRing.maximalIdeal 𝒪[F]) ∧
        GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) g = glIntegralInclusion F N u := by
  rw [generalLinearIwahoriPositivePoints, mem_generalLinearReductionPreimage,
    Langlands.GeneralLinear.BlockShape.singletons_unipotentSubgroup]
  change (∃ u, ((glResidueMap F N u : Matrix (Fin N) (Fin N) 𝓀[F]).IsUpperTriangular ∧
    ∀ i, (glResidueMap F N u : Matrix (Fin N) (Fin N) 𝓀[F]) i i = 1) ∧ _) ↔ _
  simp only [glResidueMap_isUpperTriangular_iff, glResidueMap_apply_eq_one_iff]

variable (F N)

/-- `I^+ ⊆ I`. -/
theorem generalLinearIwahoriPositivePoints_le :
    generalLinearIwahoriPositivePoints F N ≤ generalLinearIwahoriPoints F N :=
  generalLinearReductionPreimage_mono (Langlands.GeneralLinear.BlockShape.singletons_unipotentSubgroup_le _)

/-- `G(F)^{0+} ⊆ I^+`. -/
theorem positivePoints_le_generalLinearIwahoriPositivePoints :
    (generalLinearQuotientData F N).positivePoints ≤ generalLinearIwahoriPositivePoints F N := by
  rw [← generalLinearReductionPreimage_bot]
  exact generalLinearReductionPreimage_mono bot_le

/-- `I ⊆ G^0(𝒪) = GL_N(𝒪[F])`. -/
theorem generalLinearIwahoriPoints_le_integralPoints :
    generalLinearIwahoriPoints F N ≤ (generalLinearModelData F N).neutral.integralPoints := by
  rw [← generalLinearReductionPreimage_top]
  exact generalLinearReductionPreimage_mono le_top

/-- `[G^0(𝒪) : I] = [GL_N(𝓀[F]) : B(𝓀[F])]`. -/
theorem generalLinearIwahoriPoints_relIndex :
    (generalLinearIwahoriPoints F N).relIndex (generalLinearModelData F N).neutral.integralPoints =
      ((singletons N).parabolic 𝓀[F]).index := by
  rw [← generalLinearReductionPreimage_top, generalLinearIwahoriPoints,
    generalLinearReductionPreimage_relIndex, Subgroup.relIndex_top_right]

/-- `[I : I^+] = (q - 1)^N`, where `q` is the cardinality of the residue field. -/
theorem generalLinearIwahoriPositivePoints_relIndex :
    (generalLinearIwahoriPositivePoints F N).relIndex (generalLinearIwahoriPoints F N) =
      (Nat.card 𝓀[F] - 1) ^ N := by
  rw [generalLinearIwahoriPositivePoints, generalLinearIwahoriPoints,
    generalLinearReductionPreimage_relIndex, Subgroup.relIndex,
    Langlands.GeneralLinear.BlockShape.singletons_unipotentSubgroup_subgroupOf,
    Langlands.GeneralLinear.BlockShape.index_singletons_unipotentRadical]

/-- `[I^+ : G(F)^{0+}] = q^(N choose 2)`. -/
theorem positivePoints_relIndex_generalLinearIwahoriPositivePoints :
    (generalLinearQuotientData F N).positivePoints.relIndex
        (generalLinearIwahoriPositivePoints F N) = Nat.card 𝓀[F] ^ N.choose 2 := by
  rw [← generalLinearReductionPreimage_bot, generalLinearIwahoriPositivePoints,
    generalLinearReductionPreimage_relIndex, Subgroup.relIndex_bot_left,
    Langlands.GeneralLinear.BlockShape.card_singletons_unipotentSubgroup]

/-- The order formula for `[G^0(𝒪) : I]`:
`q^(N choose 2) (q - 1)^N [G^0(𝒪) : I] = ∏_{i < N} (q^N - q^i) = |GL_N(𝓀[F])|`. -/
theorem generalLinearIwahoriPoints_relIndex_mul :
    Nat.card 𝓀[F] ^ N.choose 2 * (Nat.card 𝓀[F] - 1) ^ N *
        (generalLinearIwahoriPoints F N).relIndex
          (generalLinearModelData F N).neutral.integralPoints =
      ∏ i : Fin N, (Nat.card 𝓀[F] ^ N - Nat.card 𝓀[F] ^ (i : ℕ)) := by
  let : Fintype 𝓀[F] := Fintype.ofFinite _
  rw [generalLinearIwahoriPoints_relIndex,
    ← Langlands.GeneralLinear.BlockShape.card_singletons_parabolic, Subgroup.card_mul_index,
    Matrix.card_GL_field, Nat.card_eq_fintype_card]

/-- For `GL_2`, `[G^0(𝒪) : I] = q + 1`. -/
theorem generalLinearIwahoriPoints_relIndex_two :
    (generalLinearIwahoriPoints F 2).relIndex
        (generalLinearModelData F 2).neutral.integralPoints = Nat.card 𝓀[F] + 1 := by
  have h := generalLinearIwahoriPoints_relIndex_mul F 2
  have hq : 1 < Nat.card 𝓀[F] := Finite.one_lt_card
  obtain ⟨r, hr⟩ : ∃ r, Nat.card 𝓀[F] = r + 1 := ⟨Nat.card 𝓀[F] - 1, by omega⟩
  have hr1 : 1 ≤ r := by omega
  rw [hr] at h ⊢
  rw [Fin.prod_univ_two] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, Nat.add_sub_cancel] at h
  have h1 : (r + 1) ^ 2 - 1 = r * (r + 2) := by
    rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
    ring
  have h2 : (r + 1) ^ 2 - (r + 1) = (r + 1) * r := by
    rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
    ring
  rw [h1, h2, show (2 : ℕ).choose 2 = 1 by rfl, pow_one] at h
  have hpos : 0 < (r + 1) * r ^ 2 := by positivity
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  linear_combination h

variable {F N}

/-- For `N ≤ 1` every invertible matrix is upper triangular, so `I = G^0(𝒪)`. -/
theorem generalLinearIwahoriPoints_of_le_one (hN : N ≤ 1) :
    generalLinearIwahoriPoints F N = (generalLinearModelData F N).neutral.integralPoints := by
  rw [← generalLinearReductionPreimage_top, generalLinearIwahoriPoints]
  congr 1
  refine eq_top_iff.mpr fun g _ => ?_
  rw [Langlands.GeneralLinear.BlockShape.singletons_mem_parabolic_iff]
  intro i j hij
  have hi := i.2
  have hij' := Fin.lt_def.mp hij
  omega

/-- For `N ≤ 1` the only upper unipotent matrix is `1`, so `I^+ = G(F)^{0+}`. -/
theorem generalLinearIwahoriPositivePoints_of_le_one (hN : N ≤ 1) :
    generalLinearIwahoriPositivePoints F N = (generalLinearQuotientData F N).positivePoints := by
  rw [← generalLinearReductionPreimage_bot, generalLinearIwahoriPositivePoints]
  congr 1
  refine eq_bot_iff.mpr fun g hg => ?_
  rw [Langlands.GeneralLinear.BlockShape.singletons_unipotentSubgroup] at hg
  rw [Subgroup.mem_bot]
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hij : i = j := Fin.ext (by have := i.2; have := j.2; omega)
  subst hij
  rw [Units.val_one, Matrix.one_apply_eq]
  exact hg.2 i

/-- For `N ≥ 2`, `I` is a proper subgroup of `G^0(𝒪)`: the lower transvection
`1 + E_{1,0}` over `𝓀[F]` is not upper triangular, so `B(𝓀[F]) ≠ GL_N(𝓀[F])`. -/
theorem generalLinearIwahoriPoints_lt_integralPoints (hN : 2 ≤ N) :
    generalLinearIwahoriPoints F N < (generalLinearModelData F N).neutral.integralPoints := by
  refine lt_of_le_of_ne (generalLinearIwahoriPoints_le_integralPoints F N) fun h => ?_
  have hidx := generalLinearIwahoriPoints_relIndex F N
  rw [h, Subgroup.relIndex_self, eq_comm, Subgroup.index_eq_one] at hidx
  let i1 : Fin N := ⟨1, by omega⟩
  let i0 : Fin N := ⟨0, by omega⟩
  have hne : i1 ≠ i0 := by simp [i1, i0, Fin.ext_iff]
  have hmem : Langlands.GeneralLinear.transvectionUnit i1 i0 hne (1 : 𝓀[F]) ∈
      (singletons N).parabolic 𝓀[F] := hidx ▸ Subgroup.mem_top _
  rw [Langlands.GeneralLinear.BlockShape.singletons_mem_parabolic_iff] at hmem
  have h10 := hmem (show i0 < i1 from Fin.mk_lt_mk.mpr one_pos)
  change Matrix.transvection i1 i0 (1 : 𝓀[F]) i1 i0 = 0 at h10
  rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.single_apply_same,
    zero_add] at h10
  exact one_ne_zero h10

/-- `I^+` is normal in `I`. -/
theorem generalLinearIwahoriPositivePoints_normal :
    ((generalLinearIwahoriPositivePoints F N).subgroupOf (generalLinearIwahoriPoints F N)).Normal :=
  generalLinearReductionPreimage_normal (by
    rw [Langlands.GeneralLinear.BlockShape.singletons_unipotentSubgroup_subgroupOf]
    infer_instance)

instance generalLinearIwahoriPositivePoints_subgroupOf_normal :
    ((generalLinearIwahoriPositivePoints F N).subgroupOf
    (generalLinearIwahoriPoints F N)).Normal :=
  generalLinearIwahoriPositivePoints_normal

/-- `G(F)^{0+}` is normal in `I`. -/
theorem positivePoints_normal_generalLinearIwahoriPoints :
    ((generalLinearQuotientData F N).positivePoints.subgroupOf
      (generalLinearIwahoriPoints F N)).Normal :=
  positivePoints_subgroupOf_generalLinearReductionPreimage_normal _

variable (F N) in
/-- The projection `I → B(𝓀[F]) → (GL_1(𝓀[F]))^N`: reduce, then take the diagonal. -/
def generalLinearIwahoriDiagonal :
    generalLinearIwahoriPoints F N →* (singletons N).Levi 𝓀[F] :=
  ((singletons N).leviProjection 𝓀[F]).comp
    (generalLinearReductionPreimageResidue F N ((singletons N).parabolic 𝓀[F]))

theorem generalLinearIwahoriDiagonal_surjective :
    Function.Surjective (generalLinearIwahoriDiagonal F N) :=
  Function.Surjective.comp (g := (singletons N).leviProjection 𝓀[F])
    (fun m => ⟨_, Langlands.GeneralLinear.BlockShape.leviProjection_section _ 𝓀[F] m⟩)
    (generalLinearReductionPreimageResidue_surjective _)

/-- The kernel of the diagonal projection on `I` is `I^+`. -/
theorem generalLinearIwahoriDiagonal_ker :
    (generalLinearIwahoriDiagonal F N).ker =
      (generalLinearIwahoriPositivePoints F N).subgroupOf (generalLinearIwahoriPoints F N) := by
  ext g
  obtain ⟨u, -, hgu⟩ :=
    (mem_generalLinearReductionPreimage ((singletons N).parabolic 𝓀[F]) (g : _)).mp g.2
  rw [Subgroup.mem_subgroupOf, generalLinearIwahoriPositivePoints,
    mem_generalLinearReductionPreimage_of_eq _ hgu,
    ← generalLinearReductionPreimageResidue_apply (H := (singletons N).parabolic 𝓀[F]) g hgu,
    MonoidHom.mem_ker]
  change _ ∈ (singletons N).unipotentRadical 𝓀[F] ↔ _
  exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)).symm

variable (F N) in
/-- `I/I^+` is the diagonal torus `(GL_1(𝓀[F]))^N`. -/
def generalLinearIwahoriQuotientEquiv :
    generalLinearIwahoriPoints F N ⧸
        (generalLinearIwahoriPositivePoints F N).subgroupOf (generalLinearIwahoriPoints F N) ≃*
      (singletons N).Levi 𝓀[F] :=
  (QuotientGroup.quotientMulEquivOfEq generalLinearIwahoriDiagonal_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ generalLinearIwahoriDiagonal_surjective)

end Langlands.BruhatTits.IntegralModels
