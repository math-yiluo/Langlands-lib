import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Spherical
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TestFunctions
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentHeightVolume
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentHeightIntegrability
import Langlands.Representation.Plancherel.RationalModerateGrowthStatement
import Langlands.Representation.Plancherel.FieldUnitsTopologyProof
import Langlands.Representation.Jacquet.StandardFixedVectorStructure
import Langlands.Group.HaarModulus
import Langlands.AlgebraicGeometry.PointTopology.RationalPointHaarProof
import Langlands.AlgebraicGeometry.PointTopology.RationalPointEvaluation
import Langlands.BruhatTits.Iwasawa.PointProducts

/-! # Waldspurger's weights `Ξ` and `σ` and the Schwartz space on actual rational points

For a group scheme `G` over a nonarchimedean local field `F`, a split torus `i : S → G` and a
cocharacter `ν`, this module realizes on `G(F)` the weights of Waldspurger's Harish-Chandra
Schwartz space: the modulus `δ₀` of the minimal standard parabolic `P₀(F)` acting on its radical
`U₀(F)`, the spherical function `Ξ` attached to a compact open subgroup `K` with `G(F) = P₀(F) K`,
and the height `σ = log ‖·‖` of a closed matrix representation. It then forms the space
`C(G)` of the Library's generic construction for these weights and proves its basic properties.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Normalizer

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The actual standard parabolic points normalize the actual standard radical points. -/
theorem standardParabolicPoints_le_normalizer_standardUnipotentPoints (i : S.toGrp ⟶ G)
    (ν : cocharacterLattice S) (J : Set (characterLattice S)) :
    standardParabolicPoints i ν J ≤
      Subgroup.normalizer (standardUnipotentPoints i ν J : Set (rationalPoints G)) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro u
  have hp' := (mem_standardParabolic i ν).1 hp
  have hpinv := (mem_standardParabolic i ν).1 ((standardParabolicPoints i ν J).inv_mem hp)
  constructor
  · intro hu
    refine (mem_standardUnipotent i ν).2 fun ζ hζ => ?_
    exact Dynamic.conj_mem_unipotent _ (hp' ζ hζ) ((mem_standardUnipotent i ν).1 hu ζ hζ)
  · intro hu
    refine (mem_standardUnipotent i ν).2 fun ζ hζ => ?_
    have h := Dynamic.conj_mem_unipotent _ (hpinv ζ hζ)
      ((mem_standardUnipotent i ν).1 hu ζ hζ)
    have heq : p⁻¹ * (p * u * p⁻¹) * p⁻¹⁻¹ = u := by group
    rwa [heq] at h

omit [IsAffineHom G.X.hom] in
/-- The Library's actual Iwasawa product equalities `G(F) = P K = K P` give the factorization
`G = P K` used by the spherical function. -/
theorem isIwasawaPair_of_pointProductEqualities {P K : Subgroup (rationalPoints G)}
    (h : BruhatTits.Iwasawa.PointProductEqualities P K) : IsIwasawaPair P K := by
  intro g
  have hg : g ∈ (P : Set (rationalPoints G)) * (K : Set (rationalPoints G)) :=
    h.1 ▸ Set.mem_univ g
  obtain ⟨p, hp, k, hk, hpk⟩ := Set.mem_mul.mp hg
  exact ⟨p, hp, k, hk, hpk.symm⟩

end Normalizer

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local instance rationalWeightsIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance rationalWeightsTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance rationalWeightsTopologicalGroup : IsTopologicalGroup (rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G
local instance rationalWeightsT2Field : T2Space F := BruhatTits.localField_t2Space F
local instance rationalWeightsLocallyCompact : LocallyCompactSpace (rationalPoints G) :=
  rationalPoint_locallyCompactSpace F G
local instance rationalWeightsMeasurableSpace : MeasurableSpace (rationalPoints G) := borel _
local instance rationalWeightsBorelSpace : BorelSpace (rationalPoints G) := ⟨rfl⟩

section Modulus

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- **Waldspurger's `δ₀`**: the Haar modulus of the conjugation action of the actual minimal
standard parabolic `P₀(F) = standardParabolicPoints i ν ∅` on its radical
`U₀(F) = standardUnipotentPoints i ν ∅`, so that `μ(p E p⁻¹) = δ₀(p) μ(E)` for a Haar measure
`μ` on `U₀(F)`. -/
def rationalMinimalModulus : standardParabolicPoints i ν ∅ →* ℝ≥0ˣ :=
  HaarModulus.closedRestrictCharacter (standardUnipotentPoints i ν ∅)
    (isClosed_standardUnipotentPoints i ν ∅) (standardParabolicPoints i ν ∅)
    (standardParabolicPoints_le_normalizer_standardUnipotentPoints i ν ∅)

/-- `δ₀` is trivial on `P₀(F) ∩ K` for every compact open subgroup `K`: conjugation by such an
element preserves the compact open subgroup `K ∩ U₀(F)` of `U₀(F)`. -/
theorem rationalMinimalModulus_eq_one {K : Subgroup (rationalPoints G)}
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (p : standardParabolicPoints i ν ∅) (hp : (p : rationalPoints G) ∈ K) :
    rationalMinimalModulus i ν p = 1 := by
  have hU : IsClosed (standardUnipotentPoints i ν ∅ : Set (rationalPoints G)) :=
    isClosed_standardUnipotentPoints i ν ∅
  have : LocallyCompactSpace (standardUnipotentPoints i ν ∅) := hU.locallyCompactSpace
  let KU : OpenSubgroup (standardUnipotentPoints i ν ∅) :=
    (⟨K, hKo⟩ : OpenSubgroup (rationalPoints G)).comap (standardUnipotentPoints i ν ∅).subtype
      continuous_subtype_val
  have hKU : IsCompact (KU : Set (standardUnipotentPoints i ν ∅)) :=
    hU.isClosedEmbedding_subtypeVal.isCompact_preimage hKc
  have hpn : (p : rationalPoints G) ∈
      Subgroup.normalizer (standardUnipotentPoints i ν ∅ : Set (rationalPoints G)) :=
    standardParabolicPoints_le_normalizer_standardUnipotentPoints i ν ∅ p.2
  have h := HaarModulus.normalizerCharacter_eq_one_of_preimage
    (standardUnipotentPoints i ν ∅) KU hKU ⟨p, hpn⟩ ?_
  · exact h
  · ext u
    change (p : rationalPoints G) * (u : rationalPoints G) * (p : rationalPoints G)⁻¹ ∈ K ↔
      (u : rationalPoints G) ∈ K
    constructor
    · intro hu
      have h1 : (u : rationalPoints G) = (p : rationalPoints G)⁻¹ *
          ((p : rationalPoints G) * (u : rationalPoints G) * (p : rationalPoints G)⁻¹) *
            (p : rationalPoints G) := by group
      rw [h1]
      exact K.mul_mem (K.mul_mem (K.inv_mem hp) hu) hp
    · intro hu
      exact K.mul_mem (K.mul_mem hp hu) (K.inv_mem hp)

/-- `δ₀` is trivial at every point of `U₀(F)` lying in a compact open subgroup of `U₀(F)`.
Hence, if `U₀(F)` is the union of its compact open subgroups, `δ₀(p)` depends only on the
Levi component of `p ∈ P₀(F)`. -/
theorem rationalMinimalModulus_eq_one_of_mem_compactOpen (p : standardParabolicPoints i ν ∅)
    (hpU : (p : rationalPoints G) ∈ standardUnipotentPoints i ν ∅)
    (L : OpenSubgroup (standardUnipotentPoints i ν ∅))
    (hL : IsCompact (L : Set (standardUnipotentPoints i ν ∅)))
    (hpL : (⟨p, hpU⟩ : standardUnipotentPoints i ν ∅) ∈ L) :
    rationalMinimalModulus i ν p = 1 := by
  have hU : IsClosed (standardUnipotentPoints i ν ∅ : Set (rationalPoints G)) :=
    isClosed_standardUnipotentPoints i ν ∅
  have : LocallyCompactSpace (standardUnipotentPoints i ν ∅) := hU.locallyCompactSpace
  have hpn : (p : rationalPoints G) ∈
      Subgroup.normalizer (standardUnipotentPoints i ν ∅ : Set (rationalPoints G)) :=
    standardParabolicPoints_le_normalizer_standardUnipotentPoints i ν ∅ p.2
  have h := HaarModulus.normalizerCharacter_eq_one_of_preimage
    (standardUnipotentPoints i ν ∅) L hL ⟨p, hpn⟩ ?_
  · exact h
  · set q : standardUnipotentPoints i ν ∅ := ⟨p, hpU⟩
    ext u
    have he : HaarModulus.normalizerConj (standardUnipotentPoints i ν ∅) ⟨p, hpn⟩ u =
        q * u * q⁻¹ := Subtype.ext rfl
    simp only [Set.mem_preimage, SetLike.mem_coe, he]
    constructor
    · intro hu
      have h1 : u = q⁻¹ * (q * u * q⁻¹) * q := by group
      rw [h1]
      exact L.mul_mem (L.mul_mem (L.inv_mem hpL) hu) hpL
    · intro hu
      exact L.mul_mem (L.mul_mem hpL hu) (L.inv_mem hpL)

end Modulus

section Xi

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {K : Subgroup (rationalPoints G)}

/-- **Waldspurger's spherical function `Ξ`** (II.1) on the actual rational points, for a compact
subgroup `K` with `G(F) = P₀(F) K`: `Ξ(g) = ∫_K δ₀(p(kg))^{1/2} dk` with the Haar probability
measure of `K`, where `kg = p(kg) k'` with `p(kg) ∈ P₀(F)` and `k' ∈ K`. It is the Library's
generic `xi` for `P = P₀(F)` and `δ = rationalMinimalModulus i ν`. -/
def rationalXi (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K) (g : rationalPoints G) : ℝ :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  xi hPK (rationalMinimalModulus i ν) g

variable (hKo : IsOpen (K : Set (rationalPoints G)))
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)

include hKo in
theorem rationalXi_one : rationalXi hKc hPK 1 = 1 := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  exact xi_one (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp)

include hKo in
/-- `Ξ` is positive. -/
theorem rationalXi_pos (g : rationalPoints G) : 0 < rationalXi hKc hPK g := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  exact xi_pos (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp) hKo g

include hKo in
/-- `Ξ` is bi-`K`-invariant (first assertion of Waldspurger's Lemma II.1.1). -/
theorem rationalXi_mul_mul {k₁ k₂ : rationalPoints G} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (g : rationalPoints G) : rationalXi hKc hPK (k₁ * g * k₂) = rationalXi hKc hPK g := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  exact xi_mul_mul (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp) hk₁ hk₂ g

include hKo in
/-- `Ξ` is continuous (indeed locally constant). -/
theorem continuous_rationalXi : Continuous (rationalXi hKc hPK) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  exact continuous_xi (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp) hKo

end Xi

section Height

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-- **Waldspurger's height `σ = log ‖·‖`** (I.1) on the actual rational points, for a matrix
representation `ρ : G → GL_n`: the logarithm of the largest normalized absolute value of an
entry of `ρ(g)` or `ρ(g)⁻¹`. -/
def rationalHeight (ρ : MatrixRepresentation G n) (g : rationalPoints G) : ℝ :=
  Real.log (MatrixRepresentation.rationalMatrixNorm F ρ g)

variable (ρ : MatrixRepresentation G n)

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem rationalMatrixNorm_pos (g : rationalPoints G) :
    0 < MatrixRepresentation.rationalMatrixNorm F ρ g :=
  lt_of_lt_of_le one_pos (MatrixRepresentation.one_le_rationalMatrixNorm F ρ g)

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem rationalHeight_nonneg (g : rationalPoints G) : 0 ≤ rationalHeight (F := F) ρ g :=
  Real.log_nonneg (MatrixRepresentation.one_le_rationalMatrixNorm F ρ g)

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem rationalHeight_one : rationalHeight (F := F) ρ 1 = 0 := by
  simp [rationalHeight]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem rationalHeight_inv (g : rationalPoints G) :
    rationalHeight (F := F) ρ g⁻¹ = rationalHeight (F := F) ρ g := by
  simp [rationalHeight]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- `σ(gh) ≤ σ(g) + σ(h)`. -/
theorem rationalHeight_mul_le (g h : rationalPoints G) :
    rationalHeight (F := F) ρ (g * h) ≤
      rationalHeight (F := F) ρ g + rationalHeight (F := F) ρ h := by
  unfold rationalHeight
  rw [← Real.log_mul (rationalMatrixNorm_pos ρ g).ne' (rationalMatrixNorm_pos ρ h).ne']
  exact Real.log_le_log (rationalMatrixNorm_pos ρ _)
    (MatrixRepresentation.rationalMatrixNorm_mul_le F ρ g h)

theorem continuous_rationalHeight : Continuous (rationalHeight (F := F) ρ) :=
  (MatrixRepresentation.continuous_rationalMatrixNorm F ρ).log
    fun g => (rationalMatrixNorm_pos ρ g).ne'

/-- The points of norm at most one, `ρ⁻¹(GL_n(𝒪))` on rational points. -/
def rationalHeightSubgroup : Subgroup (rationalPoints G) where
  carrier := {g | MatrixRepresentation.rationalMatrixNorm F ρ g ≤ 1}
  mul_mem' {a b} ha hb :=
    (MatrixRepresentation.rationalMatrixNorm_mul_le F ρ a b).trans
      ((mul_le_mul ha hb (rationalMatrixNorm_pos ρ b).le zero_le_one).trans (one_mul 1).le)
  one_mem' := by simp
  inv_mem' {a} ha := by simpa using ha

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem mem_rationalHeightSubgroup {g : rationalPoints G} :
    g ∈ rationalHeightSubgroup (F := F) ρ ↔ MatrixRepresentation.rationalMatrixNorm F ρ g ≤ 1 :=
  Iff.rfl

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The norm is bi-invariant under `ρ⁻¹(GL_n(𝒪))`. -/
theorem rationalMatrixNorm_mul_mul {k₁ k₂ : rationalPoints G}
    (hk₁ : k₁ ∈ rationalHeightSubgroup (F := F) ρ)
    (hk₂ : k₂ ∈ rationalHeightSubgroup (F := F) ρ)
    (g : rationalPoints G) :
    MatrixRepresentation.rationalMatrixNorm F ρ (k₁ * g * k₂) =
      MatrixRepresentation.rationalMatrixNorm F ρ g := by
  have hle : ∀ {a b : rationalPoints G}, a ∈ rationalHeightSubgroup (F := F) ρ →
      b ∈ rationalHeightSubgroup (F := F) ρ → ∀ x : rationalPoints G,
        MatrixRepresentation.rationalMatrixNorm F ρ (a * x * b) ≤
          MatrixRepresentation.rationalMatrixNorm F ρ x := by
    intro a b ha hb x
    have ha' : MatrixRepresentation.rationalMatrixNorm F ρ a ≤ 1 := ha
    have hb' : MatrixRepresentation.rationalMatrixNorm F ρ b ≤ 1 := hb
    calc MatrixRepresentation.rationalMatrixNorm F ρ (a * x * b)
        ≤ MatrixRepresentation.rationalMatrixNorm F ρ (a * x) *
            MatrixRepresentation.rationalMatrixNorm F ρ b :=
          MatrixRepresentation.rationalMatrixNorm_mul_le F ρ _ _
      _ ≤ MatrixRepresentation.rationalMatrixNorm F ρ a *
            MatrixRepresentation.rationalMatrixNorm F ρ x *
            MatrixRepresentation.rationalMatrixNorm F ρ b :=
          mul_le_mul_of_nonneg_right (MatrixRepresentation.rationalMatrixNorm_mul_le F ρ _ _)
            (rationalMatrixNorm_pos ρ b).le
      _ ≤ 1 * MatrixRepresentation.rationalMatrixNorm F ρ x * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right ha' (rationalMatrixNorm_pos ρ x).le) hb'
            (rationalMatrixNorm_pos ρ b).le (by simpa using (rationalMatrixNorm_pos ρ x).le)
      _ = MatrixRepresentation.rationalMatrixNorm F ρ x := by ring
  refine le_antisymm (hle hk₁ hk₂ g) ?_
  have h := hle ((rationalHeightSubgroup (F := F) ρ).inv_mem hk₁)
    ((rationalHeightSubgroup (F := F) ρ).inv_mem hk₂) (k₁ * g * k₂)
  have heq : k₁⁻¹ * (k₁ * g * k₂) * k₂⁻¹ = g := by group
  rwa [heq] at h

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- `σ` is bi-invariant under `ρ⁻¹(GL_n(𝒪))`. -/
theorem rationalHeight_mul_mul {k₁ k₂ : rationalPoints G}
    (hk₁ : k₁ ∈ rationalHeightSubgroup (F := F) ρ)
    (hk₂ : k₂ ∈ rationalHeightSubgroup (F := F) ρ)
    (g : rationalPoints G) :
    rationalHeight (F := F) ρ (k₁ * g * k₂) = rationalHeight (F := F) ρ g := by
  unfold rationalHeight
  rw [rationalMatrixNorm_mul_mul ρ hk₁ hk₂ g]

/-- `ρ⁻¹(GL_n(𝒪))` is open in `G(F)`. -/
theorem isOpen_rationalHeightSubgroup :
    IsOpen (rationalHeightSubgroup (F := F) ρ : Set (rationalPoints G)) := by
  let abv := LocalField.residueNormalizedAbsoluteValue F
  have hcont : ∀ (f : rationalPoints G → F), Continuous f → ∀ c : F,
      Continuous fun g => abv (f g - c) := fun f hf c =>
    (Plancherel.continuous_residueNormalizedAbsoluteValue F).comp (hf.sub continuous_const)
  have hent : ∀ a b : n, ∀ᶠ g in nhds (1 : rationalPoints G),
      abv ((ρ.rationalMatrix g : Matrix n n F) a b - (1 : Matrix n n F) a b) < 1 ∧
        abv ((ρ.rationalMatrix g⁻¹ : Matrix n n F) a b - (1 : Matrix n n F) a b) < 1 := by
    intro a b
    have h1 := (hcont _ (ρ.continuous_rationalMatrix_entry a b)
      ((1 : Matrix n n F) a b)).tendsto (1 : rationalPoints G)
    have h2 := (hcont _ ((ρ.continuous_rationalMatrix_entry a b).comp continuous_inv)
      ((1 : Matrix n n F) a b)).tendsto (1 : rationalPoints G)
    simp only [map_one, inv_one, Units.val_one, sub_self, map_zero, Function.comp_apply] at h1 h2
    exact (h1.eventually (gt_mem_nhds zero_lt_one)).and (h2.eventually (gt_mem_nhds zero_lt_one))
  have hall : ∀ᶠ g in nhds (1 : rationalPoints G), ∀ a b : n,
      abv ((ρ.rationalMatrix g : Matrix n n F) a b - (1 : Matrix n n F) a b) < 1 ∧
        abv ((ρ.rationalMatrix g⁻¹ : Matrix n n F) a b - (1 : Matrix n n F) a b) < 1 := by
    simp only [Filter.eventually_all]
    exact hent
  have hc01 : ∀ a b : n, (1 : Matrix n n F) a b = 0 ∨ (1 : Matrix n n F) a b = 1 := by
    intro a b
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hle1 : ∀ x c : F, (c = 0 ∨ c = 1) → abv (x - c) < 1 → abv x ≤ 1 := by
    intro x c hc hx
    have hc' : abv c ≤ 1 := by rcases hc with rfl | rfl <;> simp [abv]
    calc abv x = abv ((x - c) + c) := by rw [sub_add_cancel]
      _ ≤ max (abv (x - c)) (abv c) := LocalField.residueNormalizedAbsoluteValue_add_le_max F _ _
      _ ≤ 1 := max_le hx.le hc'
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  filter_upwards [hall] with g hg
  change MatrixRepresentation.rationalMatrixNorm F ρ g ≤ 1
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  change HarishChandraSchwartz.glNorm (ρ.rationalMatrix g) ≤ 1
  apply HarishChandraSchwartz.glNorm_le
  · intro a b
    exact hle1 _ _ (hc01 a b) (hg a b).1
  · intro a b
    rw [← map_inv]
    exact hle1 _ _ (hc01 a b) (hg a b).2

end Height

section Compactness

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (hρ : IsClosedSubgroup ρ)

omit [LocallyOfFiniteType G.X.hom] in
include hρ in
/-- For a closed matrix representation, every sublevel set `{σ ≤ C}` is compact. -/
theorem isCompact_rationalHeight_le (C : ℝ) :
    IsCompact {g : rationalPoints G | rationalHeight (F := F) ρ g ≤ C} := by
  have hset : {g : rationalPoints G | rationalHeight (F := F) ρ g ≤ C} =
      {g : rationalPoints G | MatrixRepresentation.rationalMatrixNorm F ρ g ≤ Real.exp C} := by
    ext g
    exact Real.log_le_iff_le_exp (rationalMatrixNorm_pos ρ g)
  rw [hset]
  exact MatrixRepresentation.isCompact_rationalMatrixNorm_le F ρ hρ _

omit [LocallyOfFiniteType G.X.hom] in
include hρ in
/-- For a closed matrix representation, `ρ⁻¹(GL_n(𝒪))` is compact. -/
theorem isCompact_rationalHeightSubgroup :
    IsCompact (rationalHeightSubgroup (F := F) ρ : Set (rationalPoints G)) :=
  MatrixRepresentation.isCompact_rationalMatrixNorm_le F ρ hρ 1

/-- `ρ⁻¹(GL_n(𝒪))` as a compact open subgroup of `G(F)`, for a closed matrix representation. -/
def rationalHeightCompactOpen : CompactOpenSubgroup (rationalPoints G) :=
  ⟨⟨rationalHeightSubgroup (F := F) ρ, isOpen_rationalHeightSubgroup ρ⟩,
    isCompact_rationalHeightSubgroup ρ hρ⟩

end Compactness

section Spherical

local instance rationalWeightsSecondCountable : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)

include hKo in
/-- **Waldspurger, Lemma II.1.3**: `∫_K Ξ(g₁ k g₂) dk = Ξ(g₁) Ξ(g₂)`. -/
theorem integral_rationalXi_mul_mul [CompactSpace K] (g₁ g₂ : rationalPoints G) :
    ∫ k : K, rationalXi hKc hPK (g₁ * k * g₂) ∂(normalizedHaar K) =
      rationalXi hKc hPK g₁ * rationalXi hKc hPK g₂ :=
  integral_xi_mul_mul (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp) hKo g₁ g₂

end Spherical

section Schwartz

local instance rationalWeightsT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G
local instance rationalWeightsTotallyDisconnected :
    TotallyDisconnectedSpace (rationalPoints G) :=
  rationalPoint_totallyDisconnectedSpace_of_localField F G.X

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n)

/-- **Waldspurger's Harish-Chandra Schwartz space `C(G)`** (III.6) on the actual rational points:
the Library's generic space for the weights `Ξ = rationalXi hKc hPK` and
`σ = rationalHeight ρ`, with its locally convex inductive-limit topology. -/
abbrev RationalSchwartzSpace :=
  Space (rationalXi hKc hPK) (rationalHeight (F := F) ρ)

/-- The inclusion `C_c^∞(G(F)) → C(G)` (Waldspurger III.6). -/
def rationalSchwartzOfTestFunction :
    HarmonicAnalysis.SchwartzBruhat (rationalPoints G) →ₗ[ℂ] RationalSchwartzSpace hKc hPK ρ :=
  ofSchwartzBruhat (continuous_rationalXi hKo hKc hPK) (rationalXi_pos hKo hKc hPK)
    (continuous_rationalHeight ρ) (rationalHeight_nonneg ρ)

theorem rationalSchwartzOfTestFunction_injective :
    Function.Injective (rationalSchwartzOfTestFunction hKo hKc hPK ρ) :=
  ofSchwartzBruhat_injective _ _ _ _

/-- **`C_c^∞(G(F))` is dense in `C(G)`** (Waldspurger III.6), for a closed matrix
representation. -/
theorem denseRange_rationalSchwartzOfTestFunction {N : ℕ} [Nonempty (Fin N)]
    (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ) :
    DenseRange (rationalSchwartzOfTestFunction hKo hKc hPK ρ) :=
  denseRange_ofSchwartzBruhat _ _ _ _ (rationalHeightCompactOpen ρ hρ)
    (fun _ hk₁ _ hk₂ g => rationalHeight_mul_mul ρ hk₁ hk₂ g) (isCompact_rationalHeight_le ρ hρ)

end Schwartz

end Rational

end Langlands.HarishChandraSchwartz
