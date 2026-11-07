import Langlands.Global.AdelicRepresentationHeightExhaustion
import Langlands.Global.AdelicRestrictionSplitCentre

/-! # Compact exhaustions of actual adelic quotients by height images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Topology
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global

namespace LeftCosetSpace

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (Γ : Subgroup H)

/-- Images of an ambient compact exhaustion under the original open left quotient map. -/
def compactExhaustionImage (K : CompactExhaustion H) :
    CompactExhaustion (LeftCosetSpace Γ) where
  toFun n := mk Γ '' K n
  isCompact' n := (K.isCompact n).image (continuous_mk Γ)
  subset_interior_succ' n :=
    (Set.image_mono (K.subset_interior_succ n)).trans
      ((isOpenQuotientMap_mk Γ).isOpenMap.image_interior_subset (K (n + 1)))
  iUnion_eq' := Set.iUnion_eq_univ_iff.mpr fun q => by
    obtain ⟨x, rfl⟩ := mk_surjective Γ q
    obtain ⟨n, hn⟩ := K.exists_mem x
    exact ⟨n, x, hn, rfl⟩

@[simp]
theorem compactExhaustionImage_apply (K : CompactExhaustion H) (n : ℕ) :
    compactExhaustionImage Γ K n = mk Γ '' K n := rfl

end LeftCosetSpace

namespace RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  {N : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin N))
  (Γ : Subgroup (AdelicGroupPoints F G))

/-- An image of the full adelic height sublevel in the existing left homogeneous quotient. -/
def adelicQuotientHeightSublevel (B : ℝ) : Set (LeftCosetSpace Γ) :=
  LeftCosetSpace.mk Γ '' adelicHeightSublevel F G rho B

@[simp]
theorem mem_adelicQuotientHeightSublevel (B : ℝ) (q : LeftCosetSpace Γ) :
    q ∈ adelicQuotientHeightSublevel F G rho Γ B ↔
      ∃ g : AdelicGroupPoints F G,
        adelicHeight F G rho g ≤ B ∧ LeftCosetSpace.mk Γ g = q := Iff.rfl

/-- Membership means that some actual left translate of the representative has bounded height. -/
theorem mk_mem_adelicQuotientHeightSublevel (B : ℝ) (g : AdelicGroupPoints F G) :
    LeftCosetSpace.mk Γ g ∈ adelicQuotientHeightSublevel F G rho Γ B ↔
      ∃ γ : Γ, adelicHeight F G rho (γ.val * g) ≤ B := by
  constructor
  · rintro ⟨x, hx, he⟩
    have hγ : x * g⁻¹ ∈ Γ := (LeftCosetSpace.mk_eq_mk_iff Γ g x).mp he.symm
    refine ⟨⟨x * g⁻¹, hγ⟩, ?_⟩
    change adelicHeight F G rho x ≤ B at hx
    simpa only [inv_mul_cancel_right] using hx
  · rintro ⟨γ, hγ⟩
    exact ⟨γ.val * g, hγ, LeftCosetSpace.mk_subgroup_mul Γ γ g⟩

theorem adelicQuotientHeightSublevel_mono {B C : ℝ} (h : B ≤ C) :
    adelicQuotientHeightSublevel F G rho Γ B ⊆
      adelicQuotientHeightSublevel F G rho Γ C :=
  Set.image_mono (adelicHeightSublevel_mono F G rho h)

/-- Positive right translation has the same submultiplicative height control as representatives. -/
theorem rightTranslate_adelicQuotientHeightSublevel_subset (hN : 0 < N) {B C : ℝ}
    {g : AdelicGroupPoints F G} (hg : g ∈ adelicHeightSublevel F G rho C) :
    LeftCosetSpace.rightTranslate Γ g '' adelicQuotientHeightSublevel F G rho Γ B ⊆
      adelicQuotientHeightSublevel F G rho Γ (B * C) := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨x * g, mul_mem_adelicHeightSublevel F G rho hN hx hg, rfl⟩

variable [IsAffine G.X.left]

theorem isCompact_adelicQuotientHeightSublevel (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho) (B : ℝ) :
    IsCompact (adelicQuotientHeightSublevel F G rho Γ B) :=
  (isCompact_adelicHeightSublevel F G rho hN hrho B).image
    (LeftCosetSpace.continuous_mk Γ)

/-- The exact images of natural height sublevels exhaust the original quotient topology. -/
def adelicQuotientHeightCompactExhaustion (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho) : CompactExhaustion (LeftCosetSpace Γ) :=
  LeftCosetSpace.compactExhaustionImage Γ (adelicHeightCompactExhaustion F G rho hN hrho)

@[simp]
theorem adelicQuotientHeightCompactExhaustion_apply (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho) (n : ℕ) :
    adelicQuotientHeightCompactExhaustion F G rho Γ hN hrho n =
      adelicQuotientHeightSublevel F G rho Γ n := rfl

@[simp]
theorem mem_adelicQuotientHeightCompactExhaustion (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho) (n : ℕ) (q : LeftCosetSpace Γ) :
    q ∈ adelicQuotientHeightCompactExhaustion F G rho Γ hN hrho n ↔
      ∃ g : AdelicGroupPoints F G,
        adelicHeight F G rho g ≤ n ∧ LeftCosetSpace.mk Γ g = q := Iff.rfl

/-- Every compact quotient set admits representatives in some common ambient height level. -/
theorem exists_adelicQuotientHeightCompactExhaustion_superset (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho)
    {K : Set (LeftCosetSpace Γ)} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ adelicQuotientHeightCompactExhaustion F G rho Γ hN hrho n :=
  (adelicQuotientHeightCompactExhaustion F G rho Γ hN hrho).exists_superset_of_isCompact hK

/-- Image exhaustions for any two positive-rank closed matrix embeddings are cofinal. -/
theorem adelicQuotientHeightCompactExhaustion_cofinal (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho)
    {M : ℕ} (sigma : GroupScheme.MatrixRepresentation G (Fin M))
    (hM : 0 < M) (hsigma : GroupScheme.IsClosedSubgroup sigma) (n : ℕ) :
    ∃ m : ℕ, adelicQuotientHeightCompactExhaustion F G rho Γ hN hrho n ⊆
      adelicQuotientHeightCompactExhaustion F G sigma Γ hM hsigma m := by
  obtain ⟨m, hm⟩ := adelicHeightCompactExhaustion_cofinal F G rho hN hrho sigma hM hsigma n
  exact ⟨m, Set.image_mono hm⟩

/-- A compact family of positive right translations has a common multiplicative level bound. -/
theorem exists_compact_rightTranslate_adelicQuotientHeightCompactExhaustion_bound
    (hN : 0 < N) (hrho : GroupScheme.IsClosedSubgroup rho)
    {K : Set (AdelicGroupPoints F G)} (hK : IsCompact K) :
    ∃ m : ℕ, ∀ g ∈ K, ∀ n : ℕ,
      LeftCosetSpace.rightTranslate Γ g ''
          adelicQuotientHeightCompactExhaustion F G rho Γ hN hrho n ⊆
        adelicQuotientHeightCompactExhaustion F G rho Γ hN hrho (n * m) := by
  obtain ⟨m, hm⟩ := exists_nat_adelicHeight_bound_of_isCompact F G rho hN hK
  refine ⟨m, fun g hg n => ?_⟩
  simpa only [adelicQuotientHeightCompactExhaustion_apply, Nat.cast_mul] using
    rightTranslate_adelicQuotientHeightSublevel_subset F G rho Γ hN (B := (n : ℝ)) (hm hg)

/-- The existing actual rational quotient, with its original left quotient topology. -/
abbrev rationalQuotientHeightCompactExhaustion (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho) :
    CompactExhaustion (AdelicGroupPoints.RationalQuotient F G) :=
  adelicQuotientHeightCompactExhaustion F G rho
    (AdelicGroupPoints.rationalSubgroup F G) hN hrho

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)

/-- The existing actual positive-central rational quotient, with no choice of representatives. -/
abbrev positiveRationalQuotientHeightCompactExhaustion (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho) :
    CompactExhaustion (PositiveRealTorus.PositiveRationalQuotient F G T i) :=
  adelicQuotientHeightCompactExhaustion F G rho
    (PositiveRealTorus.positiveRationalSubgroup F G T i) hN hrho

end RepresentationGrowth

namespace RestrictionSplitCentre

variable (F : Type) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
  (j : S.toGrp ⟶ Langlands.GroupScheme.AffineWeil.groupScheme ℚ F G)
  {N : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin N))

/-- Exact ambient height images on the existing restriction split-centre quotient. -/
abbrev quotientHeightCompactExhaustion (hN : 0 < N)
    (hrho : GroupScheme.IsClosedSubgroup rho) :
    CompactExhaustion (Quotient F G S j) :=
  RepresentationGrowth.adelicQuotientHeightCompactExhaustion F G rho
    (rationalSubgroup F G S j) hN hrho

end RestrictionSplitCentre

end Langlands.Global
