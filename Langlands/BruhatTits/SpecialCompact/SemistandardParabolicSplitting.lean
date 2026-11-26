import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.GroupScheme.Rational.DominantChamberMove
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.Representation.Aubert.General.RationalOppositeIwahoriBasisProof

/-! # Compact factorization along every semistandard dynamic parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] {i : S.toGrp ⟶ G}

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of k)))

omit [IsAffineHom G.X.hom] in
/-- Normalizing points with the same relative Weyl class act identically on cocharacters. -/
theorem cocharacterAut_normalizingAut_eq_of_mk_eq [Mono i.hom.hom.left]
    {n n' : normalizerPoints i}
    (h : (QuotientGroup.mk n' : relativeWeylGroup i) = QuotientGroup.mk n)
    (ξ : cocharacterLattice S) :
    cocharacterAut (normalizingAut i n') ξ = cocharacterAut (normalizingAut i n) ξ := by
  have hc : n'⁻¹ * n ∈ (centralizerPoints i).subgroupOf (normalizerPoints i) :=
    QuotientGroup.eq.mp h
  have hrefl : normalizingAut i (n'⁻¹ * n) = Iso.refl S :=
    (isNormalizingPoint_normalizingAut i (n'⁻¹ * n)).unique i (Subgroup.mem_subgroupOf.mp hc)
  have e : n = n' * (n'⁻¹ * n) := by group
  conv_rhs => rw [e]
  rw [normalizingAut_mul, hrefl, Iso.refl_trans]

/-- **Compact splitting along semistandard parabolics.** If every relative Weyl class has a
representative in `K` and `K` factors along every standard parabolic for a generic `ν`,
then `K` factors along the dynamic parabolic of every cocharacter `ξ` of the maximal split
torus: `m u ∈ K` exactly when `m ∈ K` and `u ∈ K`, for `m` in the actual Levi points and
`u` in the actual radical points of `ξ`. -/
theorem mul_mem_iff_of_weylRepresentatives (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {K : Subgroup (rationalPoints G)} (hW : HasWeylRepresentatives i K)
    (hP : HasParabolicFactorization i ν K) (ξ : cocharacterLattice S)
    {m u : rationalPoints G}
    (hm : m ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ξ ≫ i)).carrier X₀)
    (hu : u ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ξ ≫ i)).carrier X₀) :
    m * u ∈ K ↔ m ∈ K ∧ u ∈ K := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsSeparated G.X.hom := hG.isSeparated
  obtain ⟨n, hn⟩ := (relativeRootSystem k G hG S i hi).exists_normalizerPoint_dominant i
    hi.isSplitSubtorus.1 ν ξ
  obtain ⟨n', hn'K, hn'w⟩ := hW (QuotientGroup.mk n)
  set ξ' := cocharacterAut (normalizingAut i n') ξ with hξ'
  have hdom : ∀ α ∈ positiveRelativeRoots i ν, 0 ≤ latticePairing S α ξ' := by
    rw [hξ', cocharacterAut_normalizingAut_eq_of_mk_eq hn'w ξ]
    exact hn
  set J : Set (characterLattice S) :=
    {α | α ∈ simpleRelativeRoots i ν ∧ latticePairing S α ξ' = 0}
  have hJ : J ⊆ simpleRelativeRoots i ν := fun α h => h.1
  have hstd : IsStandardCocharacter i ν J ξ' := ⟨hJ, fun α h => h.2, fun α hα hαJ =>
    lt_of_le_of_ne (hdom α (simpleRelativeRoots_subset_positive i ν hα))
      (fun h0 => hαJ ⟨hα, h0.symm⟩)⟩
  obtain ⟨hPJ, hMJ, hUJ⟩ := (standardCocharacter k G hG S i hi ν hν J hJ).2 ξ' hstd
  have hcomp := groupHom_cocharacterAut_comp i n' ξ
  set g : rationalPoints G := (n' : rationalPoints G)
  have hm' : g * m * g⁻¹ ∈ standardLeviPoints i ν J := by
    have h := (Dynamic.mem_centralizer_conj (CommGroupScheme.groupHom ξ ≫ i) g).mp hm
    rw [G.constantPoint_self, ← hcomp] at h
    change g * m * g⁻¹ ∈ (standardLevi i ν J).carrier X₀
    rw [hMJ]
    exact h
  have hu' : g * u * g⁻¹ ∈ standardUnipotentPoints i ν J := by
    have h := (Dynamic.mem_unipotent_conj (CommGroupScheme.groupHom ξ ≫ i) g).mp hu
    rw [G.constantPoint_self, ← hcomp] at h
    change g * u * g⁻¹ ∈ (standardUnipotent i ν J).carrier X₀
    rw [hUJ]
    exact h
  constructor
  · intro hmu
    have hx : g * m * g⁻¹ * (g * u * g⁻¹) ∈
        ((K ⊓ standardParabolicPoints i ν J : Subgroup (rationalPoints G)) :
          Set (rationalPoints G)) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have : g * m * g⁻¹ * (g * u * g⁻¹) = g * (m * u) * g⁻¹ := by group
        rw [this]
        exact K.mul_mem (K.mul_mem hn'K hmu) (K.inv_mem hn'K)
      · exact Subgroup.mul_mem _ (standardLevi_le_standardParabolic i ν J X₀ hm')
          (standardUnipotent_le_standardParabolic i ν J X₀ hu')
    rw [hP J hJ] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx
    have haM : a ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ξ' ≫ i)).carrier X₀ := by
      rw [← hMJ]; exact (Subgroup.mem_inf.mp ha).2
    have hbU : b ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ξ' ≫ i)).carrier X₀ := by
      rw [← hUJ]; exact (Subgroup.mem_inf.mp hb).2
    have hm'' : g * m * g⁻¹ ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ξ' ≫ i)).carrier X₀ := by
      rw [← hMJ]; exact hm'
    have hu'' : g * u * g⁻¹ ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ξ' ≫ i)).carrier X₀ := by
      rw [← hUJ]; exact hu'
    obtain ⟨-, hma, -⟩ := Aubert.General.RationalPointFamily.dynamic_opposite_factorization_unique
      (CommGroupScheme.groupHom ξ' ≫ i) 1 (one_mem _) a haM b hbU 1 (one_mem _) _ hm'' _ hu''
      (by rw [one_mul, one_mul, hab])
    have hmK' : g * m * g⁻¹ ∈ K := hma ▸ (Subgroup.mem_inf.mp ha).1
    have hmK : m ∈ K := by
      have : m = g⁻¹ * (g * m * g⁻¹) * g := by group
      rw [this]
      exact K.mul_mem (K.mul_mem (K.inv_mem hn'K) hmK') hn'K
    refine ⟨hmK, ?_⟩
    have : u = m⁻¹ * (m * u) := by group
    rw [this]
    exact K.mul_mem (K.inv_mem hmK) hmu
  · rintro ⟨hm, hu⟩
    exact K.mul_mem hm hu

end Langlands.BruhatTits.SpecialCompact
