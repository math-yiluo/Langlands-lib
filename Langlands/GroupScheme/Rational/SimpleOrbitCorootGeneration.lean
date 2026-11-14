import Langlands.GroupScheme.Rational.A2OrbitUnits
import Langlands.GroupScheme.Rational.OrthogonalOrbitDescent
import Langlands.GroupScheme.Rational.QuasiSplitPinningOrbitPairs
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence

/-! # Coroot products of Galois-equivariant unit families lie in `G(k)^+` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.GaloisPointComparison Langlands.Geometry.Building
open Langlands.LinearAlgebra.RootDatumOrbitPairs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

private theorem perm_inv_apply_self {α : Type*} (e : Equiv.Perm α) (x : α) : e⁻¹ (e x) = x :=
  e.symm_apply_apply x

private theorem perm_apply_inv_self {α : Type*} (e : Equiv.Perm α) (x : α) : e (e⁻¹ x) = x :=
  e.apply_symm_apply x

namespace Langlands.GroupScheme

namespace SplitPinning

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance simpleOrbitCorootAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (x : p.NormalizedSimpleRootParametrizations)
    (O : Set p.base.support) (hO : ∀ a ∈ O, ∀ b ∈ O, a ≠ b → p.rootDatum.IsOrthogonal a b)
    [Fintype O]

/-- The orbit coroot product of a unit family equal to `1` off `O` is the image of its
simple-coroot product in the pinned torus. -/
theorem orbitCoroot_eq_map_simpleCorootProduct {u : p.base.support → Kˣ}
    (hu : ∀ b, b ∉ O → u b = 1) :
    orbitCoroot k K p x O hO u =
      rationalPoints.map p.inclusion (p.simpleCorootProduct u) := by
  classical
  have h1 : orbitCoroot k K p x O hO u =
      rationalPoints.map p.inclusion (∏ b : O, p.simpleCorootPoint b (u b)) := by
    rw [← Finset.noncommProd_eq_prod, Finset.map_noncommProd, orbitCoroot,
      Langlands.Algebra.RankOneRelation.prodHom, Subgroup.noncommPiCoprod_apply]
    rfl
  rw [h1, simpleCorootProduct]
  congr 1
  rw [← Finset.prod_filter_of_ne (p := fun b => b ∈ O) (s := Finset.univ)
    (fun b _ hb => by
      by_contra h
      exact hb (by rw [hu b h, map_one]))]
  exact (Finset.prod_subtype (Finset.univ.filter fun b => b ∈ O) (p := fun b => b ∈ O)
    (fun b => by simp) (fun b => p.simpleCorootPoint b (u b))).symm

end SplitPinning

namespace GaloisCompatiblePinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : GaloisCompatiblePinningData k K G)

local instance simpleOrbitCorootGenerationAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- The Galois orbit of a simple root. -/
def simpleOrbit (b : D.pinning.base.support) : Set D.pinning.base.support :=
  {x | ∃ σ : K ≃ₐ[k] K, D.action σ b = x}

theorem action_mem_simpleOrbit_iff (b : D.pinning.base.support) (σ : K ≃ₐ[k] K)
    (x : D.pinning.base.support) : D.action σ x ∈ D.simpleOrbit b ↔ x ∈ D.simpleOrbit b := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨σ⁻¹ * τ, ?_⟩
    rw [map_mul, Equiv.Perm.mul_apply, hτ, map_inv, perm_inv_apply_self]
  · rintro ⟨τ, rfl⟩
    exact ⟨σ * τ, by rw [map_mul, Equiv.Perm.mul_apply]⟩

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} (t : S ⟶ D.torus)
  [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffineHom D.torus.toGrp.X.hom]
  [LocallyOfFiniteType D.torus.toGrp.X.hom] [FiniteDimensional k K] [IsGalois k K]
  (hG : IsConnectedReductive G)
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj D.torus).toGrp)
  (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom t ≫ D.inclusion))
  (hjc : IsClosedSubgroup D.inclusion)
  (hcent : (torusCentralizer (CommGroupScheme.groupHom t ≫ D.inclusion)).IsRepresentedBy
      D.inclusion)
  (hspan : D.pinning.rootDatum.corootSpan ℤ = ⊤)
  (hρ : IsPairingCompatible D.pinning.base D.action)

include hG hT hf hcent hρ in
/-- **Orthogonal orbits.** If the Galois orbit of `b` is pairwise orthogonal, every orbit
family at `b` has coroot product in the image of `G(k)^+`. -/
theorem simpleCorootProduct_mem_of_isOrthogonal {b : D.pinning.base.support}
    (horth : ∀ σ : K ≃ₐ[k] K, D.action σ b ≠ b →
      D.pinning.rootDatum.IsOrthogonal (b : D.pinning.rootIndex) (D.action σ b))
    {c : D.pinning.base.support → Kˣ} (hc : D.IsOrbitFamily b c) :
    rationalPoints.map D.pinning.inclusion (D.pinning.simpleCorootProduct c) ∈
      relativeRootGeneratedExtension k K (CommGroupScheme.groupHom t ≫ D.inclusion) := by
  classical
  have hS : IsSplitTorus S.toGrp := hf.1.1
  have hO : ∀ x ∈ D.simpleOrbit b, ∀ y ∈ D.simpleOrbit b, x ≠ y →
      D.pinning.rootDatum.IsOrthogonal (x : D.pinning.rootIndex) y := by
    rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩ hne
    have e : D.action τ b = D.action σ (D.action (σ⁻¹ * τ) b) := by
      rw [map_mul, Equiv.Perm.mul_apply, map_inv, perm_apply_inv_self]
    have h1 : D.action (σ⁻¹ * τ) b ≠ b := fun h => hne (by rw [e, h])
    have h2 := horth _ h1
    rw [e]
    exact ⟨by rw [hρ.pairing_apply]; exact h2.1, by rw [hρ.pairing_apply]; exact h2.2⟩
  have hOs : ∀ (σ : K ≃ₐ[k] K) x, x ∈ D.simpleOrbit b ↔ D.action σ x ∈ D.simpleOrbit b :=
    fun σ x => (D.action_mem_simpleOrbit_iff b σ x).symm
  obtain ⟨a, ha, hab⟩ := D.exists_relativeRoot_restrict t hS hT hcent b
  have hres : ∀ x ∈ D.simpleOrbit b, D.restrictMap t ≫ D.pinning.rootDatum.root x =
      characterLattice.baseChange (algebraBaseMap k K) S a := by
    rintro _ ⟨σ, rfl⟩
    exact (D.restrictMap_comp_root_action t hS σ b).trans hab
  have ha0 : a ≠ 0 := ha.1
  have ha' := relativeRootNegation k G hG S _ hf a ha
  have : Fintype (D.simpleOrbit b) := Fintype.ofFinite _
  have hmem := SplitPinning.orbitCoroot_mem_map_relativeRootGeneratedSubgroup k K
    (CommGroupScheme.groupHom t ≫ D.inclusion) D.pinning D.rootMaps (D.simpleOrbit b) hO
    (D.restrictMap t) (D.groupHom_restrictMap_comp_inclusion t) a hres D.inclusion D.torusIso
    D.inclusion_eq D.rootMaps_compatible D.action_root hOs hS ha0 ha ha' (u := c) hc.1
  rwa [SplitPinning.orbitCoroot_eq_map_simpleCorootProduct k K D.pinning D.rootMaps
    (D.simpleOrbit b) hO (fun x hx => hc.2 x (fun σ h => hx ⟨σ, h⟩))] at hmem

include hG hT hf hjc hcent hspan hρ in
/-- **`A₂` orbits.** If the Galois orbit of `b` contains a simple root non-orthogonal to `b`,
every orbit family at `b` has coroot product in the image of `G(k)^+`, given noncommutation
of the root groups of Galois-conjugate adjacent simple roots at `1`. -/
theorem simpleCorootProduct_mem_of_not_isOrthogonal
    (hnc : ∀ x y : D.pinning.base.support, x ≠ y →
      D.pinning.rootDatum.pairing (x : D.pinning.rootIndex) y = -1 →
      D.pinning.rootDatum.pairing (y : D.pinning.rootIndex) x = -1 →
      (∃ σ : K ≃ₐ[k] K, D.action σ x = y) →
      ¬ Commute (D.simplePoint x 1) (D.simplePoint y 1))
    {b : D.pinning.base.support} {σ₀ : K ≃ₐ[k] K} (hσ₀ : D.action σ₀ b ≠ b)
    (hno : ¬ D.pinning.rootDatum.IsOrthogonal (b : D.pinning.rootIndex) (D.action σ₀ b))
    {c : D.pinning.base.support → Kˣ} (hc : D.IsOrbitFamily b c) :
    rationalPoints.map D.pinning.inclusion (D.pinning.simpleCorootProduct c) ∈
      relativeRootGeneratedExtension k K (CommGroupScheme.groupHom t ≫ D.inclusion) := by
  classical
  have hS : IsSplitTorus S.toGrp := hf.1.1
  have hic : IsClosedSubgroup (CommGroupScheme.groupHom t ≫ D.inclusion) := hf.1.2
  have : Mono (CommGroupScheme.groupHom t ≫ D.inclusion).hom.hom.left :=
    hf.isSplitSubtorus.mono
  have hE : RelativeRoot.HasOppositeFactorPairs (CommGroupScheme.groupHom t ≫ D.inclusion) :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs _ hS).mp
      (rootRankOneFactorization k G hG S _ hf)
  obtain ⟨m₀, hm₀⟩ := exists_root_eq_add_of_not_isOrthogonal hρ b hσ₀ hno
  obtain ⟨a, ha, hp₀⟩ := D.exists_relativeRoot_restrict t hS hT hcent b
  have hq₀ := (D.restrictMap_comp_root_action t hS σ₀ b).trans hp₀
  have hna := relativeRootNegation k G hG S _ hf a ha
  have hline := D.restrictsToMultipliableLine t hS hT hcent hE a
  have hpq : b ≠ D.action σ₀ b := Ne.symm hσ₀
  obtain ⟨M, hM, -, hMx, -, -⟩ := D.exists_mergedPieces t hm₀ hS hp₀ hq₀ hpq hline
  set g := D.pairElement (D.basePair m₀) with hg
  have hA : D.pairA b (D.basePair m₀) = D.action g b := rfl
  have hB : D.pairB (D.action σ₀ b) (D.basePair m₀) = D.action g (D.action σ₀ b) := rfl
  obtain ⟨hAB, hAB1, hAB2⟩ := D.pair_pairings t hm₀ hS hp₀ hq₀ hpq hline (D.basePair m₀)
  have hnc' := hnc _ _ hAB hAB1 hAB2 ⟨g * σ₀ * g⁻¹, by
    rw [hA, hB, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, map_inv,
      perm_inv_apply_self]⟩
  have hc' : D.IsOrbitFamily (D.pairA b (D.basePair m₀)) c := by
    refine ⟨hc.1, fun x hx => hc.2 x fun σ h => hx (σ * g⁻¹) ?_⟩
    rw [hA, map_mul, Equiv.Perm.mul_apply, map_inv, perm_inv_apply_self, h]
  exact D.simpleCorootProduct_mem_of_a2 t hm₀ hS hp₀ hq₀ hpq hline M
    (fun c => ⟨(hM c).1, (hM c).2.1⟩) hMx hT hf hjc hcent hic hspan hE ha hna rfl hnc' hc'

include hG hT hf hjc hcent hspan hρ in
/-- Every orbit family has coroot product in the image of `G(k)^+`. -/
theorem simpleCorootProduct_mem_of_isOrbitFamily
    (hnc : ∀ x y : D.pinning.base.support, x ≠ y →
      D.pinning.rootDatum.pairing (x : D.pinning.rootIndex) y = -1 →
      D.pinning.rootDatum.pairing (y : D.pinning.rootIndex) x = -1 →
      (∃ σ : K ≃ₐ[k] K, D.action σ x = y) →
      ¬ Commute (D.simplePoint x 1) (D.simplePoint y 1))
    {b : D.pinning.base.support} {c : D.pinning.base.support → Kˣ}
    (hc : D.IsOrbitFamily b c) :
    rationalPoints.map D.pinning.inclusion (D.pinning.simpleCorootProduct c) ∈
      relativeRootGeneratedExtension k K (CommGroupScheme.groupHom t ≫ D.inclusion) := by
  by_cases h : ∀ σ : K ≃ₐ[k] K, D.action σ b ≠ b →
      D.pinning.rootDatum.IsOrthogonal (b : D.pinning.rootIndex) (D.action σ b)
  · exact D.simpleCorootProduct_mem_of_isOrthogonal t hG hT hf hcent hρ h hc
  · push Not at h
    obtain ⟨σ₀, hσ₀, hno⟩ := h
    exact D.simpleCorootProduct_mem_of_not_isOrthogonal t hG hT hf hjc hcent hspan hρ hnc
      hσ₀ hno hc

include hG hT hf hjc hcent hspan hρ in
/-- **Equivariant unit families.** For every Galois-equivariant unit family `c` on the simple
roots, the image of `∏_b b^∨(c b)` lies in the image of `G(k)^+`. -/
theorem simpleCorootProduct_mem_of_equivariant
    (hnc : ∀ x y : D.pinning.base.support, x ≠ y →
      D.pinning.rootDatum.pairing (x : D.pinning.rootIndex) y = -1 →
      D.pinning.rootDatum.pairing (y : D.pinning.rootIndex) x = -1 →
      (∃ σ : K ≃ₐ[k] K, D.action σ x = y) →
      ¬ Commute (D.simplePoint x 1) (D.simplePoint y 1))
    {c : D.pinning.base.support → Kˣ}
    (hc : ∀ (σ : K ≃ₐ[k] K) (b : D.pinning.base.support), (c (D.action σ b) : K) = σ (c b)) :
    rationalPoints.map D.pinning.inclusion (D.pinning.simpleCorootProduct c) ∈
      relativeRootGeneratedExtension k K (CommGroupScheme.groupHom t ≫ D.inclusion) := by
  classical
  suffices H : ∀ n : ℕ, ∀ c : D.pinning.base.support → Kˣ,
      (∀ (σ : K ≃ₐ[k] K) (b : D.pinning.base.support), (c (D.action σ b) : K) = σ (c b)) →
      (Finset.univ.filter fun x => c x ≠ 1).card ≤ n →
      rationalPoints.map D.pinning.inclusion (D.pinning.simpleCorootProduct c) ∈
        relativeRootGeneratedExtension k K (CommGroupScheme.groupHom t ≫ D.inclusion) from
    H _ c hc le_rfl
  intro n
  induction n with
  | zero =>
    intro c _ hcard
    have h1 : c = 1 := by
      funext x
      by_contra hx
      have hmem : x ∈ Finset.univ.filter fun x => c x ≠ 1 := by simpa using hx
      have := Finset.card_pos.mpr ⟨x, hmem⟩
      omega
    rw [h1, D.simpleCorootProduct_one, map_one]
    exact Subgroup.one_mem _
  | succ n ih =>
    intro c hc hcard
    by_cases h1 : ∀ x, c x = 1
    · rw [show c = 1 from funext h1, D.simpleCorootProduct_one, map_one]
      exact Subgroup.one_mem _
    · push Not at h1
      obtain ⟨b, hb⟩ := h1
      set O := D.simpleOrbit b with hO
      let c₁ : D.pinning.base.support → Kˣ := fun x => if x ∈ O then c x else 1
      let c₂ : D.pinning.base.support → Kˣ := fun x => if x ∈ O then 1 else c x
      have hc12 : c = c₁ * c₂ := funext fun x => by
        by_cases hx : x ∈ O <;> simp [c₁, c₂, hx]
      have hbO : b ∈ O := ⟨1, by rw [map_one, Equiv.Perm.one_apply]⟩
      have hc₁ : D.IsOrbitFamily b c₁ := by
        refine ⟨fun σ x => ?_, fun x hx => ?_⟩
        · by_cases hx : x ∈ O
          · have hx' : D.action σ x ∈ O := (D.action_mem_simpleOrbit_iff b σ x).mpr hx
            simp only [c₁, hx, hx', ↓reduceIte]
            exact hc σ x
          · have hx' : D.action σ x ∉ O := fun h => hx ((D.action_mem_simpleOrbit_iff b σ x).mp h)
            simp [c₁, hx, hx']
        · have hxO : x ∉ O := fun ⟨σ, h⟩ => hx σ h
          simp [c₁, hxO]
      have hc₂ : ∀ (σ : K ≃ₐ[k] K) (x : D.pinning.base.support),
          (c₂ (D.action σ x) : K) = σ (c₂ x) := by
        intro σ x
        by_cases hx : x ∈ O
        · have hx' : D.action σ x ∈ O := (D.action_mem_simpleOrbit_iff b σ x).mpr hx
          simp [c₂, hx, hx']
        · have hx' : D.action σ x ∉ O := fun h => hx ((D.action_mem_simpleOrbit_iff b σ x).mp h)
          simp only [c₂, hx, hx', ↓reduceIte]
          exact hc σ x
      have hcard₂ : (Finset.univ.filter fun x => c₂ x ≠ 1).card ≤ n := by
        have hsub : (Finset.univ.filter fun x => c₂ x ≠ 1) ⊆
            (Finset.univ.filter fun x => c x ≠ 1).erase b := by
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          by_cases hxO : x ∈ O
          · simp [c₂, hxO] at hx
          · simp only [c₂, hxO, ↓reduceIte] at hx
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun h => hxO (h ▸ hbO), hx⟩
        have h := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (by simpa using hb)] at h
        omega
      rw [hc12, D.simpleCorootProduct_mul, map_mul]
      exact Subgroup.mul_mem _
        (D.simpleCorootProduct_mem_of_isOrbitFamily t hG hT hf hjc hcent hspan hρ hnc hc₁)
        (ih c₂ hc₂ hcard₂)

end GaloisCompatiblePinningData

end Langlands.GroupScheme
