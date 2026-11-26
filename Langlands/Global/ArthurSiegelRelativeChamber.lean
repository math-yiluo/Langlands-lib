import Langlands.Global.AdelicLocalFinitenessChamberCoordinates
import Langlands.Global.AdelicChamberFromRankOneHeight
import Langlands.Global.AdelicRankOneOrbitHeightBoundProof
import Langlands.Global.AdelicSiegelSetupExistenceProof
import Langlands.Global.AdelicIwasawaHeight

/-! # Relative chamber reduction on all of `G(𝔸_F)` for every compact Iwasawa subgroup

For a connected reductive group `G` over a number field with an actual algebraic Siegel setup,
a compact subgroup `K` with `P_0(𝔸_F) K = G(𝔸_F)` and a standard parabolic subgroup `P_1`
(`Δ_0^{P_1} = S₁`), `exists_relativeChamberReduction` translates every point of `G(𝔸_F)` by a
rational point of `P_1` into the products `n m a k` with `n ∈ N_0(𝔸_F)`, `m ∈ M_0(𝔸_F)¹`, `a` a
positive point of the maximal split torus `T` with `t ≤ |α(a)|` for every `α ∈ S₁`, and `k ∈ K`.
See the paired Markdown file for the proof. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise Matrix

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

section Factors

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- **Iwasawa factors with the full torus.** For an actual setup and every compact subgroup
`K` with `P_0(𝔸_F) K = G(𝔸_F)`, every point of `G(𝔸_F)` (not only of the norm-one group) is
`n m a k` with `n ∈ N_0(𝔸_F)`, `m ∈ M_0(𝔸_F)¹`, `a` an intrinsic positive point of the
maximal split torus `T` itself and `k ∈ K`. -/
theorem exists_torus_iwasawa_factors (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K) (g : AdelicGroupPoints F G) :
    ∃ (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
      (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
      (a : PositiveRealTorus.intrinsicSubgroup F T),
      ∃ k ∈ K, map F _ G (Standard.unipotentHom i ν ∅) n *
        map F _ G (Standard.leviHom i ν ∅) m *
        map F T.toGrp G i (a : AdelicGroupPoints F T.toGrp) * k = g := by
  classical
  have hSetup := hS
  obtain ⟨hTmax, -, -, hRL, -, hlevi, -⟩ := hSetup
  obtain ⟨q, k, hk, hqk⟩ := hK.exists_eq g
  set p := map F _ G (Standard.parabolicHom i ν ∅) q with hpdef
  have hp : p ∈ standardParabolicImage F G T i ν := ⟨q, rfl⟩
  obtain ⟨f, -, hfM, hfid, hfker⟩ := exists_standardLeviPart F G T i ν T₀ j hS
  let pp : standardParabolicImage F G T i ν := ⟨p, hp⟩
  have hfpP : f pp ∈ standardParabolicImage F G T i ν :=
    standardLeviImage_le_parabolic F G T i ν (hfM pp)
  have hu : p * (f pp)⁻¹ ∈ standardUnipotentImage F G T i ν := by
    have h := (hfker (pp * (⟨f pp, hfpP⟩ : standardParabolicImage F G T i ν)⁻¹)).mp (by
      rw [map_mul, map_inv, hfid _ (hfM pp), mul_inv_cancel])
    exact h
  obtain ⟨n, hn⟩ := hu
  obtain ⟨mM, hmM⟩ := hfM pp
  have hMc := Standard.isClosedSubgroup_leviHom i ν ∅
  have : IsAffineHom (Standard.leviScheme i ν ∅).X.hom := hMc.isAffineHom
  have hmax : IsMaximalSplitTorus (torusToStandardLevi F G T i ν) :=
    hTmax.isMaximalSplitTorus_standardLeviTorusFactor i ν ∅
      (Standard.isRepresentedBy_leviHom i ν ∅) hMc
  have hcent : IsCentral (torusToStandardLevi F G T i ν) := by
    apply isCentral_of_range_le_torusCentralizer
      (Standard.isRepresentedBy_leviHom i ν ∅).1
    rw [torusToStandardLevi_comp, (Standard.isRepresentedBy_leviHom i ν ∅).2, hlevi]
  have hsplitM : IsSplitComponent (torusToStandardLevi F G T i ν) :=
    ⟨⟨hmax.1, hcent⟩, fun A' i' hi' g hg => hmax.2 A' i' hi'.1 g hg⟩
  obtain ⟨⟨aT, nM⟩, hEM⟩ := (PositiveRealTorus.splitComponentNormOneDecomposition
    centralSplitTorusCharacter F (Standard.leviScheme i ν ∅) hRL.isConnectedReductive T
    (torusToStandardLevi F G T i ν) hsplitM).surjective mM
  rw [PositiveRealTorus.splitComponentNormOneDecomposition_apply] at hEM
  refine ⟨n, nM, aT, k, hk, ?_⟩
  have hmM' : map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) mM =
      map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅)
          (nM : AdelicGroupPoints F (Standard.leviScheme i ν ∅)) *
        map F T.toGrp G i (aT : AdelicGroupPoints F T.toGrp) := by
    rw [← hEM, (PositiveRealTorus.positivePointMap_commute F (Standard.leviScheme i ν ∅) T _
      hcent aT nM).eq, map_mul, PositiveRealTorus.positivePointMap_apply,
      ← adelicPointsMap_comp_apply, torusToStandardLevi_comp]
  have hpU : p = map F _ G (Standard.unipotentHom i ν ∅) n *
      map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) mM := by
    change _ = (map F _ G (Standard.unipotentHom i ν ∅)).toMonoidHom n *
      (map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅)).toMonoidHom mM
    rw [hn, hmM, inv_mul_cancel_right]
  rw [← hqk, hpU, hmM', mul_assoc (map F _ G (Standard.unipotentHom i ν ∅) n)]

end Factors


section Transport

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- A left factor from a compact set transfers all finite simultaneous minimum
inequalities on the full adelic group, with the square of the distortion constant. -/
theorem adelicChainHeightMinimalSet_mul_of_distortionBound
    {r : ℕ} {d : ℕ → ℕ} {ρ : (l : ℕ) → MatrixRepresentation G (Fin (d l))}
    {C : Set (AdelicGroupPoints F G)} {B : ℝ}
    (h : IsSimultaneousOrbitHeightDistortionBound F G r d ρ C B) (hB : 0 ≤ B)
    (v : (l : ℕ) → Fin (d l) → F) (hv : ∀ l, l < r → v l ≠ 0)
    (Q : ℕ → Subgroup (RationalGroupPoints F G))
    {k : AdelicGroupPoints F G} (hk : k ∈ C) {g : AdelicGroupPoints F G} {c : ℝ} (hc : 0 ≤ c)
    (hg : g ∈ adelicChainHeightMinimalSet F G r d ρ v Q c) :
    k * g ∈ adelicChainHeightMinimalSet F G r d ρ v Q (B ^ 2 * c) := by
  intro l hl q
  obtain ⟨hup, _⟩ := h l hl k hk g (v l) (hv l hl)
  obtain ⟨_, hlo⟩ := h l hl k hk (g * rational F G q) (v l) (hv l hl)
  have hmin := hg l hl q
  calc orbitHeight F G (ρ l) (v l) (k * g)
      ≤ B * orbitHeight F G (ρ l) (v l) g := hup
    _ ≤ B * (c * orbitHeight F G (ρ l) (v l) (g * rational F G q)) :=
        mul_le_mul_of_nonneg_left hmin hB
    _ ≤ B * (c * (B * orbitHeight F G (ρ l) (v l) (k * (g * rational F G q)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlo hc) hB
    _ = B ^ 2 * c * orbitHeight F G (ρ l) (v l) (k * g * rational F G q) := by
        rw [mul_assoc k]
        ring

/-- The orbit height of the trivial representation is invariant under right rational
translation. -/
theorem orbitHeight_trivial_mul_rational {n : ℕ} (v : Fin n → F) (g : AdelicGroupPoints F G)
    (q : RationalGroupPoints F G) :
    orbitHeight F G (MatrixRepresentation.trivial G (Fin n)) v (g * rational F G q) =
      orbitHeight F G (MatrixRepresentation.trivial G (Fin n)) v g := by
  rw [orbitHeight_mul_rational]
  congr 1
  change ((MatrixRepresentation.trivial G (Fin n)).affineMatrix (CommAlgCat.of F F) q).val *ᵥ
    v = v
  rw [MatrixRepresentation.trivial_affineMatrix, Units.val_one, Matrix.one_mulVec]

end Transport

section RelativeChain

/-- The dimensions of the relative chain: `1` (trivial representation) at index `0`, then the
given dimensions `d l + 1`. -/
def relativeChainDim (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | l + 1 => d l + 1

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) {d : ℕ → ℕ}

/-- The representations of the relative chain: the trivial representation at index `0`, then
the given ones. -/
def relativeChainRep (ρ : (l : ℕ) → MatrixRepresentation G (Fin (d l + 1))) :
    (l : ℕ) → MatrixRepresentation G (Fin (relativeChainDim d l))
  | 0 => MatrixRepresentation.trivial G (Fin 1)
  | l + 1 => ρ l

variable {G}

/-- The selected coordinates of the relative chain. -/
def relativeChainIndex (b : (l : ℕ) → Fin (d l + 1)) : (l : ℕ) → Fin (relativeChainDim d l)
  | 0 => (0 : Fin 1)
  | l + 1 => b l

/-- The parabolic indices of the relative chain: `S` at index `0`, then the given ones. -/
def relativeChainFamily {X : Type*} (S : Set X) (J : ℕ → Set X) : ℕ → Set X
  | 0 => S
  | l + 1 => J l

theorem relativeChainDim_pos (d : ℕ → ℕ) (l : ℕ) : 0 < relativeChainDim d l := by
  cases l <;> simp [relativeChainDim]

end RelativeChain


section RelativeReduction

open Opposite

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- **Relative chamber reduction on all of `G(𝔸_F)`.** For an actual setup, every compact
subgroup `K` with `P_0(𝔸_F) K = G(𝔸_F)` and every set `S₁` of simple relative roots (the
standard parabolic `P_1` with `Δ_0^{P_1} = S₁`), there is a positive threshold `t` such that
every `g ∈ G(𝔸_F)` has a left translate by a rational point `q ∈ P_1(F)` of the form `n m a k`
with `n ∈ N_0(𝔸_F)`, `m ∈ M_0(𝔸_F)¹`, `a` an intrinsic positive point of `T` with
`t ≤ |α(a)|` for every `α ∈ S₁`, and `k ∈ K`. -/
theorem exists_relativeChamberReduction (hG : IsConnectedReductive G)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (S₁ : Finset (characterLattice T))
    (hS₁ : (S₁ : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν) :
    ∃ t : ℝ≥0ˣ, ∀ g : AdelicGroupPoints F G, ∃ q : RationalGroupPoints F G,
      q ∈ (SubgroupFunctor.range
          (Standard.parabolicHom i ν (S₁ : Set (characterLattice T)))).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))) ∧
      ∃ (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
        (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
        (a : PositiveRealTorus.intrinsicSubgroup F T),
        (∀ α ∈ S₁, t ≤ PositiveRealTorus.normCharacter F T α
          (a : AdelicGroupPoints F T.toGrp)) ∧
        ∃ k ∈ K, map F _ G (Standard.unipotentHom i ν ∅) n *
          map F _ G (Standard.leviHom i ν ∅) m *
          map F T.toGrp G i (a : AdelicGroupPoints F T.toGrp) * k = rational F G q * g := by
  classical
  have hi : IsMaximalSplitTorus i := hS.1
  have hν : IsGenericCocharacter i ν := hS.2.1
  -- an enumeration of `S₁`
  let r := S₁.card
  let e : Fin r ≃ S₁ := S₁.equivFin.symm
  let α : ℕ → characterLattice T := fun l => if h : l < r then (e ⟨l, h⟩).val else 0
  have hαS (l : ℕ) (hl : l < r) : α l ∈ S₁ := by
    simp only [α, dite_eq_left hl]
    exact (e ⟨l, hl⟩).property
  have hinj (a l : ℕ) (ha : a < r) (hl : l < r) (heq : α a = α l) : a = l := by
    simp only [α, dite_eq_left ha, dite_eq_left hl] at heq
    exact congrArg Fin.val (e.injective (Subtype.ext heq))
  have hcover (β : characterLattice T) (hβ : β ∈ S₁) : ∃ l, l < r ∧ α l = β := by
    let l := e.symm ⟨β, hβ⟩
    refine ⟨l.val, l.isLt, ?_⟩
    simp only [α, dite_eq_left l.isLt, Fin.eta]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨β, hβ⟩)
  -- the maximal parabolics omitting the roots of `S₁`, with exact Chevalley lines
  let J : ℕ → Set (characterLattice T) := fun l => simpleRelativeRoots i ν \ {α l}
  obtain ⟨d, b, ρ, hstab, -, -⟩ := exists_adapted_standardParabolicPrefix_minima F G T i ν J
  -- the relative chain: `P_1` with the trivial representation, then the maximal parabolics
  let Kf : ℕ → Set (characterLattice T) := relativeChainFamily (S₁ : Set (characterLattice T)) J
  have hKf : ∀ a, Kf a ⊆ simpleRelativeRoots i ν := by
    intro a
    cases a with
    | zero => exact hS₁
    | succ a => exact fun _ h => h.1
  let d' := relativeChainDim d
  let ρ' := relativeChainRep G ρ
  let b' := relativeChainIndex b
  let Q := closedPrefixRationalSubgroup F G (fun a => Standard.parabolicScheme i ν (Kf a))
    (fun a => Standard.parabolicHom i ν (Kf a))
  have hv' : ∀ l, l < r + 1 → (Pi.single (b' l) 1 : Fin (d' l) → F) ≠ 0 := by
    intro l _ hz
    have he := congrFun hz (b' l)
    simp at he
  -- one distortion constant for the compact subgroup
  obtain ⟨B, hB, hdist⟩ := exists_pos_simultaneous_orbitHeight_distortionBound F G (r + 1) d' ρ'
    (fun l _ => relativeChainDim_pos d l) hK.isCompact
  have hc : 0 < B ^ 2 * 1 := by positivity
  let S : Set (AdelicGroupPoints F T.toGrp) := {s |
    ∃ (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
      (x : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅)),
      map F _ G (Standard.leviHom i ν ∅) m * map F _ G i s *
          map F _ G (Standard.unipotentHom i ν ∅) x ∈
        adelicChainHeightMinimalSet F G (r + 1) d' ρ' (fun l => Pi.single (b' l) 1) Q
          (B ^ 2 * 1)}
  -- the rank-one root bounds for the roots of `S₁`
  have hbound : ∀ β ∈ S₁, PositiveRealTorus.HasUniformCharacterBound F T β S := by
    intro β hβ
    obtain ⟨l, hl, rfl⟩ := hcover β hβ
    refine hasUniformRootBound_of_minimal_coordinates_and_prefix_minima
      F G T i ν rankOneParabolicRationalOrbitHeightBound hG hi hν Kf hKf (r + 1) d' ρ' b'
        (l + 1) (by omega) (hstab l) (α l) (hS₁ (hαS l hl))
        (by simp [Kf, relativeChainFamily, J]) (fun a ha => ?_) (B ^ 2 * 1) hc S
        (fun _ hs => hs)
    cases a with
    | zero => exact hαS l hl
    | succ a =>
      refine ⟨hS₁ (hαS l hl), ?_⟩
      simp only [Set.mem_singleton_iff]
      intro heq
      have := hinj l a hl (by omega) heq
      omega
  choose C hC using fun β : S₁ => hbound β β.property
  obtain ⟨Cmax, hCmax⟩ := (Set.finite_range C).bddAbove
  refine ⟨Cmax⁻¹, fun g => ?_⟩
  -- simultaneous minima of `g⁻¹` over `P_1(F)` for the maximal parabolic lines
  have hQanti : Antitone Q := closedPrefixRationalSubgroup_antitone F G _ _
  obtain ⟨q, hq⟩ := exists_simultaneous_min_orbitHeight F G r (fun l => d' (l + 1))
    (fun l => ρ' (l + 1)) (fun l => Pi.single (b' (l + 1)) 1)
    (fun l hl => hv' (l + 1) (by omega)) (fun l => Q (l + 1))
    (fun a l hal => hQanti (by omega)) (by
      intro a l hal hl s
      have hs : (s : RationalGroupPoints F G) ∈ closedChainRationalSubgroup F G
          (fun a => Standard.parabolicScheme i ν (Kf a))
          (fun a => Standard.parabolicHom i ν (Kf a)) (a + 1) :=
        (mem_closedPrefixRationalSubgroup F G _ _ (l + 1) _).1 s.2 (a + 1) (by omega)
      have hs' : (s : RationalGroupPoints F G) ∈ (standardParabolic i ν (J a)).carrier
          ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))) := by
        have h := hs
        change _ ∈ (SubgroupFunctor.range (Standard.parabolicHom i ν (J a))).carrier _ at h
        rwa [(Standard.isRepresentedBy_parabolicHom i ν (J a)).2] at h
      exact ((ρ a).affine_coordinateLine_scalar_iff (CommAlgCat.of F F) _ (b a)).1
        ((hstab a _ _).1 hs')) g⁻¹
  have hmem : g⁻¹ * rational F G (q : RationalGroupPoints F G) ∈
      adelicChainHeightMinimalSet F G (r + 1) d' ρ' (fun l => Pi.single (b' l) 1) Q 1 := by
    intro l hl s
    cases l with
    | zero =>
      rw [one_mul]
      exact (orbitHeight_trivial_mul_rational (n := 1) _ _ _).ge
    | succ l =>
      rw [one_mul]
      exact hq l (by omega) s
  -- the Iwasawa factors of the translate
  let z : AdelicGroupPoints F G := rational F G (q : RationalGroupPoints F G)⁻¹ * g
  obtain ⟨x, m, a, k, hk, heq⟩ := exists_torus_iwasawa_factors F G T i ν T₀ j hS hK z
  let p₀ := map F _ G (Standard.unipotentHom i ν ∅) x *
    map F _ G (Standard.leviHom i ν ∅) m * map F T.toGrp G i (a : AdelicGroupPoints F T.toGrp)
  have hp₀ : p₀⁻¹ = k * (g⁻¹ * rational F G (q : RationalGroupPoints F G)) := by
    have h : p₀ = z * k⁻¹ := by
      rw [← heq]
      simp only [p₀, mul_inv_cancel_right]
    rw [h, mul_inv_rev, inv_inv]
    simp only [z, mul_inv_rev, map_inv, inv_inv]
  have hmem' : p₀⁻¹ ∈ adelicChainHeightMinimalSet F G (r + 1) d' ρ'
      (fun l => Pi.single (b' l) 1) Q (B ^ 2 * 1) := by
    rw [hp₀]
    exact adelicChainHeightMinimalSet_mul_of_distortionBound hdist hB.le _ hv' Q hk zero_le_one hmem
  have hporder :
      map F _ G (Standard.leviHom i ν ∅) ((m⁻¹ : normOneSubgroup F _) :
          AdelicGroupPoints F (Standard.leviScheme i ν ∅)) *
        map F _ G i (a : AdelicGroupPoints F T.toGrp)⁻¹ *
        map F _ G (Standard.unipotentHom i ν ∅) x⁻¹ = p₀⁻¹ := by
    have hcomm := (hS.commute_torus_minimalLevi F G T i ν T₀ j
      (a : AdelicGroupPoints F T.toGrp) m).inv_inv
    simp only [p₀, mul_inv_rev, Subgroup.coe_inv, map_inv]
    rw [← mul_assoc, hcomm.eq]
  have hsa : (a : AdelicGroupPoints F T.toGrp)⁻¹ ∈ S := ⟨m⁻¹, x⁻¹, by rw [hporder]; exact hmem'⟩
  refine ⟨(q : RationalGroupPoints F G)⁻¹, ?_, x, m, a, fun β hβ => ?_, k, hk, heq⟩
  · exact (mem_closedPrefixRationalSubgroup F G _ _ 1 _).1 ((Q 1).inv_mem q.2) 0 Nat.zero_lt_one
  · have h1 := hC ⟨β, hβ⟩ _ hsa
    have h2 : C ⟨β, hβ⟩ ≤ Cmax := hCmax ⟨⟨β, hβ⟩, rfl⟩
    rw [map_inv] at h1
    exact inv_le'.mp (h1.trans h2)

end RelativeReduction

end Langlands.Global.AdelicSiegelFactors
