import Langlands.Representation.Plancherel.RationalFiniteSignedCartanCoverStatement
import Langlands.Representation.Aubert.General.RationalEndpoint
import Langlands.Algebra.FiniteSignedChamberLatticeProof
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterLinear
import Mathlib.Tactic.Group

/-! # Independent actual Cartan charts with all lattice directions retained -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan
open Langlands.BruhatTits.SpecialCompact Langlands.Plancherel.RenardCartan
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-- The actual Cartan middle elements admit finite signed cocharacter charts. -/
theorem rationalFiniteSignedCartanCover : RationalFiniteSignedCartanCoverStatement.{u} := by
  intro F _ _ _ _ G hG S i hi ν
  let := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let := hi.isSplitSubtorus.mono
  intro _ hν hStandard D x Z j s h hsj hcompat F₀ hF₀
  classical
  let := hi.isSplitSubtorus.1.finite_cocharacterLattice
  let := hi.isSplitSubtorus.1.torsionFree_cocharacterLattice
  have hfull : levi i ν Finset.univ = ⊤ := levi_univ_eq_top i ν hStandard hG hi hν
  have hstd (I : Finset (SimpleRoot i ν)) : ∃ ζ : cocharacterLattice S,
      (∀ β ∈ I, simpleRootPairing i ν β ζ = 0) ∧
        ∀ β ∉ I, 0 < simpleRootPairing i ν β ζ := by
    obtain ⟨ζ, hζ⟩ :=
      (hStandard F G hG S i hi ν hν _ (rootSet_subset i ν I)).1
    exact ⟨ζ, fun β hβ => hζ.2.1 β.1 ((val_mem_rootSet i ν I β).mpr hβ),
      fun β hβ => hζ.2.2 β.1 β.2 fun h' => hβ ((val_mem_rootSet i ν I β).mp h')⟩
  obtain ⟨k, gen, hgen, hnonneg, hdecomp⟩ :=
    finiteSignedChamberLattice (SimpleRoot i ν) (cocharacterLattice S)
      (simpleRootPairing i ν) hstd
  obtain ⟨jM, _, _, _, _, _, _, hlat⟩ := hcompat ∅ (Set.empty_subset _)
  obtain ⟨B, hB⟩ := exists_rep_rationalCartanSet i ν j s h hsj hlat.1 hF₀.1 Finset.univ
  obtain ⟨R, hR, hRrep⟩ := hdecomp B
  let e := uniformizerPowers i
  let F₁ : Set (rationalPoints G) := rationalPoints.map j '' F₀
  let T : Set (rationalPoints G) :=
    (fun p : cocharacterLattice S × rationalPoints G => e (.ofAdd p.1) * p.2) '' (R ×ˢ F₁)
  refine ⟨k, gen, hgen, hnonneg, T, (hR.prod (hF₀.1.image _)).image _, fun g => ?_⟩
  obtain ⟨k₁, hk₁, t, ht, k₂, hk₂, hg⟩ := exists_cartan_levi D x ν hcompat hF₀
    Finset.univ g (by rw [hfull]; exact Subgroup.mem_top _)
  obtain ⟨c, f, hf, htcf, hc⟩ := hB t ht
  obtain ⟨r, hr, ε, n, hcr⟩ := hRrep c (fun α => hc α (Finset.mem_univ α))
  have he : e (.ofAdd c) =
      e (.ofAdd r) * e (.ofAdd (∑ a, n a • gen ε a)) := by
    rw [hcr, ofAdd_add, map_mul]
  have hcomm : e (.ofAdd r) * e (.ofAdd (∑ a, n a • gen ε a)) =
      e (.ofAdd (∑ a, n a • gen ε a)) * e (.ofAdd r) := by
    rw [← e.map_mul, ← e.map_mul, mul_comm]
  refine ⟨ε, n, k₁, hk₁.1, e (.ofAdd r) * f,
    ⟨(r, f), ⟨hr, hf⟩, rfl⟩, k₂, hk₂.1, ?_⟩
  change g = k₁ * e (.ofAdd (∑ a, n a • gen ε a)) * (e (.ofAdd r) * f) * k₂
  rw [hg, htcf]
  change k₁ * (e (.ofAdd c) * f) * k₂ = _
  rw [he, hcomm]
  group

end Langlands.Plancherel
