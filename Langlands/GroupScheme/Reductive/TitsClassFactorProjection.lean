import Langlands.GroupScheme.Reductive.TitsDominantClass
import Langlands.GroupScheme.Reductive.TitsAlgebraTransport
import Langlands.GroupScheme.Rational.PathFundamentalWeights
import Langlands.GroupScheme.Torus.GaloisCharacterFunctor
import Langlands.Algebra.BrauerGroup

/-! # Highest weights and Tits classes under an actual factor projection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {K : Type u} [Field K] {G H : GroupScheme (Spec (CommRingCat.of K))}
  {n : Type} [Fintype n] [DecidableEq n]

private theorem isIrreducible_restrict_of_section
    {ρ : MatrixRepresentation H n} (hρ : ρ.IsIrreducible)
    {f : G ⟶ H} {j : H ⟶ G} (hs : j ≫ f = 𝟙 H) :
    (ρ.restrict f).IsIrreducible := by
  refine ⟨hρ.1, fun V hV => hρ.2 V ?_⟩
  simpa only [restrict_comp, hs, restrict_id] using hV.restrict j

end MatrixRepresentation

namespace GaloisPinningData

open MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (p : GaloisPinningData k K G) (q : GaloisPinningData k K H)

local notation "gChange" => GroupScheme.baseChange (algebraBaseMap k K)
local notation "tChange" => CommGroupScheme.baseChange (algebraBaseMap k K)

local instance affineGeometricAmbient : IsAffineHom ((gChange).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

local instance affineGeometricFactor : IsAffineHom ((gChange).obj H).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom _)
  infer_instance

/-- An actual retraction over the ground field with a compatible retraction on
maximal tori and the inflation of simple roots through the projection. -/
structure FactorProjection where
  inclusion : H ⟶ G
  projection : G ⟶ H
  section_comp : inclusion ≫ projection = 𝟙 H
  torusInclusion : q.torus ⟶ p.torus
  torusProjection : p.torus ⟶ q.torus
  torus_section_comp : torusInclusion ≫ torusProjection = 𝟙 q.torus
  torusProjection_comp : p.inclusion ≫ projection =
    CommGroupScheme.groupHom torusProjection ≫ q.inclusion
  vertices : q.base.support ↪ p.base.support
  root_eq : ∀ a : q.base.support, (tChange).map torusProjection ≫ q.rootDatum.root a.val =
    p.rootDatum.root (vertices a).val

namespace FactorProjection

variable {p q} (F : p.FactorProjection q)

/-- Inflation of an actual integral character through the compatible torus projection. -/
def weightInflation :
    characterLattice q.toSplitPinning.torus →ₗ[ℤ] characterLattice p.toSplitPinning.torus :=
  characterLattice.pullback ((tChange).map F.torusProjection)

private theorem geometricSection_comp : (gChange).map F.inclusion ≫ (gChange).map F.projection = 𝟙 _ := by
  rw [← (gChange).map_comp, F.section_comp, (gChange).map_id]

private theorem geometricTorusSection_comp :
    (tChange).map F.torusInclusion ≫ (tChange).map F.torusProjection = 𝟙 _ := by
  rw [← (tChange).map_comp, F.torus_section_comp, (tChange).map_id]

private theorem geometricTorusProjection_comp :
    p.toSplitPinning.inclusion ≫ (gChange).map F.projection =
      CommGroupScheme.groupHom ((tChange).map F.torusProjection) ≫ q.toSplitPinning.inclusion := by
  change (gChange).map p.inclusion ≫ (gChange).map F.projection =
    (gChange).map (CommGroupScheme.groupHom F.torusProjection) ≫ (gChange).map q.inclusion
  rw [← (gChange).map_comp, F.torusProjection_comp, (gChange).map_comp]

/-- The inflated weight space is exactly the factor weight space. -/
theorem representationWeightSpace_inflation {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation ((gChange).obj H) n)
    (μ : characterLattice q.toSplitPinning.torus) :
    p.toSplitPinning.representationWeightSpace (ρ.restrict ((gChange).map F.projection))
      (F.weightInflation μ) = q.toSplitPinning.representationWeightSpace ρ μ := by
  let : IsAffineHom ((tChange).obj p.torus).X.hom := p.isSplitTorus.isAffineHom
  let : IsAffineHom ((tChange).obj q.torus).X.hom := q.isSplitTorus.isAffineHom
  let : IsAffineHom p.toSplitPinning.torus.X.hom := p.toSplitPinning.isSplitTorus.isAffineHom
  let : IsAffineHom q.toSplitPinning.torus.X.hom := q.toSplitPinning.isSplitTorus.isAffineHom
  let ψ := ρ.restrict q.toSplitPinning.inclusion
  let t := CommGroupScheme.groupHom ((tChange).map F.torusProjection)
  let s := CommGroupScheme.groupHom ((tChange).map F.torusInclusion)
  let χ := (rationalCharacters.equivCharacterLattice q.toSplitPinning.torus).symm μ
  have hst : s ≫ t = 𝟙 _ := congrArg CommGroupScheme.groupHom F.geometricTorusSection_comp
  unfold SplitPinning.representationWeightSpace
  rw [MatrixRepresentation.restrict_comp, F.geometricTorusProjection_comp,
    ← MatrixRepresentation.restrict_comp]
  change (ψ.restrict t).characterSpace (characterRestrict t χ) = ψ.characterSpace χ
  apply le_antisymm
  · have h := characterSpace_le_restrict (ψ.restrict t) s (characterRestrict t χ)
    have hc : characterRestrict s (characterRestrict t χ) = χ := by
      change ((characterRestrict s).comp (characterRestrict t)) χ = χ
      rw [← characterRestrict_comp, hst, characterRestrict_id]
      rfl
    have hid : ψ.restrict (𝟙 ((tChange).obj q.torus).toGrp) = ψ := restrict_id ψ
    simpa only [restrict_comp, hst, hid, hc] using h
  · exact characterSpace_le_restrict ψ t χ

private theorem inflation_mem_positiveRootMonoid
    {μ : characterLattice q.toSplitPinning.torus}
    (hμ : μ ∈ q.toSplitPinning.positiveRootMonoid) :
    F.weightInflation μ ∈ p.toSplitPinning.positiveRootMonoid := by
  refine AddSubmonoid.closure_induction (fun x hx => ?_) (by simp)
    (fun x y _ _ hx hy => by simpa only [map_add] using add_mem hx hy) hμ
  obtain ⟨a, rfl⟩ := hx
  have hroot := F.root_eq a
  change F.weightInflation (q.rootDatum.root a.val) = p.rootDatum.root (F.vertices a).val at hroot
  change F.weightInflation (q.rootDatum.root a.val) ∈ p.toSplitPinning.positiveRootMonoid
  rw [hroot]
  exact p.toSplitPinning.simpleRoot_mem_positiveRootMonoid (F.vertices a)

/-- Pulling back a factor representation through the projection retains its actual
irreducible highest-weight structure at the inflated weight. -/
theorem isHighestWeight_inflation {n : Type} [Fintype n] [DecidableEq n]
    {ρ : MatrixRepresentation ((gChange).obj H) n} {μ : characterLattice q.toSplitPinning.torus}
    (hρ : q.toSplitPinning.IsHighestWeight ρ μ) :
    p.toSplitPinning.IsHighestWeight (ρ.restrict ((gChange).map F.projection)) (F.weightInflation μ) := by
  let τ := ρ.restrict ((gChange).map F.projection)
  change p.toSplitPinning.IsHighestWeight τ (F.weightInflation μ)
  have hspaces := F.representationWeightSpace_inflation ρ
  have htop : (⨆ ν, p.toSplitPinning.representationWeightSpace τ (F.weightInflation ν)) = ⊤ := by
    simp only [τ, hspaces, hρ.2.1]
  refine ⟨isIrreducible_restrict_of_section hρ.1 F.geometricSection_comp,
    top_unique (htop ▸ iSup_le fun ν => le_iSup (p.toSplitPinning.representationWeightSpace τ) _),
    ?_, ?_⟩
  · change Module.finrank K (p.toSplitPinning.representationWeightSpace
      (ρ.restrict ((gChange).map F.projection)) (F.weightInflation μ)) = 1
    rw [hspaces]
    exact hρ.2.2.1
  · intro ν hν
    have himage : ∃ β, F.weightInflation β = ν := by
      by_contra hno
      have hmem : ν ∉ Set.range F.weightInflation := hno
      have hdisj := (p.toSplitPinning.iSupIndep_representationWeightSpace τ).disjoint_biSup
        hmem
      have hsum : (⨆ β ∈ Set.range F.weightInflation,
          p.toSplitPinning.representationWeightSpace τ β) = ⊤ := by
        refine top_unique (htop ▸ iSup_le fun β => ?_)
        exact le_iSup_of_le (F.weightInflation β)
          (le_iSup_of_le (Set.mem_range_self β) le_rfl)
      rw [hsum, disjoint_top] at hdisj
      exact hν hdisj
    obtain ⟨β, rfl⟩ := himage
    rw [← map_sub]
    exact F.inflation_mem_positiveRootMonoid (hρ.2.2.2 β (by simpa only [τ, hspaces] using hν))

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom] [IsGalois k K]

/-- An inflated dominant fixed highest weight has the same actual Tits class
as its factor weight. -/
theorem dominantTitsClass_inflation {μ : characterLattice q.toSplitPinning.torus}
    (hdom : q.toSplitPinning.IsDominantWeight μ) (hfix : q.IsStarFixedWeight μ)
    (hdom' : p.toSplitPinning.IsDominantWeight (F.weightInflation μ))
    (hfix' : p.IsStarFixedWeight (F.weightInflation μ)) :
    p.dominantTitsClass (F.weightInflation μ) hdom' hfix' =
      q.dominantTitsClass μ hdom hfix := by
  obtain ⟨n, ρ, hρ⟩ := (splitHighestWeightClassification K _ q.toSplitPinning).1 μ hdom
  have hτ := F.isHighestWeight_inflation hρ
  rw [p.dominantTitsClass_eq hdom' hfix' hτ, q.dominantTitsClass_eq hdom hfix hρ]
  have := q.nonempty_of_isHighestWeight hρ
  let P (σ : K ≃ₐ[k] K) := (q.exists_intertwiner_galoisTwist hρ hfix σ).choose
  have hPu (σ : K ≃ₐ[k] K) : IsUnit (P σ) :=
    (q.exists_intertwiner_galoisTwist hρ hfix σ).choose_spec.2
  have hP (σ : K ≃ₐ[k] K) : ρ.Intertwines (galoisTwist σ ρ) (P σ) :=
    (q.exists_intertwiner_galoisTwist hρ hfix σ).choose_spec.1
  have hA : titsAlgebra (ρ.restrict ((gChange).map F.projection)) = titsAlgebra ρ := by
    rw [titsAlgebra_eq_twistedFixed ρ hρ.1
      (SplitPinning.IsHighestWeight.intertwiner_eq_scalar _ hρ) P hPu hP]
    exact titsAlgebra_eq_twistedFixed _ hτ.1
      (SplitPinning.IsHighestWeight.intertwiner_eq_scalar _ hτ) P hPu
      (fun σ => intertwines_restrict_galoisTwist σ (hP σ) F.projection)
  exact Brauer.classOf_eq_of_algEquiv (A := p.titsCSAOf hτ hfix') (B := q.titsCSAOf hρ hfix)
    (Subalgebra.equivOfEq _ _ hA)

end FactorProjection
end GaloisPinningData
end Langlands.GroupScheme
