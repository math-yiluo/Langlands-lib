import Langlands.GroupScheme.Reductive.TitsRootVanishing
import Langlands.GroupScheme.MatrixRepresentation.ScalarExtensionCoordinates

/-! # Scalar extensions of representations over `k` are Galois-rational -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The universal matrix of the scalar extension of a representation over `k` has entries
`1 ⊗ c` with `c` in the coordinate ring of `G`. -/
theorem universalMatrix_baseChange (ρ : MatrixRepresentation G n) (i j : n) :
    universalMatrix (ρ.baseChange (algebraBaseMap k K)) i j =
      (Algebra.TensorProduct.includeRight : CharacterUnits.Coord G →ₐ[k]
        K ⊗[k] CharacterUnits.Coord G)
        ((ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (CharacterUnits.Coord G))
          (CharacterUnits.universalPoint G) : Matrix n n _) i j) := by
  have h1 := affineMatrix_scalarExtensionPoint (K := K) (K ⊗[k] CharacterUnits.Coord G) ρ
    ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeRight : CharacterUnits.Coord G →ₐ[k]
        K ⊗[k] CharacterUnits.Coord G)).op ≫ CharacterUnits.universalPoint G)
  have h2 := ρ.affineMatrix_naturality (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeRight : CharacterUnits.Coord G →ₐ[k]
        K ⊗[k] CharacterUnits.Coord G)) (CharacterUnits.universalPoint G)
  rw [h2] at h1
  have h3 := congrArg (fun M => M.val i j) h1
  exact h3

/-- Every Galois twist of a scalar-extended representation has the same universal matrix. -/
theorem universalMatrix_galoisTwist_baseChange (σ : K ≃ₐ[k] K) (ρ : MatrixRepresentation G n) :
    universalMatrix (galoisTwist σ (ρ.baseChange (algebraBaseMap k K))) =
      universalMatrix (ρ.baseChange (algebraBaseMap k K)) := by
  rw [universalMatrix_galoisTwist]
  ext i j
  rw [Matrix.map_apply, universalMatrix_baseChange]
  change galoisTensor _ σ (1 ⊗ₜ _) = 1 ⊗ₜ _
  rw [galoisTensor_tmul, map_one]

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The scalar extension of a representation over `k` is Galois-rational. -/
theorem isGaloisRational_baseChange (ρ : MatrixRepresentation G n) :
    IsGaloisRational (ρ.baseChange (algebraBaseMap k K)) :=
  fun σ => universalMatrix_galoisTwist_baseChange σ ρ

end Langlands.GroupScheme.GaloisPinningData

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (d : GaloisPinningData k K G)

local instance groundMaximalAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- The sum of a set of simple roots. -/
def simpleRootSum (O : Finset d.toSplitPinning.base.support) :
    characterLattice d.toSplitPinning.torus :=
  ∑ i ∈ O, d.toSplitPinning.rootDatum.root i

/-- Some representation of `G` over `k` has, after scalar extension to `K`, the weight `ν` with
multiplicity one, and no weight strictly above `ν`. -/
def HasGroundMaximalWeight (nu : characterLattice d.toSplitPinning.torus) : Prop :=
  ∃ (m : ℕ) (ρ : MatrixRepresentation G (Fin (m + 1))),
    Module.finrank K (d.toSplitPinning.representationWeightSpace
      (ρ.baseChange (algebraBaseMap k K)) nu) = 1 ∧
    ∀ mu, d.toSplitPinning.representationWeightSpace (ρ.baseChange (algebraBaseMap k K)) mu ≠ ⊥ →
      mu - nu ∈ d.toSplitPinning.positiveRootMonoid → mu = nu

theorem hasRationalMaximalWeight_of_ground {nu : characterLattice d.toSplitPinning.torus}
    (h : d.HasGroundMaximalWeight nu) : d.HasRationalMaximalWeight nu := by
  obtain ⟨m, ρ, hmult, hmax⟩ := h
  exact ⟨Fin (m + 1), inferInstance, inferInstance, inferInstance, _,
    isGaloisRational_baseChange ρ, hmult, hmax⟩

variable [LocallyOfFiniteType G.X.hom]

theorem starOrbitSum_eq_simpleRootSum (q : d.StarOrbit) :
    d.starOrbitSum q = d.simpleRootSum (by
      classical
      exact Finset.univ.filter (fun i => (Quotient.mk _ i : d.StarOrbit) = q)) := by
  classical
  rw [starOrbitSum, simpleRootSum]

variable [IsGalois k K] 
  (hspan : d.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)

/-- Root-span vanishing of the Tits obstruction, reduced to representations over `k`: if for a
star-fixed weight `δ` and every set `O` of simple roots some representation over `k` has
`δ - ∑_{i ∈ O} α_i` as a maximal weight of multiplicity one, the obstruction vanishes on every
star-fixed element of the integral root span. -/
theorem titsObstructionValue_eq_zero_of_mem_rootSpan_of_ground
    {δ : characterLattice d.toSplitPinning.torus} (hδ : d.IsStarFixedWeight δ)
    (hground : ∀ O : Finset d.toSplitPinning.base.support,
      d.HasGroundMaximalWeight (δ - d.simpleRootSum O))
    {lam : characterLattice d.toSplitPinning.torus}
    (hlam : lam ∈ d.toSplitPinning.rootDatum.rootSpan ℤ) (hfix : d.IsStarFixedWeight lam) :
    d.titsObstructionValue hspan lam hfix = 0 := by
  classical
  refine d.titsObstructionValue_eq_zero_of_mem_rootSpan hspan hδ ?_ ?_ hlam hfix
  · have h := hground ∅
    rw [simpleRootSum, Finset.sum_empty, sub_zero] at h
    exact d.hasRationalMaximalWeight_of_ground h
  · intro q
    rw [d.starOrbitSum_eq_simpleRootSum q]
    exact d.hasRationalMaximalWeight_of_ground (hground _)

end Langlands.GroupScheme.GaloisPinningData
