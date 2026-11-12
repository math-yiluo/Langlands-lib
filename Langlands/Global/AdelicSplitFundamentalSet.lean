import Langlands.Global.AdelicSiegelChamberReduction

/-! # Springer's split fundamental-set target on actual adelic points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Springer's right-action fundamental-set property, using the full adelic split torus
and the norm-one subgroup defined by all characters of the actual minimal parabolic. -/
def HasRightAdelicFundamentalSet : Prop :=
  ∃ C : Set (normOneSubgroup F G), IsCompact C ∧
    ∃ c : ℝ≥0ˣ, ∀ g : normOneSubgroup F G,
      ∃ (q : RationalGroupPoints F G) (s : AdelicGroupPoints F T.toGrp)
        (p : normOneSubgroup F (Standard.parabolicScheme i ν ∅)),
        map F T.toGrp G i s ∈ normOneSubgroup F G ∧
          (∀ α ∈ simpleRelativeRoots i ν, PositiveRealTorus.normCharacter F T α s ≤ c) ∧
          ∃ x ∈ C, (x : AdelicGroupPoints F G) * map F T.toGrp G i s *
            map F _ G (Standard.parabolicHom i ν ∅) p * rational F G q = g

/-- The same factorization after inversion: rational points are on the left, simple-root
norms have a positive lower bound, and the parabolic factor precedes the torus. -/
def HasLeftAdelicFundamentalSet : Prop :=
  ∃ C : Set (normOneSubgroup F G), IsCompact C ∧
    ∃ t : ℝ≥0ˣ, ∀ g : normOneSubgroup F G,
      ∃ (q : RationalGroupPoints F G) (p : normOneSubgroup F (Standard.parabolicScheme i ν ∅))
        (s : AdelicGroupPoints F T.toGrp),
        map F T.toGrp G i s ∈ normOneSubgroup F G ∧
          (∀ α ∈ simpleRelativeRoots i ν, t ≤ PositiveRealTorus.normCharacter F T α s) ∧
          ∃ x ∈ C, map F _ G (Standard.parabolicHom i ν ∅) p *
            map F T.toGrp G i s * (x : AdelicGroupPoints F G) = rational F G q * g

/-- Inversion changes Springer's upper-root bound into precisely the weak lower-root
bound, while reversing the order of the factors and moving rational points to the left. -/
theorem HasRightAdelicFundamentalSet.hasLeft
    (h : HasRightAdelicFundamentalSet F G T i ν) :
    HasLeftAdelicFundamentalSet F G T i ν := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨C, hC, c, hc⟩ := h
  refine ⟨Inv.inv '' C, hC.image continuous_inv, c⁻¹, ?_⟩
  intro g
  obtain ⟨q, s, p, hs, hbound, x, hx, heq⟩ := hc g⁻¹
  refine ⟨q, p⁻¹, s⁻¹, ?_, ?_, x⁻¹, ⟨x, hx, rfl⟩, ?_⟩
  · simpa only [map_inv] using (normOneSubgroup F G).inv_mem hs
  · intro α hα
    rw [map_inv]
    exact inv_le_inv' (hbound α hα)
  · have hinv := congrArg (fun z : AdelicGroupPoints F G => z⁻¹) heq
    simp only [mul_inv_rev, map_inv, Subgroup.coe_inv, inv_inv] at hinv ⊢
    rw [← hinv]
    group

/-- The split-group case of Springer's fundamental-set theorem, before conversion to an
intrinsic derived positive torus or replacement of the compact set by a supplied Iwasawa
subgroup. Splitness is expressed by requiring the setup's split torus to be maximal torus. -/
def SplitAdelicFundamentalSetStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T)
        (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        IsSiegelAlgebraicSetup F G T i ν T₀ j →
          IsMaximalTorus i → HasRightAdelicFundamentalSet F G T i ν

end Langlands.Global.AdelicSiegelFactors
