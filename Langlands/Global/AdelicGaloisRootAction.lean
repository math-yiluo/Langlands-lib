import Langlands.Global.AdelicGaloisBorelTwisting

/-! # Galois action on the simple roots of a split Borel pair (Lemma Q)

This module states `SplitBorelGaloisRootActionStatement`, the purely algebraic input of the
proof of `GaloisBorelTwistingStatement`: for a maximal `F`-torus split over a finite Galois
extension `L` and a generic cocharacter, every `σ ∈ Gal(L/F)` is realized by a rational point
`m σ` such that `σ` followed by conjugation by `(m σ)⁻¹` permutes the simple roots, carries the
maximal standard parabolics accordingly, and these permutations form an action.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section RootAction

variable (F L : Type u) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance : IsAffineHom (AffineWeil.unitBaseChange F L G).X.hom :=
  isAffineHom_of_isAffine _


/-- The Galois root map `a σ : χ ↦ (τ σ)⁻¹ ≫ σ χ` on the characters of `T₀_L`: the Galois
translate `σ χ` (`characterLattice.galoisRepresentation`) followed by `characterAut (τ σ)`. -/
def galoisRootMap (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
    (τ : (L ≃ₐ[F] L) → ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀ ≅
      (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)) (σ : L ≃ₐ[F] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)) :
    characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀) :=
  characterAut (τ σ) (characterLattice.galoisRepresentation F L T₀ σ χ)

/-- The Galois-root-action conclusion for a torus `T₀` over `F`, the inclusion `i` of its
base change in `G_L`, a cocharacter `ν`, rational points `m σ` and automorphisms `τ σ` of
`T₀_L`: `(m σ)⁻¹` normalizes `i` through `τ σ`; the map `a σ = galoisRootMap τ σ` sends
simple roots to simple roots; for every set `J` of simple roots, the canonical Galois translate
of the standard parabolic for `J` is the `m σ`-conjugate of the one for `a σ '' J`; and `a` is
an action of `Gal(L/F)` on the simple roots. -/
def IsGaloisRootAction (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp ⟶
      AffineWeil.unitBaseChange F L G)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀))
    (m : (L ≃ₐ[F] L) → rationalPoints (AffineWeil.unitBaseChange F L G))
    (τ : (L ≃ₐ[F] L) → ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀ ≅
      (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)) : Prop :=
  (∀ σ, IsNormalizingPoint i (m σ)⁻¹ (τ σ)) ∧
  (∀ σ, ∀ β ∈ simpleRelativeRoots i ν, galoisRootMap F L T₀ τ σ β ∈ simpleRelativeRoots i ν) ∧
  (∀ σ, ∀ J ⊆ simpleRelativeRoots i ν,
    SubgroupFunctor.range (radicalGaloisHom (Standard.parabolicHom i ν J) σ) =
      SubgroupFunctor.range
        (Standard.parabolicHom i ν (galoisRootMap F L T₀ τ σ '' J) ≫
          ((AffineWeil.unitBaseChange F L G).innerIso (m σ)).hom)) ∧
  (∀ β ∈ simpleRelativeRoots i ν, galoisRootMap F L T₀ τ 1 β = β) ∧
  ∀ σ σ' : L ≃ₐ[F] L, ∀ β ∈ simpleRelativeRoots i ν,
    galoisRootMap F L T₀ τ (σ * σ') β =
      galoisRootMap F L T₀ τ σ (galoisRootMap F L T₀ τ σ' β)

end RootAction

/-- Lemma Q: a maximal torus over `F` that splits over a finite Galois extension `L`, with a
generic cocharacter of its base change, admits a Galois root action. -/
def SplitBorelGaloisRootActionStatement : Prop :=
  ∀ (F L : Type u) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (i₀ : T₀.toGrp ⟶ G),
    IsConnectedReductive G → IsMaximalTorus i₀ →
      IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp →
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : IsAffineHom (AffineWeil.unitBaseChange F L G).X.hom := isAffineHom_of_isAffine _
      ∀ ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀),
        IsGenericCocharacter ((GroupScheme.baseChange (algebraBaseMap F L)).map i₀) ν →
        ∃ (m : (L ≃ₐ[F] L) → rationalPoints (AffineWeil.unitBaseChange F L G))
          (τ : (L ≃ₐ[F] L) → ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀ ≅
            (CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)),
          IsGaloisRootAction F L G T₀ ((GroupScheme.baseChange (algebraBaseMap F L)).map i₀) ν m τ

end Langlands.Global.AdelicGaloisUnit
