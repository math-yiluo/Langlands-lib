import Langlands.GroupScheme.Rational.RankOneCocharacterSymmetrization
import Langlands.GroupScheme.Reductive.PositiveRootTangentDimension
import Langlands.GroupScheme.Dynamic.AdjointDeterminantModelIndependence
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Signed tangent dimensions of an integral rank-one symmetrization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- Taking the actual tangent submodule commutes with inverse image under an
actual group-scheme homomorphism. -/
@[simp] theorem tangentSubmodule_comap (F : SubgroupFunctor H) (j : G ⟶ H) :
    tangentSubmodule (F.comap j) =
      (tangentSubmodule F).comap (Lie.targetMapLinear j k) := rfl

/-- An actual group-scheme isomorphism restricts to a linear equivalence from
the tangent of an inverse-image subgroup functor to the tangent of that functor. -/
def tangentSubmoduleEquivOfComap (e : G ≅ H) (F : SubgroupFunctor H) :
    tangentSubmodule (F.comap e.hom) ≃ₗ[k] tangentSubmodule F :=
  (lieKernelLinearEquiv e k).ofSubmodule' (tangentSubmodule F)

@[simp] theorem tangentSubmoduleEquivOfComap_apply (e : G ≅ H)
    (F : SubgroupFunctor H) (X : tangentSubmodule (F.comap e.hom)) :
    (tangentSubmoduleEquivOfComap e F X : Additive (lieKernel H k)) =
      Lie.targetMapLinear e.hom k X := rfl

/-- Isomorphic transport preserves the dimension of the actual tangent
submodule, with no finite-dimensionality assumption. -/
theorem finrank_tangentSubmodule_comap_iso (e : G ≅ H) (F : SubgroupFunctor H) :
    Module.finrank k (tangentSubmodule (F.comap e.hom)) =
      Module.finrank k (tangentSubmodule F) :=
  (tangentSubmoduleEquivOfComap e F).finrank_eq

end RelativeRoot

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Conjugation by the supplied normalizer point identifies the actual signed
dynamic tangent submodules of its integral symmetrization. -/
def IsConnectedReductive.normalizerSymmetrizedUnipotentTangentEquiv
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints i) (ν : cocharacterLattice T) :
    haveI := hG.isAffineHom
    RelativeRoot.tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom
        (normalizerSymmetrizedCocharacter i n ν) ≫ i)) ≃ₗ[k]
      RelativeRoot.tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom
        (-normalizerSymmetrizedCocharacter i n ν) ≫ i)) := by
  let := hG.isAffineHom
  exact (LinearEquiv.ofEq _ _ (congrArg RelativeRoot.tangentSubmodule
    (hG.unipotent_normalizerSymmetrizedCocharacter_conj i hi hT hdep n ν))).trans
      (RelativeRoot.tangentSubmoduleEquivOfComap
        (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)) _)

/-- The two actual signed dynamic tangent dimensions of the symmetrized
cocharacter are equal. The normalizer class need not be nonidentity. -/
theorem IsConnectedReductive.finrank_tangentSubmodule_unipotent_normalizerSymmetrized_eq_neg
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints i) (ν : cocharacterLattice T) :
    haveI := hG.isAffineHom
    Module.finrank k (RelativeRoot.tangentSubmodule
      (Dynamic.unipotent (CommGroupScheme.groupHom
        (normalizerSymmetrizedCocharacter i n ν) ≫ i))) =
      Module.finrank k (RelativeRoot.tangentSubmodule
        (Dynamic.unipotent (CommGroupScheme.groupHom
          (-normalizerSymmetrizedCocharacter i n ν) ≫ i))) := by
  let := hG.isAffineHom
  exact (hG.normalizerSymmetrizedUnipotentTangentEquiv i hi hT hdep n ν).finrank_eq

/-- A bound for the positive symmetrized tangent submodule gives uniqueness of
positive roots for the original cocharacter, provided the supplied Weyl class
is nonidentity. -/
theorem IsConnectedReductive.positive_roots_eq_of_normalizerSymmetrized_unipotent_finrank_le_one
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints i) (hn : (QuotientGroup.mk n : relativeWeylGroup i) ≠ 1)
    (ν : cocharacterLattice T)
    (hdim : haveI := hG.isAffineHom
      Module.finrank k (RelativeRoot.tangentSubmodule
        (Dynamic.unipotent (CommGroupScheme.groupHom
          (normalizerSymmetrizedCocharacter i n ν) ≫ i))) ≤ 1) :
    haveI := hG.isAffineHom
    ∀ {α β : characterLattice T}, α ∈ roots i → β ∈ roots i →
      0 < latticePairing T α ν → 0 < latticePairing T β ν → α = β := by
  let := hG.isAffineHom
  let := hG.smooth
  intro α β hα hβ hαpos hβpos
  apply RelativeRoot.positive_roots_eq_of_tangentSubmodule_unipotent_finrank_le_one
    hT i (normalizerSymmetrizedCocharacter i n ν) hdim hα hβ
  · rw [hG.latticePairing_normalizerSymmetrizedCocharacter i hi hT hdep n hn α ν hα]
    omega
  · rw [hG.latticePairing_normalizerSymmetrizedCocharacter i hi hT hdep n hn β ν hβ]
    omega

/-- A bound on either signed tangent submodule of the integral symmetrization
implies uniqueness of positive roots for the original cocharacter. The bound
and a nonidentity normalizer class remain explicit inputs. -/
theorem IsConnectedReductive.positive_roots_eq_of_signed_normalizerSymmetrized_unipotent_finrank_le_one
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints i) (hn : (QuotientGroup.mk n : relativeWeylGroup i) ≠ 1)
    (ν : cocharacterLattice T)
    (hdim : haveI := hG.isAffineHom
      Module.finrank k (RelativeRoot.tangentSubmodule
        (Dynamic.unipotent (CommGroupScheme.groupHom
          (normalizerSymmetrizedCocharacter i n ν) ≫ i))) ≤ 1 ∨
      Module.finrank k (RelativeRoot.tangentSubmodule
        (Dynamic.unipotent (CommGroupScheme.groupHom
          (-normalizerSymmetrizedCocharacter i n ν) ≫ i))) ≤ 1) :
    haveI := hG.isAffineHom
    ∀ {α β : characterLattice T}, α ∈ roots i → β ∈ roots i →
      0 < latticePairing T α ν → 0 < latticePairing T β ν → α = β := by
  let := hG.isAffineHom
  apply hG.positive_roots_eq_of_normalizerSymmetrized_unipotent_finrank_le_one
    i hi hT hdep n hn ν
  rcases hdim with hdim | hdim
  · exact hdim
  · rw [hG.finrank_tangentSubmodule_unipotent_normalizerSymmetrized_eq_neg
      i hi hT hdep n ν]
    exact hdim

end Langlands.GroupScheme
