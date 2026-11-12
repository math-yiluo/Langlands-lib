import Langlands.Representation.Aubert.General.RationalInducedWeylConjugacyTarget
import Langlands.Representation.Aubert.General.RationalLeviCharacterDensity
import Langlands.Representation.Aubert.General.ConjugateInduction

/-! # Generic isomorphism of normalized inductions sharing a standard Levi -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Plancherel
open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  (j : S.toGrp ⟶ H) (ξ : cocharacterLattice S) (K : Finset (SimpleRoot j ξ))

local instance instRationalSameLeviGenericIso1 : IsAffine H.X.left :=
  isAffine_of_isAffineHom H.X.hom
local instance instRationalSameLeviGenericIso2 :
    IsClosedImmersion (Standard.leviHom j ξ (rootSet j ξ K)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom j ξ (rootSet j ξ K)
local instance instRationalSameLeviGenericIso3 :
    IsAffine (Standard.leviScheme j ξ (rootSet j ξ K)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom j ξ (rootSet j ξ K)).hom.hom.left

/-- Generic isomorphism of the normalized inductions from the standard parabolic
`P_J` and from the actual conjugate parabolic `g P_I g⁻¹`, which share the
literal Levi `L_J`, of the unramified twists of an irreducible admissible
representation of `L_J`, on a nonzero principal open locus of unramified
characters. No proof is supplied. -/
def RationalSameLeviGenericInductionIsoStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (I J : Finset (SimpleRoot i ν)) (g : RationalPoint k G.X)
      (hIJ : ∀ x : RationalPoint k G.X, x ∈ levi i ν J ↔ g⁻¹ * x * g ∈ levi i ν I)
      (hLJ : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν J)))
      (σ : SmoothRep.{0, u, v} ℂ (levi i ν J)),
      σ.IsIrreducible → σ.IsAdmissible →
      ∃ p : MvPolynomial
          (Fin (rationalImageRank (Standard.leviScheme i ν (rootSet i ν J)))) ℂ,
        p ≠ 0 ∧ ∀ χ ∈ leviUnramifiedPrincipalOpen i ν J hLJ p,
          Nonempty
            ((normalizedInductionFunctor
                (isSemidirectDecomposition_of_standardCocharacterStatement
                  i ν hStandard hG hi hν J) (hU J)).obj
                (σ.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ χ)) ≅
              (conjugateInductionFunctor
                (isSemidirectDecomposition_of_standardCocharacterStatement
                  i ν hStandard hG hi hν I) g hIJ (hU I)).obj
                (σ.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ χ)))

end Langlands.Aubert.General.RationalPointFamily
