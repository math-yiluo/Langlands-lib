import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Langlands.Representation.Jacquet.CompressedImageLift

/-! # The single-image canonical Jacquet section on actual standard chambers -/

noncomputable section

universe uF uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Jacquet

/-- Renard VI.6.1, (VI.6.1.2), the subsequent single-image isomorphism and
independence Proposition, on actual standard parabolics. The Chapter V
algebraic and compact-subgroup inputs are explicit. -/
def StandardCanonicalSectionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (S A : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
      (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
      (_hν : IsGenericCocharacter i ν) (J : Set (characterLattice S))
      (_hJ : J ⊆ simpleRelativeRoots i ν)
      (_hstandard : ∃ zeta, IsStandardCocharacter i ν J zeta)
      (q : A.toGrp ⟶ S.toGrp)
      (_hA : IsCompatibleStandardSplitComponent i ν J A q),
      let N := standardUnipotentPoints i ν J
      let M := standardLeviPoints i ν J
      ∀ (hMN : M ≤ Subgroup.normalizer N)
        (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
        (_hBasis : StandardParabolicBasisMember i ν J q K.toSubgroup)
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ),
        let j := fixedJacquetMap ρ N M hMN K.toSubgroup
        ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
          (∃ t : rationalPoints G, t ∈ standardComponentCAepsilon i ν J q ε) ∧
          ∃ s : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype) →ₗ[ℂ]
              fixedVectors ρ K.toSubgroup,
            j.comp s = LinearMap.id ∧
            ∀ t ∈ standardComponentCAepsilon i ν J q ε,
              let C := compressedAction ρ hρ.1 K hK t
              LinearMap.ker j ≤ LinearMap.ker C ∧
              LinearMap.ker C = LinearMap.ker j ∧
              IsCompl (LinearMap.ker C) (LinearMap.range C) ∧
              Function.Bijective (compressedImageJacquetMap ρ hρ.1 K hK t N M hMN) ∧
              LinearMap.range C = stableImage ρ hρ.1 K hK t ∧
              powerKernelSup ρ hρ.1 K hK t = LinearMap.ker j ∧
              LinearMap.range s = LinearMap.range C ∧
              ∀ hb : Function.Bijective
                  (compressedImageJacquetMap ρ hρ.1 K hK t N M hMN),
                compressedImageLift ρ hρ.1 K hK t N M hMN hb = s

end Langlands.Jacquet
