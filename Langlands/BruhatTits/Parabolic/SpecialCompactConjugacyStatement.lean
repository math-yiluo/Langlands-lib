import Langlands.BruhatTits.Iwasawa.PointProducts
import Langlands.GroupScheme.Rational.StandardParabolicClassificationStatement

/-!
# Parabolic subgroups are conjugate to standard ones under `K₀` (Renard V.5.1, Corollary)

If a subgroup `K₀` of `G(F)` satisfies `G(F) = K₀ P_∅(F) = P_∅(F) K₀` (property (1) of the
V.5.1 Theorem), then every parabolic subgroup defined over `F` is conjugate under `K₀` to a
standard parabolic subgroup.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits

open Langlands.GroupScheme

/-- Renard V.5.1, Corollary, first assertion: let `G` be a connected reductive group over a
field `F` (in the source, a nonarchimedean local field), `S` a maximal split torus with a
generic cocharacter `ν`, and `K₀` a subgroup of `G(F)` with `G(F) = P_∅(F) K₀ = K₀ P_∅(F)`,
where `P_∅` is the standard minimal parabolic of `ν`. Then every parabolic subgroup `P(ζ)` of
`G` defined over `F` is `k⁻¹ P_J k` for some `k ∈ K₀` and some set `J` of simple relative
roots. -/
def SpecialCompactParabolicConjugacyStatement : Prop :=
  ∀ (F : Type u) [Field F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
    ∀ K : Subgroup (rationalPoints G),
      Iwasawa.PointProductEqualities (standardParabolicPoints i ν ∅) K →
      ∀ zeta : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G,
        ∃ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν ∧
          ∃ k ∈ K, Dynamic.parabolic zeta = (standardParabolic i ν J).comap (G.innerIso k).hom

end Langlands.BruhatTits
