import Langlands.Representation.LanglandsClassification.LanglandsTriplet
import Langlands.GroupScheme.Rational.SubgroupRelativeRoots

/-! # Roots positive on a coroot chamber are the roots in the unipotent radical (Renard V.3.17)

For a maximal split torus `A_∅` of a connected reductive group with a generic cocharacter
(a minimal parabolic `P_∅`), integral reflection data (a coroot for every relative root) and a
standard parabolic `P = MN` with simple-root index `J`: for every `μ` in the open coroot
chamber `^G_P[𝔞*]^+` of `P`, lifted to `𝔞*_∅`, the relative roots `γ` with `⟨μ, γ̌⟩ > 0` are
exactly the roots of `A_∅` in `N`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace

/-- Renard V.3.17, Lemma. Let `G` be connected reductive over a field `k`, `i : T → G` a
maximal split torus, `ν` a generic cocharacter of `T` (fixing the positive and simple relative
roots and the standard parabolic subgroups), `D` integral reflection data supplying a coroot
`γ̌ = D.coroot γ` for every relative root `γ`, and `J` a set of simple roots (the standard
parabolic `P = MN` of `J`). For every `μ` in the open coroot chamber of `P`, taken in the real
character space of `T` itself (the published `restrictedCorootChamber` along the identity of
`T`: `⟨μ, α̌⟩ = 0` for `α ∈ J`, `⟨μ, α̌⟩ > 0` for the other simple roots), a relative root `γ`
satisfies `⟨μ, γ̌⟩ > 0` exactly when `γ` is a root of `T` in the standard unipotent subgroup
`N = standardUnipotent i ν J`, that is, a nonzero weight of `T` on its Lie algebra. -/
def CorootChamberUnipotentRootsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
    ∀ (D : RelativeRootReflectionData i) (J : Set (characterLattice T)),
      J ⊆ simpleRelativeRoots i ν →
      ∀ x ∈ restrictedCorootChamber i ν J (𝟙 T) D,
        ∀ r : relativeRoots i,
          0 < pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot r) ↔
            r.1 ∈ RelativeRoot.subgroupRelativeRoots i (standardUnipotent i ν J)

end Langlands.GroupScheme
