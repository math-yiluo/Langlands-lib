import Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement
import Langlands.Representation.Aubert.General.RationalPointFamily

/-! # Weyl groups of standard Levi subgroups (Renard V.4.3.3 and V.4.8)

For a standard Levi subgroup `M` of a connected reductive group over a nonarchimedean local
field: (V.4.3.3) the map `W(M, M)/W_M → N_G(M)/M` is a bijection; (V.4.8) `M` is maximal
exactly when its index set is `Δ_∅ ∖ {α}`, exactly when `l(M) = 2`, and then a representative
`w` of the nontrivial class of `W(M, *)/W_M` sends the standard parabolic `P ⊇ M` to the
parabolic opposite to the standard parabolic `P' ⊇ w · M`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology

/-- Renard V.4.3, (V.4.3.3), for the standard Levi subgroups `M = L_I` (rational points) of a
connected reductive `G` over a nonarchimedean local field, with maximal split torus `i` and
generic cocharacter `ν`. Write `W_G = relativeWeylGroup i = N(k)/Z(k)`,
`W_M = standardRelativeWeylGroup i ν I` and `W(M, M)` for the set of `w ∈ W_G` having a
representative `n ∈ N(k)` with `n M n⁻¹ = M`. The map `W(M, M)/W_M → N_{G(k)}(M)/M`,
`[n] ↦ [n]`, is a bijection:

* a representative `n ∈ N(k)` has class in `W_M` exactly when `n ∈ M`;
* every `g ∈ G(k)` with `g M g⁻¹ = M` lies in `n M` for some `n ∈ N(k)` with
  `n M n⁻¹ = M`. -/
def StandardLeviNormalizerQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
    ∀ I : Finset (SimpleRoot i ν),
      (∀ n : normalizerPoints i,
        (QuotientGroup.mk n : relativeWeylGroup i) ∈
            standardRelativeWeylGroup i ν (rootSet i ν I) ↔
          (n : RationalPoint k G.X) ∈ levi i ν I) ∧
      ∀ g : RationalPoint k G.X,
        (levi i ν I).map
            (MulAut.conj g : RationalPoint k G.X →* RationalPoint k G.X) = levi i ν I →
        ∃ n : normalizerPoints i,
          (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
              RationalPoint k G.X →* RationalPoint k G.X) = levi i ν I ∧
            (n : RationalPoint k G.X)⁻¹ * g ∈ levi i ν I

/-- Renard V.4.8, for the standard parabolic subgroups `P_I = L_I U_I` (rational points) of a
connected reductive `G` over a nonarchimedean local field, with maximal split torus `i` and
generic cocharacter `ν`. Write `W_G = relativeWeylGroup i`, `W_I = standardRelativeWeylGroup
i ν I`, `W(M, *)` for the set of `w` having a representative `n` with `n L_I n⁻¹ = L_J` for
some `J`, and `l(L_I)` for the number of left cosets `w W_I` of elements of `W(L_I, *)`
(Renard V.4.4). Call `P_I` maximal when it is a proper subgroup of `G(k)` and every standard
parabolic strictly containing it is `G(k)`. Then for every index set `I`:

* `P_I` is maximal exactly when `I = Δ_∅ ∖ {α}` for a simple root `α`;
* `P_I` is maximal exactly when `l(L_I) = 2`;
* if `P_I` is maximal, `n` represents an element of `W(L_I, *)` outside `W_I` and
  `n L_I n⁻¹ = L_J`, then `n P_I n⁻¹` is the parabolic opposite to `P_J`, the dynamic
  parabolic `P(-ζ)(k)` for every standard cocharacter `ζ` of `J`. -/
def StandardMaximalLeviWeylStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
    let conj : normalizerPoints i → (RationalPoint k G.X →* RationalPoint k G.X) := fun n =>
      (MulAut.conj (n : RationalPoint k G.X) : RationalPoint k G.X →* RationalPoint k G.X)
    let WS : Finset (SimpleRoot i ν) → Subgroup (relativeWeylGroup i) := fun I =>
      standardRelativeWeylGroup i ν (rootSet i ν I)
    let WLstar : Finset (SimpleRoot i ν) → Set (relativeWeylGroup i) := fun I =>
      {w | ∃ n : normalizerPoints i, (QuotientGroup.mk n : relativeWeylGroup i) = w ∧
        ∃ J : Finset (SimpleRoot i ν), (levi i ν I).map (conj n) = levi i ν J}
    let ell : Finset (SimpleRoot i ν) → ℕ := fun I =>
      Nat.card ((QuotientGroup.mk : relativeWeylGroup i → relativeWeylGroup i ⧸ WS I) ''
        WLstar I)
    let IsMaximal : Finset (SimpleRoot i ν) → Prop := fun I =>
      parabolic i ν I ≠ ⊤ ∧
        ∀ J : Finset (SimpleRoot i ν), parabolic i ν I < parabolic i ν J → parabolic i ν J = ⊤
    ∀ I : Finset (SimpleRoot i ν),
      (IsMaximal I ↔ ∃ a : SimpleRoot i ν, ∀ b : SimpleRoot i ν, b ∈ I ↔ b ≠ a) ∧
      (IsMaximal I ↔ ell I = 2) ∧
      (IsMaximal I →
        ∀ (n : normalizerPoints i) (J : Finset (SimpleRoot i ν)),
          (QuotientGroup.mk n : relativeWeylGroup i) ∉ WS I →
          (levi i ν I).map (conj n) = levi i ν J →
          ∀ ζ : cocharacterLattice T, IsStandardCocharacter i ν (rootSet i ν J) ζ →
            (parabolic i ν I).map (conj n) =
              (Dynamic.parabolic (CommGroupScheme.groupHom (-ζ) ≫ i)).carrier
                (Over.mk (𝟙 _)))

end Langlands.GroupScheme
