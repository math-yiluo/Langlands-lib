import Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement
import Langlands.Representation.Aubert.General.RationalPointFamily

/-! # Factorization into elementary Weyl elements (Renard VI.5.4, Lemma; BZ77, Lemma 2.17)

For standard Levi subgroups `L` and `M` of a connected reductive group over a nonarchimedean
local field, every `w ∈ W(L, M) = {w ∈ W_G | w · L = M}` is a product `w = w_m ⋯ w_1` of
elementary elements `w_j ∈ W(L_{j-1}, L_j)` along a chain `L = L_0, …, L_m = M` of standard
Levi subgroups. Here `w ∈ W(L, M)` is elementary when some standard parabolic `T = SV`
contains the standard parabolics of `L` and `M`, `w ∈ W_S`, and `l_S(M) = 2`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology

/-- Renard VI.5.4, Lemma (Bernstein–Zelevinsky 1977, Lemma 2.17), for the standard Levi
subgroups `L_I` (rational points) of a connected reductive `G` over a nonarchimedean local
field, with maximal split torus `i` and generic cocharacter `ν`. Write
`W_G = relativeWeylGroup i = N(k)/Z(k)`, `W_I = standardRelativeWeylGroup i ν I`, and
`w · H = n H n⁻¹` for a representative `n ∈ N(k)` of `w`.

* `W(L, M)` is the set of `w` having a representative `n` with `n L n⁻¹ = M`.
* For standard `S ⊇ M`, `l_S(M)` is the number of left cosets `v W_M` of the elements
  `v ∈ W_S` with `v · M` a standard Levi subgroup of `S` (Renard V.4.4, computed in `S`).
* `w ∈ W(L, M)` is elementary when some standard parabolic `P_S` contains `P_L` and `P_M`,
  `w ∈ W_S`, and `l_S(M) = 2`.

For standard Levis `L ≠ G` and `M`, every `w ∈ W(L, M)` admits a chain of index sets
`L = L_0, …, L_m = M` and elementary `w_j ∈ W(L_{j-1}, L_j)` with `w = w_m ⋯ w_1`. -/
def StandardWeylElementaryChainStatement : Prop :=
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
    let WLM : Finset (SimpleRoot i ν) → Finset (SimpleRoot i ν) →
        Set (relativeWeylGroup i) := fun IL IM =>
      {w | ∃ n : normalizerPoints i, (QuotientGroup.mk n : relativeWeylGroup i) = w ∧
        (levi i ν IL).map (conj n) = levi i ν IM}
    let ell : Finset (SimpleRoot i ν) → Finset (SimpleRoot i ν) → ℕ := fun IS IM =>
      Nat.card ((QuotientGroup.mk : relativeWeylGroup i → relativeWeylGroup i ⧸ WS IM) ''
        {v | v ∈ WS IS ∧ ∃ K : Finset (SimpleRoot i ν), K ⊆ IS ∧ v ∈ WLM IM K})
    let IsElementary : Finset (SimpleRoot i ν) → Finset (SimpleRoot i ν) →
        relativeWeylGroup i → Prop := fun IL IM w =>
      w ∈ WLM IL IM ∧ ∃ IS : Finset (SimpleRoot i ν),
        parabolic i ν IL ≤ parabolic i ν IS ∧ parabolic i ν IM ≤ parabolic i ν IS ∧
          w ∈ WS IS ∧ ell IS IM = 2
    ∀ IL IM : Finset (SimpleRoot i ν), (∃ a : SimpleRoot i ν, a ∉ IL) →
      ∀ w ∈ WLM IL IM,
        ∃ (m : ℕ) (Ls : Fin (m + 1) → Finset (SimpleRoot i ν)) (ws : Fin m → relativeWeylGroup i),
          Ls 0 = IL ∧ Ls (Fin.last m) = IM ∧
            (∀ j : Fin m, IsElementary (Ls j.castSucc) (Ls j.succ) (ws j)) ∧
            w = ((List.ofFn ws).reverse).prod

end Langlands.GroupScheme
