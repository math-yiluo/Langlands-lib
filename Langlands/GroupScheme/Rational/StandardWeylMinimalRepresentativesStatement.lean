import Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement
import Langlands.Representation.Aubert.General.RationalPointFamily

/-! # Minimal representatives of standard Weyl double cosets (Renard V.4.6, Lemma)

For standard parabolic subgroups `P = MN` and `Q = LU` of a connected reductive group over a
nonarchimedean local field, with Weyl subgroups `W_M` and `W_L` of the relative Weyl group
`W_G = N(k)/Z(k)`, let `W^{L,M}` be the set of `w ∈ W_G` with `w · (L ∩ P_∅) ⊆ P_∅` and
`w⁻¹ · (M ∩ P_∅) ⊆ P_∅`. Then (i) each double coset `W_M w W_L` contains exactly one element
of `W^{L,M}`, the element of minimal length; (ii) for `w ∈ W^{L,M}`, `M ∩ w·Q` and
`w⁻¹·P ∩ L` are standard parabolic subgroups of `M` and `L` with the expected Levi factors
and unipotent radicals, and the four intersection decompositions hold; (iii)
`W^{L,M} ∩ W(L, M) ≃ W_M \ W(L, M) / W_L ≃ W(L, M)/W_L`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology

/-- Renard V.4.6, Lemma, for the standard parabolic subgroups `P_I = L_I U_I` (rational
points) of a connected reductive `G` over a nonarchimedean local field, with maximal split
torus `i` and generic cocharacter `ν`. Write `W_G = relativeWeylGroup i = N(k)/Z(k)`,
`W_I = standardRelativeWeylGroup i ν I`, `w · H = n H n⁻¹` for a representative `n ∈ N(k)` of
`w`, and `P_∅ = parabolic i ν ∅`. For index sets `IL` (of `Q = LU`) and `IM` (of `P = MN`),
`W^{L,M}` is the set of `w` having a representative `n` with `n (L ∩ P_∅) n⁻¹ ⊆ P_∅` and
`n⁻¹ (M ∩ P_∅) n ⊆ P_∅`, and `W(L, M)` the set of `w` with `w · L = M`. Then:

* (i) every double coset `W_M w W_L` contains exactly one element of `W^{L,M}`, and for every
  Coxeter system on `W_G` realizing the relative root action (published
  `IsRelativeWeylCoxeterRealization`) it is strictly shorter than every other element of its
  double coset;
* (ii) for every representative `n` of an element of `W^{L,M}`: `M ∩ nQn⁻¹ = M ∩ P_K`,
  `M ∩ nLn⁻¹ = L_K` and `M ∩ nUn⁻¹ = M ∩ U_K` for some `K ⊆ IM`; `L ∩ n⁻¹Pn = L ∩ P_{K'}`,
  `L ∩ n⁻¹Mn = L_{K'}` and `L ∩ n⁻¹Nn = L ∩ U_{K'}` for some `K' ⊆ IL`; and
  `P ∩ nQn⁻¹ = (P ∩ nLn⁻¹)(P ∩ nUn⁻¹)`, `Q ∩ n⁻¹Pn = (Q ∩ n⁻¹Mn)(Q ∩ n⁻¹Nn)`,
  `N ∩ nQn⁻¹ = (N ∩ nLn⁻¹)(N ∩ nUn⁻¹)`, `U ∩ n⁻¹Pn = (U ∩ n⁻¹Mn)(U ∩ n⁻¹Nn)`;
* (iii) for every `w ∈ W(L, M)`, exactly one element of `W^{L,M} ∩ W(L, M)` lies in `w W_L`,
  and `W_M w ⊆ w W_L`. -/
def StandardWeylMinimalRepresentativesStatement : Prop :=
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
    let P0 := parabolic i ν ∅
    let Wmin : Finset (SimpleRoot i ν) → Finset (SimpleRoot i ν) →
        Set (relativeWeylGroup i) := fun IL IM =>
      {w | ∃ n : normalizerPoints i, (QuotientGroup.mk n : relativeWeylGroup i) = w ∧
        (levi i ν IL ⊓ P0).map (conj n) ≤ P0 ∧ (levi i ν IM ⊓ P0).map (conj n⁻¹) ≤ P0}
    let WLM : Finset (SimpleRoot i ν) → Finset (SimpleRoot i ν) →
        Set (relativeWeylGroup i) := fun IL IM =>
      {w | ∃ n : normalizerPoints i, (QuotientGroup.mk n : relativeWeylGroup i) = w ∧
        (levi i ν IL).map (conj n) = levi i ν IM}
    ∀ IL IM : Finset (SimpleRoot i ν),
      -- (i)
      (∀ w : relativeWeylGroup i,
        ∃! v, v ∈ Wmin IL IM ∧ ∃ a ∈ WS IM, ∃ b ∈ WS IL, v = a * w * b) ∧
      (∀ (C : CoxeterMatrix (SimpleRoot i ν)) (cs : CoxeterSystem C (relativeWeylGroup i)),
        IsRelativeWeylCoxeterRealization i ν cs →
          ∀ v ∈ Wmin IL IM, ∀ a ∈ WS IM, ∀ b ∈ WS IL,
            a * v * b ≠ v → cs.length v < cs.length (a * v * b)) ∧
      -- (ii)
      (∀ n : normalizerPoints i, (QuotientGroup.mk n : relativeWeylGroup i) ∈ Wmin IL IM →
        (∃ K : Finset (SimpleRoot i ν), K ⊆ IM ∧
          levi i ν IM ⊓ (parabolic i ν IL).map (conj n) = levi i ν IM ⊓ parabolic i ν K ∧
          levi i ν IM ⊓ (levi i ν IL).map (conj n) = levi i ν K ∧
          levi i ν IM ⊓ (unipotent i ν IL).map (conj n) =
            levi i ν IM ⊓ unipotent i ν K) ∧
        (∃ K' : Finset (SimpleRoot i ν), K' ⊆ IL ∧
          levi i ν IL ⊓ (parabolic i ν IM).map (conj n⁻¹) = levi i ν IL ⊓ parabolic i ν K' ∧
          levi i ν IL ⊓ (levi i ν IM).map (conj n⁻¹) = levi i ν K' ∧
          levi i ν IL ⊓ (unipotent i ν IM).map (conj n⁻¹) =
            levi i ν IL ⊓ unipotent i ν K') ∧
        ((parabolic i ν IM ⊓ (parabolic i ν IL).map (conj n) :
            Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) =
          ((parabolic i ν IM ⊓ (levi i ν IL).map (conj n) : Subgroup (RationalPoint k G.X)) :
            Set (RationalPoint k G.X)) *
          ((parabolic i ν IM ⊓ (unipotent i ν IL).map (conj n) :
            Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) ∧
        ((parabolic i ν IL ⊓ (parabolic i ν IM).map (conj n⁻¹) :
            Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) =
          ((parabolic i ν IL ⊓ (levi i ν IM).map (conj n⁻¹) :
            Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) *
          ((parabolic i ν IL ⊓ (unipotent i ν IM).map (conj n⁻¹) :
            Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) ∧
        ((unipotent i ν IM ⊓ (parabolic i ν IL).map (conj n) :
            Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) =
          ((unipotent i ν IM ⊓ (levi i ν IL).map (conj n) :
            Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) *
          ((unipotent i ν IM ⊓ (unipotent i ν IL).map (conj n) :
            Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) ∧
        ((unipotent i ν IL ⊓ (parabolic i ν IM).map (conj n⁻¹) :
            Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) =
          ((unipotent i ν IL ⊓ (levi i ν IM).map (conj n⁻¹) :
            Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) *
          ((unipotent i ν IL ⊓ (unipotent i ν IM).map (conj n⁻¹) :
            Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X))) ∧
      -- (iii)
      ∀ w ∈ WLM IL IM,
        (∃! v, v ∈ Wmin IL IM ∧ v ∈ WLM IL IM ∧ ∃ b ∈ WS IL, v = w * b) ∧
        ∀ a ∈ WS IM, ∃ b ∈ WS IL, a * w = w * b

end Langlands.GroupScheme
