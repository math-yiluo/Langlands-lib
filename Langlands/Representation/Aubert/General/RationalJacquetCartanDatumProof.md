# Jacquet–Cartan data on the rational points of reductive groups: proof

Module `Langlands.Representation.Aubert.General.RationalJacquetCartanDatumProof`.

The theorem `Langlands.Aubert.General.rationalPointsJacquetCartanDatum` proves
exactly `RationalPointsJacquetCartanDatumStatement.{u}` (module
`Langlands.Representation.Aubert.General.JacquetCartanDatumStatement`) at an
arbitrary universe `u`. [Statement](JacquetCartanDatumStatement.md)

```
theorem rationalPointsJacquetCartanDatum : RationalPointsJacquetCartanDatumStatement.{u}
```

## What is proved

For every field `F : Type u` with `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`, every group scheme
`G : GroupScheme (Spec (CommRingCat.of F))` and every
`hG : IsConnectedReductive G`, the rational points `RationalPoint F G.X`, with
the topology `rationalPointTopology F G.X` pinned inside the statement, carry a
`Langlands.JacquetCartanDatum.{u, u}`. The index type and the wall types lie in
the universe `u` of `F`.

The scope is the full scope of the statement. It covers equal and mixed
characteristic and every residue characteristic. It covers every connected
reductive `G`: nonsplit and non-quasi-split groups, and anisotropic groups,
where the set of simple relative roots is empty. The theorem has no hypotheses,
and its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The Lean term is one application:

```
rationalPointsJacquetCartanDatum_of
  Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence
  Langlands.GroupScheme.standardCocharacter
  Langlands.GroupScheme.standardParabolicOrder
```

- `rationalPointsJacquetCartanDatum_of` (module
  `Langlands.Representation.Aubert.General.RationalJacquetCartanDatum`) derives
  the target from three Prop-valued statements: the joint special compact basis
  existence statement, the standard cocharacter statement and the standard
  parabolic order statement. [Reduction](RationalJacquetCartanDatum.md)
- `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
  (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves
  `JointSpecialCompactBasisExistenceStatement.{u}`. Take a maximal split torus
  `i : S → G` and a generic cocharacter `ν`. The theorem gives one apartment
  datum `D`, one special vertex `x`, and one represented torus centralizer
  `j : Z → G` with `s ≫ j = i` and the restriction-evaluation bijection `h`.
  At these witnesses, with `K₀ = D.specialCompactSubgroup x`, it proves the
  following: the special compact properties, the ambient and Levi Iwasawa
  products, the ambient and standard-Levi Cartan comparisons, and the
  simultaneous standard basis (Renard V.5.1–V.5.2).
  [Joint basis](../../../BruhatTits/SpecialCompact/JointBasisProof.md)
- `Langlands.GroupScheme.standardCocharacter` (module
  `Langlands.GroupScheme.Rational.StandardCocharacterProof`) proves
  `StandardCocharacterStatement.{u}`. Every set of simple relative roots has a
  standard cocharacter, and the standard parabolic, Levi and unipotent
  subgroups agree with the dynamic subgroups of that cocharacter.
- `Langlands.GroupScheme.standardParabolicOrder` (module
  `Langlands.GroupScheme.Rational.StandardParabolicOrderProof`) proves
  `StandardParabolicOrderStatement.{u}`. For sets `J`, `K` of simple relative
  roots, `J ⊆ K` holds exactly when `P_J ≤ P_K`, and `J ⊆ K` gives
  `M_J ≤ M_K` and the reversed inclusion `N_K ≤ N_J` of unipotent radicals.
  The map `J ↦ P_J` is injective.

## The datum that the proof constructs

The proof of `rationalPointsJacquetCartanDatum_of` does the following:

1. It chooses a maximal split torus `i : S → G` with a generic cocharacter `ν`.
2. It applies the joint statement to get `D`, `x`, `Z`, `j`, `s` and `h` with
   their properties.
3. It takes a finite lattice transversal `F₀ ⊆ Z(F)`
   (`IsFiniteLatticeTransversal`): a finite set with exactly one element in
   each class of the quotient of the valuation lattice of `Z(F)` by the image
   of the valuation lattice of the split torus.
4. It forms `rationalStandardParabolicSystem`, a `StandardParabolicSystem` of
   `G(F)`.
5. It converts that system into a datum with
   `StandardParabolicSystem.nonempty_jacquetCartanDatum` (module
   `Langlands.Representation.Aubert.General.JacquetCartanAssembly`).

The resulting datum has the following components:

- **Indices.** The indices are the finite sets `I` of simple relative roots
  `SimpleRoot i ν`, with rank `|I|`. The Levi and unipotent subgroups are the
  standard Levi `M_I(F)` and the unipotent radical `N_I(F)` of the standard
  parabolic `P_I`. The top index contains every simple root, so `N_top` is
  trivial.
- **Iwasawa set.** The Iwasawa set is `K₀`, from `G(F) = P_∅(F) K₀`
  (Renard V.5.1 (1)).
- **Walls.** The walls of `I` are all proper subsets `J ⊊ I`, with wall
  subgroup `N_J(F) ∩ M_I(F)` and descent index `J`. The descent uses
  `N_J = (N_J ∩ M_I) N_I`.
- **Cartan decomposition.** `M_I(F) = (K₀ ∩ M_I(F)) Λ (K₀ ∩ M_I(F))`. Here
  `Λ = rationalCartanSet i ν j s h F₀ I` is a countable set. It is the image
  under `j` of the dominant intersection `(C₀ F₀) ∩ Z_dom(M_I)`, where `C₀ F₀`
  is the full representative set of Renard V.3.23 and `Z_dom(M_I)` is the
  part of `Z(F)` that is dominant for the positive roots of `M_I`. This
  intersection is Renard's `C̃⁺` of V.3.23, taken in each standard Levi as in
  V.5.1 (4), (5). Renard then makes an additional choice of the finite set so
  that `C̃⁺` equals the product `C⁺ F` of positive lattice points and
  representatives. The datum here makes no such choice: `F₀` is any finite
  lattice transversal, and `Λ` is the intersection itself, which need not equal
  that product.
- **Contraction.** The contraction is the dichotomy of the proof of Renard
  VI.2.1 `a) ⇒ b)`. It is obtained from the lattice model of the Cartan
  elements (`isCartanLatticeModel_rational`, and
  `IsCartanLatticeModel.hasWallContraction`).

Renard and the Markdown of the target statement take as walls only the sets
`I ∖ {α}` for `α ∈ I`. The datum built here takes every proper subset of `I` as
a wall. The statement only asks that some datum exist, so this larger family of
walls is admissible. With the larger family, the contraction dichotomy follows
from the lattice data.

## Provenance

The structure follows D. Renard, *Représentations des groupes réductifs
p-adiques* (French version dated 9 July 2026, source id
`renard-2026-representations-groupes-reductifs-padiques`). The relevant passages
are V.3.11, V.3.12 and V.3.23 (printed pp. 112, 117), V.4.2 and V.4.8 (printed
pp. 118, 122), V.5.1 and V.5.2 (printed pp. 122–123), and the proof of VI.2.1
(printed pp. 138–139). This file adds no mathematics of its own. Its proof
composes the published Library theorems named above.
