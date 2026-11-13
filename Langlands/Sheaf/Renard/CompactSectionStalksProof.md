# Proof: stalks are quotients of compact sections

Worker 41 implemented this proof for Task 5507. The entry theorem is
`Langlands.Sheaf.Renard.CompactSectionStalks.stalkQuotientComparison :
StalkQuotientComparison`. It proves the published statement
`CompactSectionStalks.StalkQuotientComparison` from
`Langlands/Sheaf/Renard/CompactSectionStalksStatement.lean`, unchanged: for every
`X : Type` with a topology satisfying `Langlands.Topology.IsLocallyProfinite X`,
every complex vector sheaf `F : VectorSheafScalars.VectorSheaf X` and every point
`x : X`, the canonical map `stalkQuotientMap F x` is bijective. No premise is
added: no compactness, countability or nonemptiness of `X`, and no restriction on
`F`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, II.2.5, Remarque, printed p.42 / PDF p.48, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. PDF p.48
was read for this proof. The Remark states
`F_x = F_c(X) / ⟨f · φ, φ ∈ F_c(X), f ∈ D(X), f(x) = 0⟩`. Its proof takes a
section `φ` vanishing near `x` with support `Z`, chooses a compact open `U`
containing `Z` but not `x` (using Lemma II.1.1), and notes that the characteristic
function `f` of `U` satisfies `f · φ = φ` and `f(x) = 0`. The Lean proof follows
this argument. It does not go through the source's middle description by sections
vanishing on a neighbourhood of `x`. A zero germ at `x` already means that `x` is
outside the support.

## Implemented proof

The file `CompactSectionStalksProof.lean` contains four declarations.

- `exists_isCompact_isOpen_between` is a topological helper. Suppose `X` has a
  compact open neighbourhood basis (`Langlands.Topology.HasCompactOpenNeighborhoodBasis`).
  Then every compact `K` inside an open `U` lies in a compact open `V` with
  `K ⊆ V ⊆ U`. For each `y ∈ K` the basis gives a compact open `W y` with
  `y ∈ W y ⊆ U`. `IsCompact.elim_nhds_subcover'` extracts a finite subcover, and
  `V` is the finite union of those `W y`. It is open by `isOpen_biUnion` and
  compact by `Finset.isCompact_biUnion`. This is the step Renard attributes to
  Lemma II.1.1. It generalizes the published
  `CompactSectionTestModule.exists_compactOpen_superset`, which is the case
  `U = univ`.
- `mem_vanishingSpan_of_germ_eq_zero`: let `hX : IsLocallyProfinite X` and let
  `s` be a compact section with `CompactGerms.germ F x s = 0`. The germ map is
  `Γgerm x` on the underlying section (`CompactGerms.germ_apply` holds by `rfl`),
  and `CompactSupport.support` is the set of points with nonzero germ. Hence
  `x ∉ support s` holds definitionally. The support is compact because `s` is a
  member of `CompactSupport.submodule`. The set `{x}ᶜ` is open because the
  Hausdorff half `hX.t2Space` gives T1. The helper, applied to the neighbourhood
  half `hX.2`, therefore gives a compact open `V` with `support s ⊆ V ⊆ {x}ᶜ`.
  `V` is closed by `IsCompact.isClosed` in a T2 space, so it is clopen. Let
  `f = PointwiseTestAlgebra.characteristic hV hVc`. Then `f x = 0` by
  `characteristic_apply` and `Set.indicator_of_notMem`, since `x ∉ V`. The
  published `CompactSectionTestModule.characteristic_smul_eq_self` gives
  `f • s = s`. Rewriting `s` as `f • s`, the published
  `CompactSectionStalks.smul_mem_vanishingSpan` puts it in `vanishingSpan F x`.
- `stalkQuotientMap_injective`: `stalkQuotientMap F x` is defined as
  `(vanishingSpan F x).liftQ (CompactGerms.germ F x) _`. By `LinearMap.ker_eq_bot`
  and Mathlib's `Submodule.ker_liftQ_eq_bot`, it is enough to show
  `ker (CompactGerms.germ F x) ≤ vanishingSpan F x`. That is the previous lemma.
- `stalkQuotientComparison`: introduce `X`, its topology, `hX`, `F` and `x`.
  Bijectivity is `stalkQuotientMap_injective` together with the published
  `CompactSectionStalks.stalkQuotientMap_surjective`.

The proof imports only `Langlands.Sheaf.Renard.CompactSectionStalksStatement`,
which brings in the published constructions. It edits no Library file. A
development check reported only the standard axioms `propext`,
`Classical.choice` and `Quot.sound` for `stalkQuotientComparison`.
