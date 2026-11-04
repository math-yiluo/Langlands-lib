# Borel subgroups under extensions of algebraically closed fields: proof

Worker 1498 and Worker 1382, reusing Worker 1370's published solvability theorem.

- Worker 1498 wrote this module, `BorelFieldExtensionFields`, `BorelFieldExtensionKSide`
  and `BorelFieldExtensionMaximality`.
- Worker 1382 wrote the algebraic core, `BorelFieldExtensionHeight` and
  `BorelFieldExtensionDescent`.
- Worker 1370 wrote `solvableFieldExtensionStatement` (Library module
  `Langlands.GroupScheme.Absolute.SolvableFieldExtensionProof`).

`Langlands.GroupScheme.borelAlgClosedFieldExtensionStatement` proves exactly
`Langlands.GroupScheme.BorelAlgClosedFieldExtensionStatement.{u}`, with no additional
hypotheses. The statement is as follows. Let `k K : Type u` be algebraically closed fields with
`Algebra k K`, and let `G` be a group scheme over `Spec k` with `IsAffineHom G.X.hom`,
`Smooth G.X.hom` and `ConnectedSpace G.X.left`. Then for every `i : B ⟶ G` with
`IsBorelSubgroup i`, the base change
`i_K = (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i`
satisfies `IsBorelSubgroup i_K`. The universe, the characteristic and the extension
(algebraic or transcendental, of any degree) are arbitrary, and trivial groups are included.
The proof leaves `GroupScheme`, `IsBorelSubgroup`, `IsSolvableGroupScheme` and
`GroupScheme.baseChange` unchanged.

## The final theorem

After introducing the hypotheses, the proof registers `IsAffineHom G.X.hom` and
`Smooth G.X.hom` as instances. Smoothness gives `LocallyOfFiniteType G.X.hom` by instance
search. It then applies `BorelFieldExtension.isBorelSubgroup_baseChange_of_maximal`
(module `BorelFieldExtensionFields`). That lemma proves the four fields other than maximality
and takes maximality as its hypothesis. That hypothesis is discharged by
`BorelFieldExtension.maximal_baseChange` (module `BorelFieldExtensionMaximality`).

## Helper modules

Each helper module has its own Markdown file with full statements and proofs. In outline:

- `BorelFieldExtensionFields`: base change along any morphism of field spectra preserves the
  first four fields:
  - the closed-subgroup field, by `IsClosedSubgroup.baseChange`;
  - smoothness, by stability under base change;
  - connectedness, by `GroupScheme.connectedSpace_baseChange_of_smooth_affine`;
  - solvability, by `solvableFieldExtensionStatement`.

  Here `B` is affine because it is a closed subgroup of the affine `G`.
- `BorelFieldExtensionHeight`: a height inequality for the special fibre of a flat family. It
  is pure commutative algebra and uses the dimension inequality and going down from Mathlib.
- `BorelFieldExtensionDescent`: the algebraic core `exists_isPrime_lt_of_solvable`. Its
  setting is a finitely generated Hopf algebra `H` over the algebraically closed field `k`,
  with:
  - a solvable group `S` of `K`-points of `H`;
  - a prime `Q` of `K ⊗[k] H`, the vanishing ideal of `S`;
  - a prime `P` of `H` such that `Q` maps to zero in `K ⊗[k] (H ⧸ P)` (so `Q` is contained
    in the extension `K ⊗ P` of `P`), while `1 ⊗ p ∉ Q` for some `p ∈ P`.

  The conclusion is a prime `𝔭 < P` together with a solvable group of `k`-points
  containing every `k`-point that kills `𝔭`. The proof writes the equations of the derived
  series of `S` over `K`. It descends them to a finitely generated subalgebra of `K`,
  specializes them at a `k`-point (Nullstellensatz), and controls the specialized prime
  with the height inequality.
- `BorelFieldExtensionKSide`: over `k`, let `𝔭` be a prime contained in the coordinate kernel
  of a Borel inclusion. If some solvable group of rational points contains every rational
  point that kills `𝔭`, then the coordinate kernel lies in `𝔭`. The proof uses
  the closure of that group of points, its identity component, Jacobson density and
  maximality of `B`.
- `BorelFieldExtensionMaximality`: the dictionary between points of `G` or `G_K` and points
  of `H`, a comparison map `K ⊗[k] H → Γ(G_K)`, a Nullstellensatz for reduced schemes of
  finite type, and the maximality theorem `maximal_baseChange`. Let `B'` be a smooth,
  connected, solvable closed subgroup of `G_K` containing `B_K`. Let `S` be its group of
  `K`-points and `Q` its prime in `K ⊗[k] H`, and let `P` be the prime of `B` in `H`.
  - If `1 ⊗ P` is not contained in `Q`, the descent theorem and the `k`-side lemma give a
    contradiction.
  - Otherwise every `K`-point of `B'` lies in `B_K`. Since `B'` is reduced, `B'` then lies in
    `B_K`, and equality of coordinate kernels makes the inclusion `B_K → B'` an isomorphism.

## Relation to the literature

The statement is the preservation direction of J. S. Milne, *Algebraic Groups* (2017),
§17.66 (printed p.375, one-based PDF p.391; registered source `milne-2017-algebraic-groups`),
for algebraically closed `k` and `K`, as explained in the statement's Markdown. Milne derives
preservation from completeness of `G/B` and conjugacy of Borel subgroups. Neither is
available in the Library, so the implemented proof takes a different route. It specializes
solvable groups of points from `K` to `k` (modules `BorelFieldExtensionDescent` and
`BorelFieldExtensionHeight`) and uses the maximality of `B` over `k` directly (module
`BorelFieldExtensionKSide`). It uses no Borel fixed-point theorem, conjugacy, or properness
of `G/B`.

The transitive imports contain no `ParabolicDynamic`, parabolic field-extension or
connected-reductive field-extension module. The proof uses no new axioms.
