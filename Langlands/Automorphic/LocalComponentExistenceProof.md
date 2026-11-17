# Local components of automorphic representations at every place (proof)

Original proof author: Worker 3657.
Submission preparation: Worker 833. Verification: Workers 833 and 835.

Lean module: `Langlands.Automorphic.LocalComponentExistenceProof`. It imports
`Langlands.Automorphic.LocalComponentFinitePlace` (finite places, and the
reduction to the infinite places) and
`Langlands.Automorphic.OperatorSubquotientPlaceComponentComplex` (complex
places, importing the real-place module
`Langlands.Automorphic.OperatorSubquotientPlaceComponent`). It changes no
published file.

This is the entry point of the proof for Task 6815. It proves the
published proposition `Langlands.Automorphic.LocalComponentExistenceStatement`
(module `Langlands.Automorphic.OperatorSubquotientLocalComponentStatement`),
unchanged, with its universe parameter `u`.

## Main theorems

```lean
theorem Langlands.Automorphic.IrreducibleOperatorSubquotient.exists_realPlace_localComponent
    {r : ℕ} (Q : IrreducibleOperatorSubquotient F r)
    (hQ : Q.subquotient.IsJointlyAdmissible)
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) :
    ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      Archimedean.IsRealGKModule (r + 1) ρ π ∧ Archimedean.IsIrreducibleGKModule ρ π ∧
        Archimedean.IsAdmissibleGKModule ρ ∧ Q.subquotient.IsRealPlaceIsotypic v ρ π

theorem Langlands.Automorphic.IrreducibleOperatorSubquotient.exists_complexPlace_localComponent
    … -- the same at a complex place, with `U(r+1)`, `ℂ ⊗_ℝ 𝔤𝔩_(r+1)(ℂ)`,
      -- `IsComplexGKModule` and `IsComplexPlaceIsotypic`

theorem Langlands.Automorphic.localComponentExistence :
    LocalComponentExistenceStatement.{u}
```

The first two are clauses 2 and 3 of the target for one `Q` and one place
(`F : Type u`); the third is the target.

## Proof

- **Real place.** `OperatorSubquotient.exists_realPlaceComponent` (with
  `Q.irreducible`, the Library instance `space_nontrivial` and joint
  admissibility) gives a subspace `W` of `Q.Space`, irreducible for the
  place actions at `v` and admissible for `O(r+1)`. Take
  `V = ModuleCat.of ℂ W` (a carrier in universe `u`), `ρ` and `π` the
  restricted actions `restrictCompact` and `restrictLie`. Then:
  - `IsRealGKModule` is `PlaceComponent.isRealGKModule_restrict` (Library,
    `CuspidalArchimedeanGenericComponentReduction`) applied to
    `isRealGKModule_realPlace`;
  - `IsIrreducibleGKModule` is `PlaceComponent.isIrreducibleGKModule_restrict`;
  - `IsAdmissibleGKModule` is `PlaceComponent.isAdmissibleGKModule_restrict`;
  - `IsRealPlaceIsotypic` is `isRealPlaceIsotypic_restrict`.
- **Complex place.** The same with `exists_complexPlaceComponent`,
  `isComplexGKModule_restrict` applied to `isComplexGKModule_complexPlace`,
  and `isComplexPlaceIsotypic_restrict`.
- **The target.** `localComponentExistenceStatement_of_infinitePlaces`
  (`LocalComponentFinitePlace`) supplies the finite-place clause
  (`localComponentExistence_finitePlace`) and reduces the target to the two
  theorems above.

## Modules of the proof

- `Langlands/Representation/Smooth/JointIsotypicComponent.lean`: an
  irreducible admissible isotypic component for a smooth representation
  with a jointly irreducible commuting operator set.
- `Langlands/Automorphic/LocalComponentFinitePlace.lean`: the finite-place
  clause and the reduction to the infinite places.
- `Langlands/Automorphic/OperatorSubquotientPlaceComponent.lean`: real
  places, descent from the numerator, operator stability, `gkSpan`.
- `Langlands/Automorphic/OperatorSubquotientPlaceComponentComplex.lean`:
  complex places.
- `Langlands/Automorphic/LocalComponentExistenceProof.lean`: this module.

## Provenance and route

The target is the existence half of Getz–Hahn, *An introduction to automorphic
representations* (2024), Theorem 6.3.7, p.165 (PDF 179), with its proof on
p.166 (PDF 180) and Lemma 6.3.6 on p.165 (PDF 179)
(`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`), and
of Flath, *Decomposition of representations into tensor products* (1979),
Theorem 3, p.181 (PDF 177) (`flath-1979-tensor-products`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`;
printed page = PDF page + 4). It is read, as the statement's Markdown
explains, through isotypy at one place, as in Flath's proof of Theorem 1,
p.180 (PDF 176): "the restriction of `W` to `G_i` is `W_i`-isotypic".

The implemented proof follows Route A of the task (the operators at `v`
against the operators commuting with them) one place at a time. Its
finite-dimensional finiteness input is the same one used in the proof of
Getz–Hahn Theorem 5.7.2(ii), p.153 (PDF 168). It proves isotypy directly, without
building a tensor factorization `Q ≅ π_v ⊗ π^v` and without Flath's
restricted-product theorem (Route B is not used):

- at a finite place, the minimal-dimension and averaging argument of
  `JointIsotypicComponent` (see `LocalComponentFinitePlace.md`);
- at an infinite place, Worker 174's minimal-multiplicity construction for
  cuspidal realizations (`PlaceComponentExistence`), ported to operator
  subquotients, with isotypy from the operator-stability theorem (see
  `OperatorSubquotientPlaceComponent.md`).

Joint admissibility of `Q`, a hypothesis of the target, gives admissibility
of the local components; irreducibility of `Q` gives their irreducibility
and the isotypy.

## Axioms

`lean_check` (lake build) inspection of
`Langlands.Automorphic.localComponentExistence` reports only `propext`,
`Classical.choice` and `Quot.sound`.
