# Finite length of finitely generated admissible quasicuspidal Levi representations

Author: Worker 395.

`Langlands.CuspidalSupport.leviQuasicuspidalFiniteLength` proves the
existing closed proposition
`Langlands.CuspidalSupport.LeviQuasicuspidalFiniteLengthStatement`.
For every prime `p`, `F : PadicField.{uF} p`, compatible topological data
`T`, rank `n`, actual standard product Levi `G = B.Levi F.Carrier`, and
`A : SmoothRep.{0,uF,uV} Complex G`, the theorem deduces
`IsFiniteLength Complex[G] A.representation.asModule` from exactly
admissibility, Levi quasicuspidality and
`Module.Finite Complex[G] A.representation.asModule`.
The field and representation universes remain independent. The closing
theorem explicitly orders its universe parameters as field, then carrier,
matching the published statement.

The proof keeps the actual group, representation and algebraic group
algebra. All four helper theorems below are internal deductions in the
namespace `Langlands.CuspidalSupport.QuasicuspidalFiniteLength`.

## Generation after restriction

`orbit_span_eq_top` starts from a finite group-algebra generating family
`v : Fin m → ρ.asModule`. It forms the complex span of all translates
`ρ g (v i)` and proves that this span is invariant under `G`. Its
corresponding group-algebra submodule contains the original generating
family, hence is the whole module. The complex span of those group
translates is therefore all of `V`.

`exists_fixedVectors_generating` applies to a smooth complex representation
of a nonarchimedean weakly locally compact group and an open subgroup `H`
such that `J = H ⊔ center G` has finite index. Choose the preceding finite
family `v` and, for each left coset `q : G ⧸ J`, its representative
`s(q) = q.out`. The vectors

```text
w(q,i) = ρ(s(q)⁻¹)(v i)
```

form a finite family. The published
`Langlands.exists_compactOpen_fixing_finite`, with the neighborhood `H`,
gives a compact open subgroup `K ≤ H` fixing every `w(q,i)`.

For arbitrary `g` and `i`, set `q = [g⁻¹]`. Mathlib's
`QuotientGroup.mk_out_eq_mul` gives `s(q) = g⁻¹ j` for some `j ∈ J`.
The center is normal, so `Subgroup.mem_sup_of_normal_right` expresses
`j = h z` with `h ∈ H` and `z ∈ center G`. Thus

```text
g = h z s(q)⁻¹,     ρ(g)(v i) = ρ(h)(ρ(z)(w(q,i))).
```

Centrality makes `ρ(z)(w(q,i))` fixed by `K`: the actions of `k ∈ K`
and `z` commute, and `k` fixes `w(q,i)`. Any `H`-subrepresentation
containing `V^K` therefore contains every `ρ(g)(v i)`. The orbit-span
lemma makes it the whole representation. This proves that `V^K`
generates the restriction to `H`. Finite index is used only for `J`,
not for `H`.

`finite_of_fixedVectors_generating` is an algebraic lemma. If `V^K` is
finite-dimensional and has the preceding generating property, choose
finitely many complex generators of `V^K`, regard them as elements of
the restricted group-algebra module, and take their `Complex[H]`-span.
The corresponding `H`-subrepresentation contains `V^K`, so equals the
whole representation. These vectors witness `Module.Finite` for the
restricted module. There is no finite-dimension assertion about all of
`V`.

## Semisimplicity and finite length

For the actual Levi, set `H = determinantUnitOpenSubgroup T B`.
The published `determinantUnit_sup_center_finiteIndex` gives the finite
index required above. The chosen `K` is an ambient open subgroup, so
`A.IsAdmissible` supplies finite dimension of its fixed-vector space.
The two generation lemmas consequently give finite generation over
`Complex[H]`.

The forward implication of the published
`CuspidalSupport.leviHarishChandraTheorem` turns Levi quasicuspidality
into compact smooth-dual coefficients on the determinant-unit
restriction. The proof installs the published topology of `H`, its
nonarchimedean and locally compact structures, its resulting total
disconnectedness, and its Borel measurable structure. It chooses the
left Haar measure supplied by Mathlib and applies
`CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients`.
The restriction is smooth by `isSmooth_determinantUnitRestriction`.
This yields semisimplicity of its actual group-algebra module through
`Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`.

Mathlib provides Noetherian and Artinian instances for a finitely generated
semisimple module; the latter uses `IsSemisimpleModule.finite_tfae`.
The proof combines them with
`isFiniteLength_iff_isNoetherian_isArtinian` to obtain finite length
over `Complex[H]`. It does not construct a separate numerical bound
on invariant-subspace chains.

`finiteLength_of_restriction` proves the final transfer for any subgroup.
Forgetting some invariance gives an order embedding from the lattice of
`G`-subrepresentations into that of `H`-subrepresentations, retaining
each underlying complex subspace. Compose it with Mathlib's
`Subrepresentation.subrepresentationSubmoduleOrderIso` for each action.
This embeds the original group-algebra submodule lattice into the
restricted one. Pull back well-founded strict descent and strict ascent
along this embedding, obtaining respectively Artinianity and
Noetherianity for the original module. Their conjunction proves the
required `IsFiniteLength` over `Complex[G]`.

## Boundary cases and provenance

The same proof handles rank zero and the empty product Levi. Its imported
Harish-Chandra theorem explicitly includes rank zero; the determinant-unit
finite-index result and topology constructions cover every block shape.
The proof never chooses a nonzero vector or assumes positive rank.
The finite generating family and the common-stabilizer construction
allow an empty index type, so zero representations are also included.

No scalar or generalized central-character hypothesis, irreducibility,
supplied semisimplicity, or supplied restricted finite length occurs in the
closed theorem. Its statement pair and complete import closure are
preserved. The proof uses no downstream general admissible finite-length
theorem or induced finite-type or finite-length result.

The source-to-statement correspondence is documented in
[the statement's paired Markdown](QuasicuspidalFiniteLengthStatement.md).
Its registered originals are Silberger, *Introduction to Harmonic
Analysis on Reductive p-adic Groups* (1979),
`silberger-1979-harmonic-analysis`, Theorem 5.4.1.6 and proof,
printed pp.291–292, and Bernstein–Zelevinsky, *Representations of the
group GL(n,F) where F is a non-Archimedean local field* (1976),
`bernstein-zelevinsky-1976-representations-gln`, §§2.39–2.44 and
3.18–3.21, printed pp.26–28 and 34–35. Their respective retained
content hashes are
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`
and
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
No source-specific errata note is present in the workspace's public notes.

The implemented route derives finite generation of the determinant-unit
restriction directly and then uses Mathlib's semisimple module criterion.
It does not reproduce Silberger's central-character reductions. The four
helper lemmas and the uniform rank-zero extension have the internal
provenance explained above; the compact-coefficient and determinant-unit
ingredients are imported by their published Lean names.
