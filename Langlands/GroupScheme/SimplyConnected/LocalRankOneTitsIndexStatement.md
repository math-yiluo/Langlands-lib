# Actual local rank-one Tits indices

Author: Worker 165.

`Langlands.GroupScheme.LocalRankOneTitsIndexStatement.{u}` is an unproved
prerequisite for the local rank-one group classification. It enumerates
actual Tits indices. It supplies neither a proof of the enumeration nor
an identification of a group with a classical model.

Let `K : Type u` have the instances `Field`, `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField`. Let `G` be a group
scheme over `Spec K`, with affine and locally finite type structure
morphism. For every actual `d : TitsIndexData G`, if `G` is simply
connected, absolutely almost simple and has `splitRank G = 1`, the
statement asserts one of the following alternatives.

| Predicate on `d` | Absolute diagram | Distinguished vertices, numbered from 1 | Full star image |
| --- | --- | --- | --- |
| `HasRankOneInnerAIndex degree` | `A_(2*degree-1)`, with `degree > 0` | `degree` | identity |
| `HasRankOneOuterAIndex n` | `A_n`, with `n = 2` or `3` | `1` and `n` | identity and chain reversal |
| `HasRankOneCIndex n` | `C_n`, with `n = 2` or `3` | `2` | identity |
| `HasRankOneOuterD4Index` | `D_4` | `2`, the central vertex | identity and interchange of tips `3,4` |
| `HasRankOneInnerD5Index` | `D_5` | `2` | identity |

These are, respectively, Tits's indices `¹A_(2d-1),1^(d)`,
`²A_2,1^(1)` or `²A_3,1^(1)`, `C_2,1^(2)` or `C_3,1^(2)`,
`²D_4,1^(2)`, and `¹D_5,1^(2)`. The degree parameter is a positive
natural number in the first predicate; it is not supplied algebra data.

## Actual diagrams and actions

The predicates use the published actual index interface:
`d.Vertex` is the set of simple roots of the actual absolute root datum,
`d.cartan` is its integral root-coroot pairing,
`d.distinguishedVertices` is the complement of the roots restricting to
zero on the chosen maximal split torus, and `d.star` is the action of
the full group `SeparableClosure K ≃ₐ[K] SeparableClosure K`.

`d.IsNumberingOf M marked e` requires a bijection
`e : d.Vertex ≃ Fin n` that identifies every actual Cartan entry with
`M` and identifies distinguished membership in both directions with
`marked`. Thus every vertex and every pairing is compared. Each listed
predicate uses `CartanMatrix.A`, `.C` or `.D` and the specified marked
subset. No type name or group-model isomorphism is an input field.

`d.StarIsTrivial` fixes every actual vertex for every Galois element.
For the outer cases, `d.StarImagePair e τ` requires `τ ≠ 1`, requires
each Galois element to act globally either as the identity or as `τ`
under the same numbering, and requires some Galois element to realize
`τ` on all vertices. The choice between the two permutations is outside
the vertex quantifier. The identity is realized by `d.star_one`, so the
image is exactly the indicated two-element set. For outer A, `τ` is
`Fin.revPerm`. For outer D4, it is `Equiv.swap (2 : Fin 4) (3 : Fin 4)`.
This specifies the full image, without specifying a particular quadratic
extension or the kernel of the action. It excludes the order-three and
order-six trialitarian images.

The Lean numbering starts at zero. A displayed one-based vertex `j`
corresponds to `i.val + 1 = j`. Mathlib's actual `CartanMatrix.A n`
has `Fin n` rows and columns and is the rank-`n` chain, despite its
docstring calling it `A_(n-1)`. For `C_n`, the final lower off-diagonal
entry is minus 2. Here `d.cartan a b` means root `a` evaluated on
coroot `b`, so this is the type-C orientation of Tits's diagram.
For `D_n`, Mathlib's zero-based fork vertex is `n-3` and its tips are
`n-2,n-1`. After subtracting 1, these agree with the numbering in Tits's
Table I.

The statement has arbitrary universe `u` and retains every characteristic
of `K` and its residue field, including 2. It assumes actual index data
for every choice `d`; existence and choice-independence of those data are
separate structural obligations. The locally finite type instance is
required by the actual index interface. The final classification target
does not acquire this or any other additional premise: its proof must
derive the needed structure and construct the actual index data.

## Source comparison and provenance

The enumeration is a derived formulation of the following registered
original sources using the Library's actual root datum. It is not quoted
as a theorem with this Lean interface.

1. G. Prasad and M. S. Raghunathan, *On the Kneser–Tits problem*,
   Comment. Math. Helv. 60 (1985), 107–121,
   `prasad-raghunathan-1985-kneser-tits`, PDF SHA-256
   `42f4db49659757b703d1b9c72c6ae5e17d75161eb13088790bd60b549a30058f`,
   §2, printed p.111 / PDF p.6. This supplies the local classification's
   arbitrary-characteristic scope, lists the classical families and
   excludes exceptional rank-one forms. It attributes characteristic zero
   to Kneser and arbitrary characteristic to Bruhat–Tits.
2. J. Tits, *Classification of algebraic semisimple groups*, Proc.
   Sympos. Pure Math. 9 (1966), 33–62,
   `tits-1966-classification-algebraic-semisimple`, proceedings PDF SHA-256
   `962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.
   Section 2.3, printed p.39 / PDF p.44, defines the actual index and
   inner type by trivial star action. Table I, printed p.53 / PDF p.58,
   fixes the numbering. Table II explanations and classical entries,
   printed pp.54–57 / PDF pp.59–62, give the diagrams, distinguished
   vertices, classical descriptions and special-field restrictions.
   Its exceptional and trialitarian entries, printed pp.58–61 /
   PDF pp.63–66, give the comparison excluding rank one over the
   fields in column `p`. That column means p-adic fields; it is not
   itself an arbitrary-characteristic assertion.
3. F. Bruhat and J. Tits, *Groupes algébriques simples sur un corps
   local*, in T. A. Springer (ed.), *Proceedings of a Conference on
   Local Fields* (Driebergen 1966), 1967, 23–36,
   `springer-1967-conference-local-fields`, PDF SHA-256
   `903b0fb1de045c18061e25513c2272cbca56b0149e2508c0b4a3638bb719bbb6`.
   Section 4, printed p.29 / PDF p.35, works over complete discretely
   valued fields with perfect residue field. Section 8, Proposition 6,
   printed p.35 / PDF p.41, identifies the anisotropic groups as inner
   type A under the residue-field conditions satisfied by a finite
   residue field. This is the structural input for extending the local
   admissibility argument to every characteristic.

Setting relative rank `r = 1` in the classical entries of Table II
gives the following comparison. Inner A has `d(r+1) = n+1`, hence
`n = 2d-1` and distinguished vertex `d`. Outer A over a p-adic field
has `d = 1` and `n = 2r-1, 2r, 2r+1`; its nontrivial outer cases are
`n = 2,3`, with endpoints forming one distinguished orbit. In type C,
the nonsplit local case has `d = 2`, so distinguished vertex `2`.
The intended ranks are `2,3`. The type-C `p` line actually prints
`n = 2r` or `2r-1`; this conflicts with its own distinguished vertex
`rd = 2r ≤ n` and with PR85's rank `2` or `3` symplectic family.
This statement uses `2r+1` for the second possibility, with that source
discrepancy explicit, as in the published classification's Markdown.

For type D with `d = 2`, inner D allows `n = 2r` or `2r+3`,
and outer D allows `n = 2r+1` or `2r+2`. At `r = 1`, the new
absolutely simple cases are outer D4 and inner D5, with distinguished
vertex `2`. Their star actions are, respectively, the transposition
of the last two tips and the identity. The case D2 is not absolutely
simple; the D3 cases are renumbered as A3. The rank-one cases of B1
and C1 are A1; B2 is C2 after interchanging the two vertices, which
also takes its distinguished vertex 1 to the distinguished vertex 2
used here. The split type-C case has `n = r = 1` and is covered by
inner A1. These coincidences explain the normalization to five
alternatives rather than additional B or small-D cases.

This source comparison explains the statement's intended meaning.
Proving it through actual anisotropic kernels and admissibility,
including exclusion of every exceptional or trialitarian index and
transport between all actual index choices, remains necessary.
The intended proof route is independent of the final group-model
classification; that final theorem is not an input of this statement.

## Implemented helper proofs and remaining obligations

`HasRankOneInnerAIndex.hasInnerTypeA` forgets the marked-vertex condition
and uses positivity of `degree` to obtain positive absolute rank. It
then supplies the same Cartan numbering and trivial full star action
to the published `HasInnerTypeA` predicate. No norm-one identification
is proved or assumed by this helper.

`StarImagePair.not_starIsTrivial` uses a Galois element realizing the
specified nonidentity permutation. If every actual vertex were fixed,
surjectivity of the numbering would force that permutation to be the
identity. This proves the stated incompatibility.

The main enumeration is a closed `Prop`-valued definition and remains
unproved. The proof of the enumeration, construction and structural
properties of actual indices, classical group-scheme identifications,
and the unconditional `LocalRankOneClassificationStatement` are still
separate obligations.
