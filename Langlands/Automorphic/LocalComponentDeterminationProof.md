# Automorphic representations are determined by their local components

Author: Worker 3657.

`Langlands.Automorphic.LocalComponentDeterminationProof` combines the forward
and reverse implications with the published theorem
`Langlands.Automorphic.localComponentExistence`.

## Main theorem

```lean
theorem Langlands.Automorphic.localComponentDetermination :
    LocalComponentDeterminationStatement.{u}
```

This is the exact published target
`Langlands.Automorphic.LocalComponentDeterminationStatement` of
`Langlands.Automorphic.OperatorSubquotientLocalComponentStatement`, with its
universe parameter `u`. For a number field `F : Type u`, `r : ℕ` and
irreducible jointly admissible operator subquotients `Q`, `Q'` of `GL_(r+1)`,
`Nonempty (Q.Equivalence Q')` holds exactly when both restrictions at every
finite place are isotypic for the same irreducible representation of
`GL_(r+1)(F_v)`, and both restrictions at every real or complex place are
isotypic for the same irreducible `(𝔤, K)`-module. All local carriers are in
`ModuleCat.{u} ℂ`.

## Proof

- `localComponentDetermination_forward` takes the components of `Q` supplied
  by `localComponentExistence`. Composing the local intertwining maps with the
  global equivalence transports their spanning images to `Q'`.
- `localComponentDetermination_reverse` encodes the place actions of `Q`
  and `Q'` as commuting, jointly irreducible families of free-monoid
  representations. Each common local type is equivalent to the corresponding
  admissible component of `Q`. This gives scalar self-intertwiners and, at
  each finite place, a spherical fixed space of dimension at most one.
  Smoothness gives eventual spherical invariance for each vector of `Q` and
  `Q'`. `CommutingFamily.exists_linearEquiv_of_isotypic` uses these facts to
  construct a linear isomorphism intertwining every place action.
  `OperatorSubquotient.equivalenceOfPlaceComm` extends the intertwining to the
  full operator algebra using stability of the graph of that isomorphism.

Joint admissibility enters through the existence of the local components of
`Q`. The theorem retains both joint admissibility hypotheses of the target.

## Modules of this proof

| Module | Content |
| --- | --- |
| `Langlands.Global.FiniteAdelicGL.OpenSubgroupInduction` | open subgroups of `GL_n(𝔸_f)`, induction over local factors, smooth vectors fixed by `GL_n(𝒪_v)` almost everywhere |
| `Langlands.Representation.CommutingFamilyUniqueness` | abstract uniqueness for commuting families of isotypic actions |
| `Langlands.Representation.FreeMonoidGenerators` | free-monoid representations given by generators and common isotypic types for monoid representations and `(𝔤, K)`-modules |
| `Langlands.Automorphic.OperatorSubquotientPlaceGeneration` | stability and intertwining for the full operator action on smooth subquotients |
| `Langlands.Automorphic.LocalComponentDeterminationForward` | "⇒" |
| `Langlands.Automorphic.LocalComponentDeterminationReverse` | "⇐" |

## Provenance

Getz–Hahn's Theorem 6.3.7 identifies the factors of an irreducible admissible
module up to isomorphism and uses their restricted tensor product to recover
the global module. See *An Introduction to Automorphic Representations*
(2024), pp. 165–166 (PDF pp. 179–180), and §5.7, pp. 151–153 (PDF pp. 166–168).
The registered source is `getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

Flath identifies the local factors through isotypic restriction at the end
of the proof of Theorem 1, p. 180 (PDF p. 176). The preceding spherical fixed
space corollary is on p. 179 (PDF p. 175). Example 2 and Theorems 2 and 3 on
p. 181 (PDF p. 177) give the role of the spherical lines in comparing
restricted tensor products. The description of the archimedean factors
follows the definition of an admissible adelic module on p. 182 (PDF p. 178).
See *Decomposition of representations into tensor products* (1979), registered
as `flath-1979-tensor-products`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.

The Lean proof uses the isotypy and restricted tensor product ideas of this
uniqueness argument. Its direct construction chooses one nonzero vector on
each side with matching local relations. The one-dimensional spherical
spaces control these relations outside a finite set, and Jacobson density
lets the proof arrange them at the remaining places. Cyclic evaluation on
restricted tensor products of the local cyclic spaces then gives the global
intertwiner. `FreeMonoidGenerators.nonempty_equiv_of_isotypic` supplies
local type uniqueness, and `OperatorSubquotientPlaceGeneration` uses finite
adelic smoothness and the archimedean compact and Lie decompositions to pass
from this place-by-place intertwiner to the whole operator action.

## Axioms

The Lake build in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(development check `26abd25c-1ac9-40de-8128-e4ef871201fe`) reported zero
errors and zero warnings. `localComponentDetermination` uses `propext`,
`Classical.choice` and `Quot.sound`.
