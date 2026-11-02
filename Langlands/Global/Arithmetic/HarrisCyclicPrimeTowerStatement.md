# The local cyclic prime-step tower used in Harris's general position

Author: Worker 84. This module defines the proposition
`Langlands.Global.HarrisCyclicPrimeTowerStatement.{u}`. It supplies a
separate target for the field-theoretic tower needed in H2 of the global
automorphic and Henniart-input program. The module proves no existence
assertion.

## Mathematical content

For every prime `p`, every `F : PadicField.{u} p`, and every finite
extension `E : LocalFactor.CommonClosure.Extension F` that is Galois over
`F.Carrier`, the proposition asserts a natural number `n` and a family
`T : Fin (n + 1) → Extension F` such that

- `(T 0).field = E.field`;
- `(T (Fin.last n)).field = ⊥`, the copy of the base field in the common
  algebraic closure;
- for each `i : Fin n`,
  `GeneralPosition.IsCyclicPrimeStep F (T i.succ) (T i.castSucc)`.

The last condition uses the existing Library definition unchanged. It
requires an inclusion `(T i.succ).field ≤ (T i.castSucc).field`, a Galois
extension with cyclic automorphism group, and prime finite dimension.
The relative algebra is the actual inclusion expressed by Mathlib's
`IntermediateField.extendScalars`. Thus the tower descends from `E` to
`F`; each step has prime degree and is strict.

Every field lies in the same `AlgebraicClosure F.Carrier`. The tower is
not merely a sequence of abstract fields linked by unspecified
isomorphisms. The only extra premise on the finite extension is
`IsGalois F.Carrier E.field`. Solvability, a chosen composition series,
and an existing tower are not premises.

The universe `u` is arbitrary. All residue characteristics, including
`p = 2`, are retained, with no restriction on the extension degree. The
trivial extension is included: `n = 0` is allowed, and the step condition
then has empty index type.

## Original sources and derived scope

Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), Definition 4.5, printed p.201
(one-based PDF p.25), defines general position using a descending tower
from the Galois closure of `F'/F` to `F`. Condition (i) requires cyclic
steps of prime degree. Condition (ii) separately requires irreducibility
of the Mackey constituents at every stage. The proof of Lemma 4.7,
printed pp.204–206 (PDF pp.28–30), constructs suitable characters and
uses its exact-stabilizer condition to address irreducibility.

Jean-Pierre Serre, *Local Fields* (1979), Chapter IV, Section 2,
Proposition 7 and Corollary 5, printed pp.66–68 (PDF pp.73–75), give
solvability of inertia and, when the residue field is finite, of the
whole finite Galois group. Corollary 5 explains that the quotient by
inertia is cyclic in this case. Finite extensions of p-adic fields have
finite residue fields. A composition series of the resulting finite
solvable Galois group, followed by Galois correspondence, gives cyclic
Galois steps of prime degree.

This is an internal extracted prerequisite derived from those passages.
Harris starts the tower at a Galois closure. The present statement
allows any finite Galois `E/F` in the common closure, so that it can be
specialized to that closure. It expresses precisely the tower condition
using the Library's existing `IsCyclicPrimeStep`. It does not assert
Mackey irreducibility, an exact stabilizer, existence of a character,
general position, or a global realization of the tower.

The title restriction `n < p` of Harris's paper imposes no such
restriction on the local Galois-solvability argument. Harris's
character-construction issue at residue characteristic two is a
separate obligation; this tower proposition contains no character
construction. Serre's 2019 author corrections, PDF pp.2–3, contain no
correction to IV.2 Corollary 5. The Harris correction concerning the
earlier twisting calculation does not affect Definition 4.5(i).

Registered originals:

- `harris-1998-local-langlands`, SHA-256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- `serre-1979-local-fields`, SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

## Dependencies and verification boundary

The module imports
`Langlands.Global.Arithmetic.GeneralPositionStatement`. This supplies
the existing common-closure extension objects and `IsCyclicPrimeStep`.
Neither that module's general-position assertions nor the present
proposition are assumed true by defining this target.

The planned proof reuses the Library's actual inertia-solvability
theorem and `Langlands.FieldTheory.solvableGaloisPrimeTower`. The generic
tower theorem takes solvability as a premise; this target requires
deriving it for the actual local field and transporting the resulting
intermediate fields into the common closure. Its proof belongs to a
separate exact-target proof task after this proposition is independently
accepted and published.
