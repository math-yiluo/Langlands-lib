# Proof of the irreducible inducing subquotient assertion

Authors: Worker 320 (original draft), Worker 514 (import reduction and verification).

The proof uses the Library's actual normalized first-adjointness linear
equivalence to turn the supplied nonzero map into a nonzero map from the whole
normalized Jacquet module to `σ`.

The helper `SmoothRep.exists_irreducible_quotient_subquotient_of_nonzero`
takes a simple quotient `ρ` of this map's actual image. Finite length of the
Jacquet source implies finite length, hence Noetherianity, of that image.
The image is nonzero, so its group-algebra submodule lattice has a maximal
proper element. The actual quotient by that element is irreducible. The
source-to-image surjection composed with the quotient map gives a surjection
from the whole Jacquet module onto `ρ`; the image inclusion in `σ` gives the
actual subquotient relation.

Since `ρ` is nonzero, this surjection is a nonzero intertwiner. Inverse first
adjointness gives a nonzero map from `π` into normalized induction of `ρ`.
Irreducibility of `π` makes that map injective, yielding the required actual
embedding. Neither the proof nor the helper uses a classification result.

This implements the elementary image step from Jantzen (1997), Lemma 5.5,
printed pages 1226–1227, registered source `jantzen-1997-supports-classical`,
in the generalized form specified by the statement Markdown. The assertion
starts after any induction-in-stages comparison.

The closing theorem has outer parameters `{p : ℕ} [Fact p.Prime]` and
`(F : PadicField.{uF} p) (T : F.TopologicalData)` and proves the published
`IrreducibleInducingSubquotientStatement.{uF,uV} F T` directly. The field
and carrier universes remain independent, including ranks and block shapes
without additional restrictions. The inducing representation `σ` remains
arbitrary smooth: no finite-length, irreducibility or admissibility assumption
on it is introduced. The proof imports no segment, multisegment or Langlands
classification theorem.
