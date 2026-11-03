# Finite group-algebra maps and actual split-torus characters

Author: Worker 384.

This module supplies the character-side argument used in the split-torus
isogeny comparison. All fields and exponent groups are in an arbitrary universe.
There is no perfectness, separability, or characteristic-zero assumption.

The entry construction `splitTorus.diagonalizableMap I J f` is the morphism
from `D(ℤᴵ)` to `D(ℤᴶ)` induced by restriction along the published actual
character pullback `splitTorus.characterMap I J f`. Here `f` is an actual
homomorphism from the standard torus indexed by `I` to the one indexed by `J`,
over the spectrum of the field. The coordinate index types are finite.
The construction uses the existing group-algebra corepresentations and their
natural group-scheme morphism construction.

`diagonalizableMap_splitIso` proves that this construction equals `f` under
the existing standard split-torus isomorphisms. Its proof tests the two
morphisms on every scheme over the base. The image of each target coordinate
is the character obtained by pulling back its projection. The existing
character-lattice equivalence evaluates this character as the product of
coordinate units to their integral powers. This agrees with restriction of
the corresponding homomorphism from the exponent group to global units.
The auxiliary lemmas `diagonalizable_splitIso_points` and
`characterLatticeEquiv_proj` identify these evaluations. No claim of
surjectivity on field-valued points is used.

`diagonalizableMap_hom_left` identifies the underlying scheme morphism with
the spectrum of `Diagonalizable.incl` applied to the actual character
pullback. It unfolds the classifying map of the natural transformation and
uses `Diagonalizable.homEquiv_symm_restrict`.

The algebraic helper `Diagonalizable.incl_surjective` shows that a surjective
homomorphism of additive exponent groups induces a surjective group-algebra
map, by induction on sums of monomials. For a field `k` and an arbitrary
homomorphism `a : M →+ N`,
`Diagonalizable.finite_cokernel_of_incl_finite` proves that finiteness of
`k[M] → k[N]` implies finiteness of `N / range(a)`. The proof passes to the
group algebra of the cokernel. The quotient-induced algebra map is
surjective and therefore finite. Its composite with the original map
factors through augmentation to `k`. The resulting scalar map from `k` is
finite, so the cokernel group algebra is a finite-dimensional vector space.
Its standard basis is indexed by the cokernel, which must consequently be
a finite type.

`splitTorus.characterMap_finite_cokernel` transports a finite torus
morphism through the split-torus isomorphisms, uses the spectrum
identification, and applies this algebraic helper. It concludes finiteness
of the quotient of `I → ℤ` by the range of the actual coordinate character
map. Separately, `characterMap_injective_of_epi` proves that a categorical
epimorphism of the underlying schemes is injective on characters. Its
proof cancels that epimorphism after applying the character-lattice
equivalences. Flat surjective morphisms can supply this epimorphism
hypothesis in the later isogeny proof.

These are derived supporting constructions and lemmas, rather than an
assertion of the full anti-equivalence of diagonalizable groups. Their
mathematical source is the group-algebra exactness argument in Milne,
*Algebraic Groups* (2017), Theorem 12.9(a,b), printed pp.233–234
(PDF pp.249–250), source `milne-2017-algebraic-groups`. The implementation
proves the needed finite-cokernel consequence directly using Mathlib
finiteness of algebra maps and the Library's actual torus comparison.
Milne's printed pp.484–485 also describe the character-lattice isogeny and
its rational criterion in the split reductive setting; this module does
not assert that broader root-data result.

The registered official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was checked. Its Chapter 12
and Chapter 23 corrections do not change Theorem 12.9 or these passages
on pp.484–485.
