# Polynomial detection of nonnilpotence in a linear family

This derived internal module concerns a linear family of endomorphisms
`φ : V →ₗ[k] Module.End k W` over a field, with a finite basis of `V` and
finite-dimensional `W`. The scalar, vector, target, basis-index and extension
field types have independent universes.

`endomorphismFamilyBaseChange φ K` extends the parameters to `K ⊗[k] V`
and the operators to `K ⊗[k] W`, by composing the scalar extension of `φ`
with the canonical endomorphism scalar-extension map. If this actual extended
family contains a nonnilpotent endomorphism, then a coefficient below the
leading term of Mathlib's `LinearMap.polyCharpoly φ b` is nonzero over `k`.
Indeed, if all those coefficients vanished, the monic family characteristic
polynomial would be `X ^ finrank k W`. Mathlib's compatibility with scalar
extension and evaluation would force that same characteristic polynomial for
every member of the extended family; Cayley–Hamilton would make every such
member nilpotent, a contradiction.

A nonzero value of the chosen coefficient implies nonnilpotence: a nilpotent
endomorphism has characteristic polynomial `X ^ finrank k W`, whose
coefficient at the chosen lower index is zero. The module therefore supplies
a nonzero polynomial whose nonvanishing locus consists of nonnilpotent
members. Over an infinite field, the paired imported polynomial nonvanishing
lemma shows both existence of a ground-field nonnilpotent member and that
all nonnilpotent members span `V`.

The provenance is the described internal derivation from Mathlib's universal
family characteristic polynomial, its scalar-extension compatibility, the
characteristic-polynomial criterion for nilpotence, and the Library's
polynomial spanning lemma. No external structural theorem is assumed. This
is intended for the nonnilpotent adjoint locus in Cartan generation. It does
not identify an actual group adjoint differential, construct semisimple
replacement inside a group Lie module, or prove Cartan generation.
