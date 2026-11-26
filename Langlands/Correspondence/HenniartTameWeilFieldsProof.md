# Frobenius parametrization of tame totally ramified fields

`Langlands.Henniart.tameWeilFrobeniusParametrization` proves
`TameWeilFrobeniusParametrizationStatement` for a p-adic base field in any
universe. The fields are the actual finite intermediate fields of its fixed
algebraic closure. The chosen Weil element has geometric degree `+1`.

The parametrization refines the field count used in Koch (1984), §8, Lemma 5,
printed p. 113 (PDF p. 6, `koch-1984-numerical-langlands-remarks`). The proof
uses the structure of the tame quotient that also appears in the proof of
Koch's Lemma 7. The finite ramification input is Serre, *Local Fields*, IV
§2, Proposition 7 and Corollaries 1 and 3 (PDF pp. 74–75,
`serre-1979-local-fields`), via `Ramification.Padic.finiteTameInertiaStructure`.

## Proof

1. **Initial field.** Let `β` be an `m`th root of a uniformizer of `K` and take
   its simple intermediate field `L`. The minimal polynomial divides the
   radical polynomial, so `[L : K] ≤ m`. Scaling the normalized additive
   order along the inclusion and applying the degree identity give
   `[L : K] = m · ord_L(β) · f(L/K)`. Both factors after `m` are positive
   integers. The degree bound forces `[L : K] = m` and `f(L/K) = 1`.
2. **Common inertia intersection.** A totally ramified field's fixing
   subgroup, together with absolute inertia, generates the absolute Galois
   group. The index of the fixing subgroup therefore equals the index of its
   intersection in inertia. Compare any two fields of degree `m` in a finite
   Galois subfield containing both. Absolute inertia surjects onto the zeroth
   lower ramification group there. Every subgroup of index `m` in that finite
   group contains the first lower group: its relative index in the first
   lower group is a power of `p` dividing `m`. The quotient by the first
   lower group is cyclic, so the subgroup of index `m` is unique. This also
   makes it invariant under conjugation by the finite Galois group. Pulling
   it back inside absolute inertia gives the same closed normal subgroup for
   every field. Its pullback to the Weil group is open by Krull openness of
   finite-field stabilizers and openness of Weil inertia.
3. **Field of a lift.** For a Weil element `w` of degree `+1`, extend the
   integer powers of its absolute Galois projection continuously to the
   profinite integers using `Weil.profiniteIntegerLifting`. The extension is
   a section of absolute residue degree by density of the integer powers of
   Frobenius. Adjoin its image to the common absolute inertia intersection.
   The resulting subgroup is closed, as membership is tested by multiplying
   by the inverse of the section at the element's residue degree. It meets
   inertia in the common intersection and has index `m`. Its fixed field
   is finite of degree `m`, and the degree scaling for the Weil map of the
   fixed field forces residue degree one since its Weil image contains `w`.
   Any other degree-`m` tame totally ramified field whose Weil image contains
   `w` has a closed fixing subgroup containing the section image and with
   the same inertia intersection. Decomposing elements using the section
   gives equality of the fixing subgroups and hence of the embedded fields.
4. **Bijection.** Every indexed field has a degree-one lift in its Weil
   image. For a fixed geometric Frobenius lift `φ`, every degree-one element
   is `g * φ` for `g` in Weil inertia. Two such translates fix the same field
   precisely when their ratio belongs to the common open normal subgroup.
   This gives the bijection from the inertia quotient to the fields. The
   index `m` gives the equivalence with `Fin m`.
