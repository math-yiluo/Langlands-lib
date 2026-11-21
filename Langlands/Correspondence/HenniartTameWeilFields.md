# Degree-m tame fields and Frobenius cosets

`tameFieldWeilImage K E` is the image of `W_E` in `W_K` for an actual
`TameTotallyRamifiedExtensions K m` index. Its map is the published
`Weil.Local.intermediateWeilMap`, using the prescribed field in the fixed
closure. `tameInertiaCosets K J` is the quotient of inertia `I_K` by the
restriction of a given open normal subgroup `J` of `W_K` to `I_K`.

`TameWeilFrobeniusData K m φ` packages the following data, without asserting
that such data exists:

- an open normal subgroup `J` of `W_K` contained in `I_K`;
- an enumeration of `I_K/J` by `Fin m` and a bijection from `I_K/J` to the
  actual tame totally ramified fields of degree `m`;
- for each indexed field `E`, the intersection of the image of `W_E`
  with `I_K` equals `J`;
- for every `g` in `I_K`, the field indexed by the coset of `g` has `g * φ`
  in its Weil image.

`TameWeilFrobeniusParametrizationStatement` asserts the existence of this
package for `p ∤ m` and any lift `φ` of geometric degree `+1`. The degree
convention is the published `localDegreeInt`. By the last two properties,
for a given indexed field the elements of degree `+1` in its Weil image
are precisely `J` times the indicated lift. Conjugate but distinct fields
are not identified.

**Derived provenance.** H. Koch, *Bemerkungen zur numerischen lokalen
Langlands-Vermutung* (1984), §8, printed p. 113 (PDF p. 6), Lemma 5 and the
description of the tame quotient in Lemma 7. Lemma 5 counts the actual
embedded fields. The coset parametrization refines that count by recording
which lift of Frobenius fixes each field and by retaining their common
inertia kernel. In a finite tame inertia quotient of order `m`, extend the
finite quotient by an unramified degree divisible by the old group order.
Each degree-one lift then generates a subgroup mapping isomorphically to
the new residue group, and its fixed field is totally ramified. The
cyclicity of the finite tame inertia quotient (Serre, *Local Fields*, IV
§2, Proposition 7, Corollary 1) gives the common inertia kernel. This is
an arithmetic input to the fixed-cutoff averaging route, not a statement
about representation counts.
