# Finite multiplication kernel from an ample pullback identity

`Langlands.GroupScheme.FieldAmpleMultiplicationKernelStatement` is a
`Prop`-valued definition stating a target for a separate proof. This module
does not prove the proposition.

For every field `K : Type u` and every group scheme
`G : Grp (Over (Spec (CommRingCat.of K)))`, assume `IsCommMonObj G.X`.
Assume that its structure morphism `G.X.hom` is smooth, proper, and
geometrically connected. For every line bundle
`L : Langlands.AlgebraicGeometry.Picard.LineBundle G.X.left`, assume
`L.IsAmple`. For every natural number `n` with `0 < n`, assume that there
exists an isomorphism of actual module sheaves

\[
  [n]^*L \cong L^{\otimes(n\cdot n)}.
\]

The conclusion is that the structure morphism

```lean
(Langlands.GroupScheme.kernel
  (Langlands.GroupScheme.multiplication G (n : ℤ))).X.hom
```

to `Spec (CommRingCat.of K)` satisfies `AlgebraicGeometry.IsFinite`.
The quantifiers have exactly the order just described; the sheaf isomorphism
is a `Nonempty` hypothesis, so no chosen isomorphism is part of the target's
data.

## Concrete imported constructions

`LineBundle X` is the full subcategory of actual `X.Modules` whose objects
are locally isomorphic to the structure sheaf. Its underlying sheaf is
`L.obj`. The pullback is the existing
`AlgebraicGeometry.Scheme.Modules.pullback` along the underlying scheme
map `(multiplication G (n : ℤ)).hom.hom.left`. The line-bundle pullback
module proves preservation of local rank one.

The published multiplication map is the integer power of the identity in
the group of homomorphisms. On sections it is the power map, or multiplication
by `n` in additive notation. The exponent `n * n` in
`Langlands.Scheme.Modules.tensorPow L.obj (n * n)` is computed in `ℕ`.
These are right-associated sheafified tensor powers, with zeroth power the
structure sheaf and successor `tensorObj L.obj` of the preceding power.
Their trailing structure-sheaf factor is handled by tensor coherence, not
by a new convention for powers.

The kernel is the published pullback of the homomorphism along the identity
section in group schemes over the base. The published
`kernel_isPullback_scheme` identifies its underlying square as a pullback of
actual schemes, and `kernelι_isClosedImmersion` supplies the closed immersion
when the target structure map is separated. The conclusion concerns the
whole scheme-theoretic kernel, including possible nilpotents. It concerns
its structure morphism to the field, rather than its inclusion into `G`,
its set of points, or a reduced subgroup.

## Sources and derived provenance

The main source is J. S. Milne, *Abelian Varieties*, the 1986
*Arithmetic Geometry* article in the author's corrected version dated
January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The retained file is
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
Printed and one-based PDF page numbers agree.

The first proof paragraph of Theorem 8.2, p.13, restricts the multiplication
pullback of a symmetric ample invertible sheaf to the closed scheme kernel.
Its restriction is both ample and trivial, so the kernel has dimension zero.
The paragraph invokes Corollary 7.2, p.12, for a symmetric ample sheaf;
that corollary follows from projectivity in Theorem 7.1, pp.10–12. Here the
ample sheaf and the actual multiplication pullback identity are supplied
explicitly. Consequently the extracted implication needs no symmetry
hypothesis. The separately stated
`FieldSymmetricMultiplicationPullbackStatement` is intended to supply the
identity when a symmetric ample bundle has been obtained.

The provenance is **derived**: this is the finite-kernel implication of that
proof paragraph, isolated from the existence of the bundle and the proof of
the pullback formula. In detail, the intended geometric argument is:

1. Since `n > 0`, the exponent `n * n` is positive. A positive tensor power
   of an ample line bundle is ample.
2. The kernel inclusion is a closed immersion because `G` is proper, hence
   separated. Restricting the positive power to this closed subscheme
   preserves ampleness, and pulling back the displayed isomorphism
   identifies it with the restriction of `[n]^*L`.
3. On the kernel, multiplication factors through the identity section
   `Spec K → G`. The pullback of `L` along that section is a line bundle
   over the field, hence isomorphic to its structure sheaf. Pulling it
   back to the kernel makes the restricted multiplication pullback trivial.
4. The kernel is proper over `K`, being closed in the proper group scheme.
   A proper scheme over a field with an ample trivial line bundle is finite
   over that field. This yields the stated finiteness; Milne expresses the
   intermediate consequence as dimension zero.

These steps explain the extraction; they are not proofs implemented in
this module. In particular, proving rank one of the relevant tensor powers,
the needed tensor and pullback identifications, preservation of ampleness,
the factorization and field trivialization, and the proper ample-trivial
finiteness criterion remains separate work. No finiteness conclusion or
equivalent criterion has been supplied as an extra hypothesis.

The group-scheme presentation agrees with Milne's Section 20 opening
definition, p.42: smoothness, properness, and connected geometric fibres.
Over a field these are abelian varieties. For the variety convention on
p.2, properness gives separatedness and finite type; after algebraic
closure, smoothness gives regularity and reducedness. A connected regular
noetherian scheme is irreducible, since its irreducible components are
disjoint and open. Thus geometric connectedness supplies geometric
integrality, and the identity section supplies nonemptiness. This explains
the presentation; the equivalence is not proved here. Explicit
commutativity allows the existing bundled multiplication operation.

## Ampleness convention and comparison boundary

The imported ampleness definition follows Stacks Project Definition 28.27.1,
tag `01PS`, in the registered source
`stacks-invertible-picard-ampleness-2026-10-21`, folder SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`.
The retained folder is
`literature/Stacks Project - Invertible sheaves, Picard groups and ampleness (HTML snapshot 2026-10-21)`;
the relevant files are `01PS.html` and `01CY.html` (Lemma 17.25.10).

Precisely, `L.IsAmple` asserts `CompactSpace X` and, for each `x : X`,
the existence of a natural `m ≥ 1` and a global section of
`tensorPow L.obj m` such that `x` lies in its **entire** generation open and
that entire open is affine. This generation open is the largest open on
which the section-induced map from the structure sheaf is an isomorphism.
It is not an arbitrarily chosen affine neighbourhood.

In tag `01CY`, the source's `X_s` is the nonvanishing locus in the stalk
modulo its maximal ideal, and the lemma identifies it with the open where
the section trivializes the invertible sheaf. This is the mathematical
comparison with the imported generation-open presentation. The current
`Ample` module offers `LineBundle.isAmple_iff_nonvanishingLocus` only under
explicit hypotheses giving the residue-open comparison and local rank
one of every tensor power. This statement does not discharge those
hypotheses or treat that conditional interface as an unconditional proof.
The source comparison, including any passage from Milne's ample-invertible-
sheaf convention to this concrete formulation, must be justified in the
future geometric proof or its prerequisites.

## Scope and proof boundary

The field is arbitrary, with no algebraic-closure, perfectness, or
characteristic restriction. All positive natural numbers are included,
even when the characteristic divides `n`, and dimension zero is included.
There is no smoothness or reducedness assumption on the kernel and no
additional projectivity, finite-kernel, flatness, or isogeny hypothesis.
The statement asserts neither that multiplication is an isogeny, nor its
degree, nor etaleness. The substantial geometric proof belongs to a
separate exact-target proof task after this statement is published.

Worker 131 specified the exact interface and the extraction from Milne;
Worker 124 prepared this Lean statement and its source correspondence.
