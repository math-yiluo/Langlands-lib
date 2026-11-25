# Faithfully flat strictly Henselian DVR extensions

The theorem
`Langlands.CommutativeAlgebra.strictHenselianDvrExtension.{u}` proves the
unchanged published proposition
`Langlands.CommutativeAlgebra.StrictHenselianDvrExtensionStatement.{u}`.
It applies to every commutative domain DVR in every universe, without
completeness, excellence, residue-characteristic, or residue-finiteness
hypotheses.

## Implemented proof

Fix an irreducible element `t` of the base DVR `R` and let `Ω` be an
algebraic closure of its fraction field. Both `Ω` and the subalgebras used
below live in the same universe as `R`.

The companion module `MaximalUniformizerSubalgebra` defines
`FixedUniformizer t S`: the image of `t` in `S` is a nonunit and every
element of `S` is zero or a power of that image times a unit. The bottom
subalgebra has this property, and nonempty directed unions preserve it.
The inverse of a putative unit image of `t` in a union would already occur
in one stage, a contradiction. Zorn's lemma gives a maximal such `S`.
The published elementwise DVR criterion makes `S` a domain DVR; the image
of `t` is irreducible and the base map is local.

`FixedUniformizer.algebraMap_surjective` shows that every local flat
essentially finite type formally unramified DVR algebra `T` over `S` has
a surjective base map. The helper `EtaleDvrRootExtensions` embeds `T` in
`Ω` over `S`: pass to fraction fields, use finite type and unramifiedness
to obtain an algebraic field extension, and embed it in the algebraically
closed field. The image of `T` is an `R`-subalgebra containing `S`. The
image of the chosen uniformizer remains irreducible, so transfer its
power-unit factorizations through the isomorphism to this image.
Maximality forces the image to be `S`. Injectivity of the embedding then
proves surjectivity of the original base map.

`FixedUniformizer.exists_root_of_simple` realizes a prescribed simple root
of a monic polynomial at any field point whose kernel is the maximal
ideal. The companion root extension lemma uses a standard etale
polynomial algebra and localization at that point's prime kernel.
`EtaleDvrExtensions` proves that this local extension is a domain DVR.
Surjectivity from the preceding paragraph pulls its distinguished root
back to `S`; faithful flatness reflects the root equation, and the field
point preserves its prescribed value.

`FixedUniformizer.henselianLocalRing` applies this result to the residue
point of a proposed simple root, giving the Henselian root and its required
congruence. `FixedUniformizer.isSepClosed_residueField` applies
`IsSepClosed.of_exists_root`. A monic irreducible separable polynomial over
the residue field lifts to a monic polynomial over `S`. Choose a root in
an algebraic closure of the residue field; separability makes the
derivative nonzero there. Apply the same prescribed-root result to the
composite field point, whose kernel remains the maximal ideal. Reducing
the resulting root of the lifted polynomial gives a root of the original
residue polynomial.

Finally, `strictHenselianDvrExtension` takes this `S` as `A`. Its
`R`-module is torsion free, hence flat over the Dedekind domain `R`.
The local flat base map is faithfully flat. These instances supply exactly
the existential witnesses of the published statement.

## Provenance and scope

This is an internal alternative proof of the existential consequence of
[Stacks Tag 04GP, Lemma 10.155.2](https://stacks.math.columbia.edu/tag/04GP),
[Tag 07QM, Lemma 15.46.1(1)](https://stacks.math.columbia.edu/tag/07QM), and
[Tag 0AP3, Lemma 15.46.11](https://stacks.math.columbia.edu/tag/0AP3).
The registered source is
`stacks-strict-henselian-dvr-extension-2026-11-16`; its retained files
`04GP.html`, `07QM.html`, and `0AP3.html` were read at their statements and
proofs. No matching project erratum was found.

The Stacks construction uses a filtered colimit of pointed etale
algebras. The implemented proof instead uses a maximal subalgebra in a
fixed algebraically closed overfield. It establishes exactly the
existential statement, including the same-universe witnesses. It makes
no assertion that the constructed ring has the strict Henselization's
universal property, that its residue field is a chosen separable closure
of the base residue field, or that the construction is canonical.
