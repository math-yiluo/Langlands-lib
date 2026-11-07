# Finite-point avoidance for affine pinching

This auxiliary development constructs compatible affine neighborhoods for finite
pinching. It is derived work following the proof of Theorem 5.4(a) and Lemma 5.5
in Ferrand, *Conducteur, descente et pincement* (2003), printed pp. 570–572,
registered as `ferrand-conducteur-descente-pincement-2003` (PDF pages 18–20).
The schemes and morphisms are actual Mathlib schemes and morphisms. The finite
sets can contain arbitrary points, including nonclosed points.

`exists_add_mem_ideal_avoiding` states that, for an ideal `I`, finitely many
prime ideals none of which contains `I`, and an element `v`, there is an
`a ∈ I` for which `v + a` lies in none of those primes. The implementation
uses induction on the finite family. When the current representative lies
in a new prime `p`, it adds a product from `I` which avoids `p` and belongs
to every earlier prime not contained in `p`. Earlier primes contained in
`p` are automatically avoided once `p` is avoided. A separate finite-product
induction supplies this correction. Thus the proof includes families with
specializations between their prime points and makes no closed-point
assumption.

`exists_section_lift_avoiding` applies this algebraic result to the kernel of
the surjective map on global sections of a closed immersion into an affine
scheme. Under the canonical affine-spectrum isomorphisms, a point outside the
closed subscheme corresponds to a prime not containing that kernel. Adjusting
any lift by an element of the kernel therefore preserves its restriction and
makes it invertible at every prescribed point outside the closed subscheme.
This implements Ferrand's Lemma 5.5.

`exists_basicOpen_of_finite_in_affineOpen` transports the Library's finite-point
prime-avoidance lemma from the scheme of an affine open to its ambient scheme.
It produces a principal open of the chosen affine open which contains the finite
set and lies inside any other open containing that set. The proof uses the
isomorphism between sections on the open and global sections on its associated
scheme, and identifies the image of the resulting principal open.

`exists_affineOpen_lift_basicOpen` applies section lifting on an arbitrary
affine open `U` of `X`. Given a section on `i ⁻¹ᵁ U` and a finite set `E`
inside `U` and disjoint from the range of the closed immersion `i`, it constructs
an affine open `V ≤ U` containing `E` whose inverse image under `i` is
exactly the principal open defined by that section.

`exists_compatible_affineOpens_of_finite` is the compatible-neighborhood step
in Ferrand's proof of Theorem 5.4(a). Its hypotheses are a closed immersion
`i : Z ⟶ X`, a finite morphism `j : Z ⟶ Y`, the property that every finite
set has an affine neighborhood on each of `X` and `Y`, finite sets `E ⊆ X`
and `F ⊆ Y`, and disjointness of `E` from the range of `i`. It produces affine
opens `U` and `V` with `E ⊆ U`, `F ⊆ V`, and
`i ⁻¹ᵁ U = j ⁻¹ᵁ V`. The equality also ensures that the image under `i`
of `j ⁻¹' F` lies in `U`.

The implementation first chooses affine neighborhoods `U₀` of
`E ∪ i '' (j ⁻¹' F)` and `V₀` of `F`; finiteness of `j` makes this choice
possible. Prime avoidance on `i ⁻¹ᵁ U₀`, followed by a section lift retaining
`E`, shrinks `U₀` to an affine `U₁` such that `j ⁻¹' F ⊆ i ⁻¹ᵁ U₁`
and `i ⁻¹ᵁ U₁ ≤ j ⁻¹ᵁ V₀`. Since `j` is closed, the complement
`W = Y \ j '' (Z \ i ⁻¹ᵁ U₁)` is open, contains `F`, and has
`j ⁻¹ᵁ W ≤ i ⁻¹ᵁ U₁`. A principal open `V` of `V₀` containing `F`
and contained in `W` thus has inverse image contained in `i ⁻¹ᵁ U₁`.
Pull its defining section back to `i ⁻¹ᵁ U₁` and lift it once more, retaining
`E`. Its principal open `U` has the required equality of inverse images.

This module does not construct a pushout or prove the AF-preservation target
on its own. Those conclusions also require a theorem realizing compatible
affine pairs as affine neighborhoods in the supplied pushout.
