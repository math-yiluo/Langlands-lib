# Quasi-compact projective immersions from an ample line bundle

`Langlands.AlgebraicGeometry.Picard.AmpleHQuasiProjectiveStatement` is a
proposition definition (universe parameter `u`). It is a statement only. The
module proves nothing.

## The statement

Let `R : Type u` be a commutative ring and let `X : Scheme.{u}` be a scheme with a
morphism `f : X ⟶ Spec (CommRingCat.of R)`. Assume:

- `LocallyOfFiniteType f` (Mathlib's predicate), and
- some line bundle `L : LineBundle X` (the Library's `Picard.LineBundle`) is
  ample in the Library's sense `L.IsAmple`.

Then `IsHQuasiProjective f` holds (the Library's predicate from
`Langlands.AlgebraicGeometry.HQuasiProjective`). That is, there are a natural
number `n` and a morphism `i : X ⟶ ProjectiveSpace R n` such that:

- `i` is an immersion,
- `i` is quasi-compact, and
- `i ≫ projectiveSpaceToSpec R n = f`.

The ring `R` is arbitrary. In particular it need not be noetherian.

The Library's `L.IsAmple` (module `Langlands.AlgebraicGeometry.Picard.Ample`)
says two things: `X` is quasi-compact, and every point of `X` lies in the open
locus `L.sectionOpen s` of some section `s` of a positive tensor power
`L^{⊗k}` (`k ≥ 1`) with this locus affine. This is the Stacks definition of an
ample invertible sheaf. The registered snapshot restates it at the start of
Section 29.38 (Properties, Definition 28.27.1).

## Source

Registered source `stacks-quasi-projective-ample-finite-type-2026-11-19`
(content SHA-256
`112270b8b6f437c38228945f1221ccc306b020c84ff13bc87f6c2c6efda77692`), file
`Stacks-29.40-02NO.html`, Lemma 29.40.3 (Tag 01VS):

> Let `f : X → S` be a morphism of schemes. Let `L` be an invertible sheaf on
> `X`. Assume that the invertible sheaf `L` is ample on `X`, and the morphism
> `X → S` is locally of finite type. Then there exists a `d₀ ≥ 1` such that for
> every `d ≥ d₀` there exist an `n ≥ 0` and an immersion `i : X → P^n_S` over
> `S` such that `L^{⊗d} ≅ i^*O(1)`.

The Lean statement specialises to an affine base `S = Spec R` and to the
Library's model `ProjectiveSpace R n` of `P^n_R`. It keeps only the existence of
some immersion over `S`. It drops the control of `d` and the identification
`L^{⊗d} ≅ i^*O(1)`.

The Lean conclusion also asks for `QuasiCompact i`, which Lemma 29.40.3 does not
state. This follows from the hypotheses, as the next section explains. With it,
the conclusion is exactly Stacks' H-quasi-projectivity, Definition 29.41.1 in
`Stacks-29.41-01VV.html` of the same source: "We say `f` is H-quasi-projective if
there exists a quasi-compact immersion `X → P^n_S` over `S` for some `n`." The
proof of Lemma 29.41.6 in the same file draws this conclusion from Lemma 29.40.3
in the same setting: "By Lemma 29.40.3 we see that there exists an immersion of
`X` into a projective space over `S`, i.e., `X` is H-quasi-projective over `S`".

## Why the immersion is quasi-compact

Ampleness includes compactness of `X` (`L.IsAmple.compactSpace`), so `f` is
quasi-compact. The structure morphism `ProjectiveSpace R n ⟶ Spec R` is
separated (a `Proj` construction), hence quasi-separated. If a composite
`i ≫ p` is quasi-compact and `p` is quasi-separated, then `i` is quasi-compact
(Stacks, Schemes, Lemma 26.21.14, cited for this purpose in footnote 2 of
Section 29.41). So any immersion `i` over `Spec R` given by Lemma 29.40.3 is
quasi-compact.

## Relation to other Library statements

`ProperAmpleClosedImmersionBySectionsStatement` (in
`Langlands.AlgebraicGeometry.Picard.ProperAmpleClosedImmersionBySectionsStatement`,
proved in the Library) is the proper counterpart. It assumes a noetherian ring,
a proper `f` and an ample line bundle, and gives a closed immersion by sections.
The present statement drops properness and the noetherian hypothesis. It gives
only an immersion, which need not be closed.

## Use

The proved reduction `largeLevelQuasiProjectivity_of_ample` (module
`Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelQuasiProjectivityAmpleReduction`) to
`LargeLevelQuasiProjectivityStatement` uses the universe-zero
instance `AmpleHQuasiProjectiveStatement.{0}` with `R = ℤ[1/n]`.
