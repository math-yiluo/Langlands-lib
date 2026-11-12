# Generic isomorphism of inductions from parabolics sharing a standard Levi

Author: Worker 60. This module states one proposition,
`RationalSameLeviGenericInductionIsoStatement`. It supplies no proof.

## Statement

The data are those of the actual standard rational-point family used by
`RationalInducedK0WeylConjugacyStatement`:

- a nonarchimedean local field `k` of any characteristic;
- a connected reductive group scheme `G` over `k`, possibly nonsplit and
  non-quasisplit;
- a maximal split torus `i : T → G` and a generic cocharacter `ν`;
- the canonical evaluation topology `pointTopology` on `G(k)`. Local
  compactness, the nonarchimedean-group property and Hausdorffness of this
  topology are explicit instance binders.

The statement also takes `StandardCocharacterStatement`, which gives the
semidirect decompositions `P_I = L_I ⋉ U_I` of the literal standard families
`parabolic i ν`, `levi i ν` and `unipotent i ν`, and closedness of every
`U_I`. Field and representation-carrier universes `u` and `v` are independent.

Fix simple-root subsets `I` and `J` and a point `g ∈ G(k)` with
`x ∈ L_J ↔ g⁻¹ * x * g ∈ L_I` for all `x`. Then `g P_I g⁻¹` is a parabolic
subgroup with Levi `L_J`. In the Lean statement this conjugate decomposition
is `IsSemidirectDecomposition.conjugateWithLevi`, and its induction functor is
`conjugateInductionFunctor`. The point `g` need not normalize the torus. Fix
also connected reductivity of the Levi representative
`Standard.leviScheme i ν (rootSet i ν J)`; it is needed to form the published
coordinates on unramified characters. Let `σ` be an irreducible admissible
smooth complex representation of `L_J`.

The conclusion is the existence of a nonzero polynomial `p` in the published
finite coordinates `leviRationalUnramifiedCharacterCoordinates`. For every
unramified character `χ` of the full rational norm family
`leviRationalNormCharacters i ν J` in the nonvanishing locus
`leviUnramifiedPrincipalOpen i ν J hLJ p`, there is an actual isomorphism of
smooth `G(k)`-representations

`i_{P_J}(σ ⊗ χ) ≅ i_{g P_I g⁻¹}(σ ⊗ χ)`.

Both sides are the Library's actual normalized induction functors applied to
the literal twist `σ.twist χ`. The principal open is nonempty and dense
(`dense_leviUnramifiedPrincipalOpen`). It contains every character when the
coordinate rank is zero.

## Provenance and truth

This is an internal intermediate target. It isolates the
representation-theoretic content that remains after the published reduction
`inductionK0_comp_conjugationK0_of_rationalPrincipalOpen` and the companion
reduction module `RationalInducedWeylGenericIsoReduction`. It is the classical
generic-isomorphism property of normalized parabolic induction from two
parabolics with a common Levi. In the standard intertwining-operator
treatment, the integral operator `J_{P'|P}(σ ⊗ χ)` is rational in `χ`. For
irreducible `σ`, generic irreducibility of the induced representations
(Sauvageot) together with the nonvanishing of these operators makes them
isomorphisms off a proper Zariski-closed subset. The public
[Waldspurger source map](../../../../notes/plancherel/waldspurger-source-map.md)
records this theory: rows IV.1, Thm IV.1.1 and IV.3, and Sauvageot's
generic-irreducibility citation at IV.3, p.285. Worker 60 did not reread
those printed passages for this statement, and has not checked their
characteristic hypotheses. The formulation here is derived, not quoted. It
keeps the full scope of the target `RationalInducedK0WeylConjugacyStatement`,
whose positive-characteristic case presupposes the corresponding theory.

The statement is not an external Chapter V structural input. It is a
representation-theoretic proof obligation. Its isomorphism conclusion is
stronger than equality of the two exact finite-length classes. It is asserted
only generically in `χ`, and only for irreducible admissible `σ`.
