# Local finite free representatives with minimal residue-field ranks

`Langlands.Cohomology.ModuleComplex.localMinimalPerfect` proves the exact
`LocalMinimalPerfectStatement.{u}`. The universe `u` is arbitrary. The inputs
are a commutative ring `R`, an actual bounded finite projective cochain
complex `K` of `R`-modules, and a prime ideal `p`. No further hypothesis
is added.

Write `κ := p.ResidueField` and
`d i := Module.finrank κ
  (((baseChange (algebraMap R κ)).obj K).homology i)`.
The theorem proves that these homology modules are finite over `κ`. It also
provides a single `r ∉ p` and a bounded finite free complex `P` over
`Localization.Away r`, together with an isomorphism from the derived image
of `P` to that of the ordinary localization of `K`, and a linear equivalence
`P.X i ≃ₗ[Localization.Away r] (Fin (d i) → Localization.Away r)`
in every degree. The same `r` and `P` satisfy all conclusions.

## Implemented proof

The proof composes three existing results:

1. `primeMinimalPerfect`, from
   `Langlands.Cohomology.PrimeMinimalPerfectProof`, gives finite residue-field
   homology and one bounded finite free complex `L` over `Localization.AtPrime p`.
   It supplies an actual homotopy equivalence from `L` to the localization
   of `K` and linear equivalences from each `L.X i` to the free module of
   rank `d i`.
2. `primeFreeHomotopyDescent`, from
   `Langlands.Cohomology.PrimeFreeHomotopyDescentProof`, is applied with the
   rank family `n := d`, this `L`, its finite freeness, its homotopy
   equivalence and its termwise linear equivalences. It returns one
   `r ∉ p`, a bounded finite free `P` over `Localization.Away r`, an actual
   homotopy equivalence from `P` to the ordinary localization of `K`, and
   the termwise linear equivalences with the unchanged ranks `d i`.
3. `derivedIsoOfHomotopyEquiv`, from
   `Langlands.Cohomology.PerfectModuleComplexHomotopy`, sends that last
   homotopy equivalence to an actual isomorphism in the derived category.
   The final tuple retains all the other witnesses returned by descent.

Thus the rank family always comes from the homology of the original
residue-field extension of `K`; it is never recomputed using a different
representative. The derived category uses the local instance
`HasDerivedCategory.standard`, as in the target statement.

## Source and scalar-extension conventions

The source is the Stacks Project, *More on Algebra*, tag
[0BCD](https://stacks.math.columbia.edu/tag/0BCD),
`lemma-lift-perfect-from-residue-field`, together with the preceding local
lemma [0BCC](https://stacks.math.columbia.edu/tag/0BCC).
The complete statements and proofs are in `more-algebra.tex`,
lines 19547–19625, at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, registered as
`stacks-perfect-complexes-a04446e5` with folder SHA-256
`54c831042614714cdb007a024d45dca7f60709efe2c307389ca2ad848b0ccbed`.
No project errata note for this source was available when preparing this proof.

The source first constructs a minimal model over the local ring and then
descends it to a principal neighborhood. The implemented proof follows
these two steps through the proved homotopy versions named above.
It proves the precise ordinary scalar-extension formulation in the
unchanged target. The source's derived-tensor interpretation uses the
mathematical fact that bounded projective complexes are K-flat; this file
does not construct a derived tensor functor or prove a general K-flatness
theorem. Independence of ordinary scalar extension from the choice of
bounded projective representative is separately proved by
`baseChangeDerivedIso` in `PerfectModuleComplexHomotopy`: it lifts the
derived comparison to a homotopy equivalence between K-projective
representatives, extends that equivalence, and returns to the derived
category. These comparisons use actual proved maps and homotopies rather
than an inference from the definition of `baseChange`.

No geometric cohomology, proper direct image, base-change theorem for
schemes, or local Picard conclusion is asserted here.
