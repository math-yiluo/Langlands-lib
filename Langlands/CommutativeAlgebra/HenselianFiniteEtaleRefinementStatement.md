# Finite étale local refinement over a Henselian local ring

`Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinementStatement`
is a proposition, stated separately in each universe `u`. It is not proved in
this module.

For a Henselian local commutative ring `R` and an affine étale morphism
`f : Spec A → Spec R` whose image contains the closed point, the proposition
asserts the existence of a local commutative ring `R'` with an `R`-algebra
structure, finite as an `R`-module and étale over `R`. It also supplies an actual
morphism `g : Spec R' → Spec A` with
`g ≫ f = Spec.algebraMap R R'`. Thus the algebra structure in the conclusion
agrees with the composite through the given neighbourhood.

The premise `IsLocalRing.closedPoint R ∈ Set.range f` means that there is a point
of `Spec A` over the closed point of `Spec R`. The ring `R'` is nonzero because
`IsLocalRing R'` includes nontriviality. Neither a finite residue field nor
Noetherianity is assumed. The conclusion does not prescribe a residue-field
extension, retain a chosen point of `Spec A`, or assert that `g` is an open
immersion.

The source is the Stacks Project, *Commutative Algebra*, version `ed88ff78`,
Section 153, Lemma 153.3 (Tag 04GG), assertions (10) and (13), pp.411–413,
and Lemma 153.4 (Tag 04GH), especially assertion (4) and its proof, p.414.
The registered source is `stacks-commutative-algebra-chapter-ed88ff78`,
file `Stacks Project - Commutative Algebra, full chapter PDF (version ed88ff78).pdf`,
SHA-256 `b035a1f02104906a1820636cd332a0d7962fef3318d207a056634cb14dc86947`.

This is a derived interface to those ring-theoretic results. An étale affine
algebra is quasi-finite. Choose a prime over the maximal ideal of `R`. Tag 04GG
first separates the finite part of the algebra, then decomposes that finite
part as a finite product of local rings. The chosen prime selects a nonzero
local factor. This factor is finite over `R`; because it is an open and closed
component of the original étale algebra, it is also étale over `R`. The factor
projection gives `g` and the required factorization. Tag 04GH identifies the
corresponding localization as finite over `R`. Étaleness here uses the finite
product decomposition, rather than finite presentation of an arbitrary
localization.

The intended consumer pulls a supplied coordinate split maximal torus from
`Spec A` to `Spec R'`, then applies the local-ring root-space results. This
statement alone makes no assertion about group schemes or the existence of an
étale splitting neighbourhood.
