# Positive-order detection for smooth mirabolic representations

Authors: Worker 700, Worker 749.

`Langlands.Derivative.MirabolicDerivativeDetection F T` is an unproved
proposition definition. For every prime, p-adic field `F`, supplied
compatible topology datum `T`, nontrivial unitary additive character `ψ`,
natural number `N` and actual smooth complex representation `A` of
`GeneralLinear.mirabolic N F.Carrier`, it asserts

```lean
Nontrivial A → 0 < level T ψ A
```

The field and representation-carrier universes `uF` and `uV` are independent.
The category is `SmoothRep.{0,uF,uV}` with the supplied topology installed.
There is no finite-length, Artinianity, admissibility, irreducibility,
homogeneity, segment, product, head, socle or classification premise.
`Nontrivial A` tests the actual underlying vector space, rather than a
chosen irreducible constituent or an isomorphism class.

The imported `level` is the finite maximum of orders with nontrivial
actual derivative carrier, with zero as its default. A valid order is
`k` with `0 < k ∧ k ≤ N+1`. The corresponding published functor
`mirabolicDerivativeOfOrder T ψ N k hk` has target `GL_(N+1-k)`.
Its object is the actual iterated minus-functor quotient, including
the rank equality transport in the published construction.
The existing elementary theorem `level_pos_iff` makes the asserted
positivity equivalent to the existence of a nontrivial derivative at
one of these orders. That equivalence alone does not prove detection.

The source is Bernstein–Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 3.5, printed p.452 / one-based PDF page 13, constructs a finite
filtration for every smooth representation of the mirabolic group,
whose successive factors are plus-functor images of its positive
derivatives. If all derivatives vanish, these factors vanish and hence
the representation vanishes. The implication recorded here is that
consequence, expressed with the Library's finite-maximum level. This
provenance is derived from the general filtration, rather than a claim
that the paper uses the Library's `Nat.findGreatest` packaging.
The source's `P_n` is the Library's `mirabolic (n-1)`, so its orders
`1,…,n` become `1,…,N+1`. Section 3.2, printed p.451 / PDF page 12,
supplies the exact sequence and functor identities used to construct
the filtration.

The original PDF pages 12–14 were read and page 13 was inspected as an
image by Worker 700; Worker 749 independently reread the extracted text of
PDF pages 12–13, including the definition `τ^(k) = Ψ⁻(Φ⁻)^(k-1)(τ)` for
`k = 1,…,n` and the filtration `0 ⊂ τ_n ⊂ … ⊂ τ_1 = τ` with
`τ_k/τ_(k+1) ≅ (Φ⁺)^(k-1)Ψ⁺(τ^(k))`. No source-specific errata note was present in the supplied public
notes. A search for corrections to BZ77 section 3.5 found the original
article and publication records, but no applicable correction. This is
a record of that search, not a claim that no erratum exists.

The rank boundary `N=0` is included: the only valid positive order is
one, and its target is `GL_0`. The source group is then `P_1`.
There is no order-zero derivative assertion. For a zero carrier,
the imported construction gives level zero; the premise of the
displayed implication excludes this case.

The derivative construction uses explicit determinant absolute-value
twists of exponent `-1/2`, inherited from the published minus functors.
These twists change the group action but not the underlying quotient
carrier, so they do not affect which carriers are nontrivial. Comparison
with the source's Haar-modulus normalization remains a separate
obligation and is not used or asserted here. This statement supplies
no filtration, exactness theorem, analytic detection proof, plus-model
embedding or lattice comparison.

This is a standalone general BZ77 statement. Its later proof must be
independent of the strong-indecomposability reduction that consumes it,
the segment derivative formulas of Zelevinsky 1980 sections 3.5 and
9.6, every segment head/socle existence or classification result,
both nonadjacent and full two-supercuspidal product conclusions,
and all the further exclusions in its task contract. Sharing its
proposition with those consumers does not prove it.

The only direct project import is the independently published
`Langlands.Representation.Derivative.Homogeneity`. Its accepted definition
artifact `609028d8-d915-4c8c-8223-2ece7bff15ff` was freshly fetched and
verified; both frozen bundle hashes match the workspace pair and the current
public pair. Its independent semantic review approves without qualifications.
This supplies the constructions and elementary laws described above, with
its stated normalization qualification retained.

The complete transitive project import closure was checked against Library
commit `e40be87d4e73ac457e91929eddf904bd95d12d2f` by Worker 700 and again
by Worker 749 against the current Library commit
`84146da9789e8ef59d6b18efecbc0086898b1f14`. In both checks all 53
dependency Lean/Markdown pairs, including the direct import, are
byte-identical to the published tree. No project
module is missing and every dependency is paired. The complete closure is:

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Dual.Definitions
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Topology.Nonarchimedean.Subgroup
```

These dependencies are general group, smooth-representation, quotient,
twist, character, minus-iteration and derivative-level constructions and
elementary laws. None contains an analytic derivative-detection or
filtration proof, a segment construction or derivative formula, a product
irreducibility or commutation result, the combined mirabolic
strong-indecomposability reduction, or an ordered-socle, head, exhaustion,
coverage or classification conclusion excluded in the task. The later
BZ77 proof dependencies described above remain proof obligations; no
unproved proposition is used as a theorem here. Every later proof and
lower split must retain the full task exclusion set and audit its own
mathematical and import dependencies.

Development checks `7dd06d53-2258-40ef-92ce-77fe3cd1c8a3` and
`f0a8022d-945d-449a-bbe1-5d1f2a226cee` succeeded with zero errors or
warnings. Inspection reports a definition returning `Prop`,
exactly the independent universe parameters `uF` and `uV`, and only
`propext`, `Classical.choice` and `Quot.sound`. The source's complete
outer telescope is `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`; the character, rank and actual representation
are universally quantified inside the proposition, after installing the
supplied topology. A separate scratch check confirmed that the
proposition is equivalent to its literal expansion with `Nontrivial` on
the carrier `A.obj.V` and `Nat.findGreatest`, that it is equivalent via
`level_pos_iff` to the existence of a valid order `k` with nontrivial
`(mirabolicDerivativeOfOrder T ψ N k hk).obj A`, that at `N=0` it yields
nontriviality of `(Mirabolic.psiMinus T 0).obj A`, and that it
instantiates at distinct universes. These development checks establish
elaboration and proposition kind. Independent semantic acceptance and publication are still
required; no proof of detection is supplied.

The Library already contains the proved helper
`Langlands.Derivative.Mirabolic.subsingleton_of_psiMinus_phiMinus` in
`Langlands.Representation.Derivative.MinusVanishing`: a smooth
representation of `mirabolic (m+1)` whose `Ψ⁻` and `Φ⁻` carriers both
vanish has zero carrier. This statement does not import it. A later proof
may use it only after auditing its own dependency closure against the full
exclusion set above.
