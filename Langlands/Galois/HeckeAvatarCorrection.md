# Idele correction at a coefficient place

Fix the integral infinity type `t`, a coefficient embedding `ι : L →+* ℂ`,
a lift `emb σ : K →+* L` of every complex embedding `σ`, and a lift `φ` of the
finite idele character as in `IsHeckeFinitePart`. For a place `λ` of `L`,
`avatarPlaceBelow (emb σ) λ` contracts `λ` to the base field using `emb σ`.
`avatarCompletionMap` uses the Library's completion map for those two places.
Writing `jσ,λ` for this map and `x_f` for the finite factor of the idele `x`,
`correctedIdeleValue` is

\[
  \iota_\lambda(\phi(x_f))
   \prod_{\sigma:K\hookrightarrow\mathbb C}
         j_{\sigma,\lambda}(x_{v(\sigma,\lambda)})^{t(\sigma)}.
\]

`ι_λ` is the actual embedding `L → L_λ`. Each contraction lies over the
rational prime of `λ`. On a principal idele the monomial is the completed
value of the complex infinity type and cancels the finite part. The formula
is trivial on the infinite idele factor. At a finite place of different
residue characteristic every coordinate entering the monomial is one.

`HeckeAvatarIdeleCorrectionStatement` asserts the existence of a continuous
character of the actual idele-class group with values in
`(λ.adicCompletionIntegers L)ˣ`. The first identity specifies its value on
every full idele after the actual units inclusion. The second exposes the
comparison on one-place ideles of different residue characteristic for
later use with local units and uniformizers. The formula and both identities
apply to arbitrary integral infinity type.

## Source and proof route

The construction is the rank-one transport of Serre, *Abelian l-Adic
Representations and Elliptic Curves*, Chapter II §2.3, pp. II-10–II-12,
especially the principal-idele identity and the correction formula on
p. II-11. Section 2.7, pp. II-23–II-24, identifies the complex infinity type
via the real correction. Serre's factor on the diagonal equals the finite
part, which is the inverse of the written complex infinity type. Thus the
monomial in the formula here uses `t` with the displayed sign.

The finite-part lift has open kernel, so after the embedding into `L_λ`
it is continuous. The correction factor is continuous by the coordinate
and completion maps. Principal cancellation uses
`AdelicFunctoriality.FiniteExtension.completionMap_coe`, the diagonal
coordinate formula in `InfinityType`, and the pairing of complex embeddings
by infinite places. Descend via the quotient topology. The resulting
valuation homomorphism to the discrete torsion-free value group kills the
infinite factor and the compact product of finite integral units. It then
factors through the proved finite `IntegralIdeleClassQuotient`, so its image
is trivial. The completed integer units have the subspace topology from the
field units via value and inverse, giving the asserted continuous corestriction.
The comparison at a place of different residue characteristic follows from
the contraction formula and the one-place coordinate computation.

Source ID `serre-abelian-l-adic-1989` (SHA-256
`971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4`).
