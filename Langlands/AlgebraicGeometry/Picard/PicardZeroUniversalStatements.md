# Uniqueness target for universal geometric Picard-zero bundles

`Langlands.AbelianScheme.PicardZeroUniversalUniquenessStatement` is a
proposition definition. Assuming the explicit rigidified pullback coherence
proposition, it quantifies over any scheme `S : Scheme.{u}`, abelian scheme
`A/S`, parameter schemes `P` and `Q` over `S`, and actual relative
rigidified line bundles `L` and `M` parametrized by them. If both families
satisfy `IsUniversalPicardZero`, it asserts that there is a unique
isomorphism `e : P ≅ Q` in `Over S` such that the actual rigidified pullback
of `M` along `e.hom` is isomorphic to `L`.

The isomorphism being unique is the parameter-scheme isomorphism. The
compatibility condition is `Nonempty` of a bundle isomorphism; uniqueness
of a bundle-isomorphism witness or triviality of rigidified automorphisms
is not asserted. Neither existence of a universal bundle nor an
abelian-scheme structure on `P` or `Q` is part of the conclusion.

No global `PicardZeroPullbackStatement` hypothesis is needed for this
target. Each universal family already satisfies the geometric-fibre
condition by its own universal-property predicate, so it can be classified
by the other one. The expected inverse maps and their identities use
classification uniqueness and the identity/composition comparisons of
actual rigidified class pullback. The coherence proposition is therefore
retained explicitly. This describes the rationale of the target; this
module supplies no proof.

The registered original source is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft,
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VI §1, paragraph (6.2), printed p.88 (PDF p.92), gives the
universal rigidified bundle property by actual pullback and a unique
parameter map. Printed p.95 (PDF p.99) and Corollary (7.22), printed
p.106 (PDF p.110), motivate the geometric-fibre criterion selected by
parent-task item 3.

This is a derived uniqueness target for that universal property restricted
to the existing Picard-zero classes. It is not claimed to be a verbatim
theorem from those passages. It imposes no noetherian or projectivity
hypothesis on the base, because it concerns uniqueness conditional on
universal families, rather than a representability or existence theorem.
