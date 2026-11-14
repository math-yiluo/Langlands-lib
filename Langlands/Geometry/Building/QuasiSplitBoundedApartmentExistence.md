# Bounded quasi-split apartments

This internally derived construction strengthens the existing quasi-split apartment
assembly by retaining algebraic bounds throughout the actual construction. It uses
the published multipliable-root opposite-pair theorem; that theorem is not an
additional premise of the final existence result.

`QuasiSplitAllDepthBoundedApartmentExistenceStatement` quantifies over an arbitrary
universe, a field with its supplied valuative relation, a compatible surjective
integer-valued valuation with henselian valuation ring, an affine quasi-split group,
and every prescribed maximal split torus. It concludes the existence of an actual
apartment class and centralizer datum satisfying full V6, with every root filtration
at every point and every real depth algebraically bounded in the original group.
The corollary `quasiSplitIntegerBoundedApartmentExistence` proves the previously
introduced depth-zero existence proposition by taking depth zero.

The scalar lemma chooses an integer below any real threshold. Surjectivity supplies
a nonzero base scalar with multiplicative valuation exp of the negative integer.
The normalized henselian additive extension takes that integer value on its image,
so the all-depth split-apartment scalar hypothesis holds.

The descent helper follows the published `exists_isOmegaCompatible_of_descent`
construction. It forms the split apartment of the centralizer torus over a finite
Galois splitting field, takes a Galois-fixed point, restricts its family first along
the original split torus and then to the original field, and proves the root-datum
valuation axioms and original-point normalizer shifts by the existing assembly
lemmas. Opposite pairs at multipliable roots use the supplied helper premise; the
final construction supplies the published proof `quasiSplitMultipliableOpposite`.
The original full V6 proof supplies compatibility of the same descended family
with the actual centralizer torus and its restriction-evaluation isomorphism.

For bounds, install the compatible cofinal relation induced by the normalized
henselian separable additive valuation on the splitting field. Split-apartment
boundedness applies to the chosen upper point at every depth. The exact
torus-then-field preimage theorem and finite upper-root products descend these
bounds to the original family. Its translation orbit then has bounded filtrations
at every point, since translation changes only the real threshold.

The final theorem obtains the actual full centralizer of the prescribed torus,
uses quasi-splitness to make it a torus, and chooses a finite Galois splitting
field. The existing structural theorems provide maximality and bijective character
restriction evaluation, so the strengthened descent helper applies. No completeness,
compactness or residue-field condition is used.

This result assumes quasi-splitness over the henselian base. It does not by itself
prove quasi-splitness over the actual maximal unramified field or the host task's
unconditional target. The original target and its imported files are unchanged.
