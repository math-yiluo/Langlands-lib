# Triangular linear normalization

Author: Worker 1687.

This is an internal construction for the ordered PBW proof. It is proved directly
from well-founded recursion and linear algebra; it does not invoke an external
normal-form or PBW theorem.

Let `k` be any commutative ring, `W` any type, `r` a well-founded relation on `W`,
and `rule w p` a relation between words and finitely supported formal sums over
`k`. A word is `Irreducible` if no rule starts there. `Triangular r rule` says
that every word in the support of a right-hand side is strictly below the
left-hand word. `Coherent r rule` says that two right-hand sides have the same
image under every endomorphism of the free word module which respects all
rules whose left-hand words are strictly smaller.

`normalizeWord` uses well-founded recursion. At a reducible word it chooses a
right-hand side and takes the linear combination of the recursively normalized
support words. At an irreducible word it returns its unit singleton. The
construction is defined even without triangularity, by dropping support terms
which are not smaller. `normalize` extends word normalization linearly.

Under triangularity, normalized sums are supported on irreducible words;
normalization fixes every irreducible-supported sum, is idempotent, and has
image exactly the submodule of such sums. Every formal sum differs from its
normal form by an element of `relations rule`, the submodule spanned by
`single w 1 - p` for rules `rule w p`. These assertions follow by well-founded
induction on words, then by linearity on finite sums.

Adding coherence makes normalization respect every rule: the inductive
hypothesis supplies exactly the smaller-rule premise of coherence. Consequently
its kernel is exactly `relations rule`, and two sums have equal normal forms
if and only if their difference belongs to that submodule.

The construction is generic: the future PBW application must establish its
triangularity and coherence hypotheses using the actual Lie bracket and must
compare the resulting word relations with the actual universal enveloping
algebra. No such concrete conclusion is claimed by this helper.
