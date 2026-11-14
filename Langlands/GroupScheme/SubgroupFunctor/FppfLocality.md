# Fppf locality of represented subgroup membership

Internal subgroup descent support for the derived-group correspondence.
Membership in a monomorphic group homomorphism's range can be checked on
any fppf covering family of the test scheme. Containment in that range
can be checked after base change to every member of an fppf cover of the
base. There is no finiteness restriction on either cover.

The proof uses subcanonicity of the fppf topology to regard the covering
family as effectively epimorphic. Monicity forces compatibility of the
local lifts; effective epimorphy descends them to a single lift over the
original test scheme. The containment criterion then applies this
membership argument to the pulled-back covering family.

This is internal content derived from published subgroup base-change
equivalences and Mathlib's fppf sheaf theorem.
