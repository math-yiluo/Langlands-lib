# Small projected elements from compact representatives

This internal topological lemma is derived for the adelic duality proof. It does
not assume or conclude any duality theorem. Let an additive group `K` map into a
topological commutative ring `R`, and let a noncompact additive topological group
`F` have a set-theoretic section `s` of a continuous additive map `p : R → F`.
Suppose `s(F)` is annihilated by a ring element `b`, and a compact set `C` meets
every coset modulo `K`. Then every neighborhood of zero contains `i(k) * b` for
some nonzero `k : K`.

The proof assumes the contrary for one neighborhood. Shrink it to a neighborhood
whose pairwise differences, after multiplication by `b`, lie in the original
one. Cover `C` by finitely many translates of the smaller neighborhood, and
choose a decomposition `s(x) = i(k(x)) + c(x)` for each `x : F`. If two compact
representatives lie in the same cover member, their difference gives a small
projected `i(k(y)-k(x))`; the contrary assumption forces `k(x)=k(y)`.
Consequently the values of `k(x)` are controlled by the finite cover. Applying
`p` shows that all of `F` lies in a finite union of translates of `p(C)`. That
union is compact, forcing the whole space `F` to be compact, a contradiction.
The section need not be continuous. The proof uses no approximation or character
classification theorem.
