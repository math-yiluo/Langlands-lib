# Proof: cotangent surjectivity for finite maps of augmented local algebras

This module proves `Langlands.CommutativeAlgebra.FiniteLocalCotangentSurjectivityStatement.{u,v,w}`
as the theorem `Langlands.CommutativeAlgebra.finiteLocalCotangentSurjectivity`, with the
independent universes of `K`, `A`, and `B` retained.

The setting is as in the statement. `K` is a field. `A` and `B` are local `K`-algebras, and
`B` is Noetherian. `r : B →ₐ[K] K` is an augmentation and `f : A →ₐ[K] B` is a `K`-algebra
map. `B` is an `A`-algebra through `f`, and it is a finite `A`-module for this structure.
The cotangent map `augmentationCotangentMap r f`, from the cotangent space of
`mA = ker (r.comp f)` to the cotangent space of `mB = ker r`, is surjective. The conclusion
is that `f` is surjective.

## Proof

1. **The kernels are the maximal ideals.** `r` and `r.comp f` are onto, since
   `r (algebraMap K B c) = c` and `(r.comp f) (algebraMap K A c) = c`. Their kernels are
   therefore the maximal ideals of the local rings `B` and `A`
   (`IsLocalRing.ker_eq_maximalIdeal`). In particular both lie in the Jacobson radical of
   `⊥` (`IsLocalRing.maximalIdeal_le_jacobson`).
2. **`mB ≤ f(mA)B + mB • mB`.** Let `b ∈ mB`. By surjectivity, the cotangent class of `b`
   is the image of the class of some `a ∈ mA`. That image is the class of `f a`, by the
   definition of `Ideal.mapCotangent`. By `Ideal.toCotangent_eq`, `f a - b ∈ mB ^ 2`. Hence
   `b = f a - (f a - b)` lies in `Ideal.map f mA ⊔ mB • mB`.
3. **`mB ≤ f(mA)B`.** `mB` is a finitely generated ideal, since `B` is Noetherian. So
   Nakayama's lemma `Submodule.le_of_le_smul_of_le_jacobson_bot` over `B` applies to step 2.
4. **`B = f(A) + mA • B`.** For `b ∈ B`, `b - algebraMap K B (r b)` lies in `mB`. Also
   `algebraMap K B (r b) = f (algebraMap K A (r b))`, because `f` is a `K`-algebra map. By
   step 3 and `Ideal.smul_top_eq_map`, the element `b - algebraMap K B (r b)` lies in
   `mA • ⊤` as an `A`-submodule of `B`. So `⊤ ≤ range (Algebra.linearMap A B) ⊔ mA • ⊤`.
5. **Conclusion.** `B` is a finite `A`-module, so `⊤` is finitely generated. Nakayama's lemma
   over `A` gives `⊤ ≤ range (Algebra.linearMap A B)`. Here `Algebra.linearMap A B` is `f`,
   so `f` is surjective.

## Provenance

This is an internal derived result, one of the four steps of the local closed-immersion
criterion `Langlands.AlgebraicGeometry.ProperRationalImmersionLocalClosedImmersionStatement`
(proved in `Langlands.AlgebraicGeometry.ProperRationalImmersionLocalClosedImmersionProof`);
no external theorem is transcribed.
The proof imports the published statement and uses only the Mathlib results cited above
and the actual cotangent map from `Langlands.AlgebraicGeometry.CotangentDualNumber`.

The proof applies to arbitrary characteristic and to possibly non-reduced algebras.
It requires no finite-type assumption over `K` or algebraic closure. Both locality
assumptions, Noetherianity of `B`, and finiteness for the action induced by the given
`f` are exactly those of the statement. This result concerns the finite augmented
local algebra criterion; tangent comparisons and scheme constructions are separate.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
