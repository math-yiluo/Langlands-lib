# Explicit low-degree cocycle contraction for diagonalizable groups

Let `R` be any commutative ring, `Λ` any abelian group, and `D = D_R(Λ)` the actual diagonalizable group scheme from the Library. Let `M` be any `R`-module, with an action of `D` given by `ModuleRepresentation M D`. This module constructs explicit contractions of regular one- and two-cocycles. Its theorem `hasVanishingLowDegreeCohomology` proves `HasVanishingLowDegreeCohomology D`.

There is no assumption that `R` is a field, that `Λ` is finitely generated or torsion free, or that `M` is finite, free, projective or flat. Thus the theorem includes nonsmooth diagonalizable groups and arbitrary quasi-coherent module coefficients. The lack of a finiteness condition on `Λ` is a feature of this internal construction; it makes no assertion that every such group satisfies the finite-type relative multiplicative-type predicate.

For an affine test algebra `A`, the averaging algebra is the group algebra `A[Λ]`. The actual universal `D`-point over that algebra is the scalar extension of the Library's universal point. `coefficientZero` extracts the coefficient of the identity character, and `average` tensors this linear functional with `id_M` over `R`:

`A[Λ] ⊗[R] M → A ⊗[R] M`.

The supporting lemmas prove that averaging recovers constant module points, is natural in `A`, and is invariant under translation by any point of `D(A)`. It also commutes with the action of a constant group point. The last fact follows by tensor induction: every pure tensor is a scalar multiple of a constant tensor, the action is linear over `A[Λ]`, and its value on constant tensors is controlled by naturality. No choice of module basis enters the argument.

For a regular two-cochain `c`, `averageTwo c` averages its second argument while holding the first one constant. Coefficient naturality makes the result a natural one-cochain. Evaluate the two-cocycle equation at two constant points and the universal averaging point, then apply `average`. Translation invariance identifies the last term, compatibility with the action handles the action term, and averaging constants recovers the original two-cochain value. The result is exactly

`c(h,k) + b(hk) = ρ(h)b(k) + b(h)`.

Thus `twoCocycle_isCoboundary` supplies an actual regular one-cochain primitive.

For a one-cocycle `c`, `averageOne c A` averages `c` at the universal point. The same argument gives

`averageOne c A = c(h) + ρ(h)(averageOne c A)`.

The average is natural in `A`. Applying this naturality to the structure map `R → A` and the canonical comparison `R ⊗[R] M ≃ M` shows that it comes from a single element of `M`. Its negative is the base element whose coboundary is `c`, with the differential convention in `RegularCochains`. This proves `oneCocycle_isCoboundary`.

Provenance: this is a derived construction from the published actual point, translation and identity-coefficient invariance results in `Torus.DiagonalizableAveraging`, Mathlib tensor products, and the regular affine-test cochain interface. It proves the split case of the low-degree vanishing used in Conrad, *Reductive group schemes* (2014), Remark B.2.4, p.285, by explicit averaging rather than the source's grading and derived-functor argument. It does not prove descent to a nonsplit multiplicative-type group, identify infinitesimal kernels with quasi-coherent modules, or prove a homomorphism lifting theorem.
