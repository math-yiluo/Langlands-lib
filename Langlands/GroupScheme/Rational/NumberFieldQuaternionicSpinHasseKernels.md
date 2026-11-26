# The quaternionic spin Hasse kernel from its norm-one and central parts

Module: `Langlands.GroupScheme.Rational.NumberFieldQuaternionicSpinHasseKernels`.

Throughout, `D` is a central division algebra of dimension four over the ground field (a
quaternion division algebra), `σ : FirstKindInvolution F D` is an involution of the first
kind whose symmetric subspace has dimension three (an orthogonal involution), and
`q : σ.QuadraticForms (Fin n)` is a quadratic form in the sense of Tits whose polar Gram
matrix is invertible (`σ.IsNondegenerateQuadratic q`). Such forms correspond to
nondegenerate skew-hermitian forms of rank `n` for the canonical involution of `D`.
`σ.isometryGroup q` is the isometry group `O(q)`, and `σ.normOneIsometryGroup q` is the
kernel of the reduced norm of `M_n(D)` restricted to `O(q)`, the special unitary group
`SU(h)` of the corresponding skew-hermitian form `h`.

The module states two propositions, proves neither of them, and proves that together they
imply the published `NumberFieldQuaternionicSpinHasseStatement`. The proof also uses the
connectedness of the norm-one group, `quaternionicNormOneIsometryConnectedness` from
`Langlands.GroupScheme.Quaternionic.NormOneIsometryConnectedness`.

## The two statements

`NumberFieldQuaternionicNormOneIsometryHasseStatement`: over a number field `F`, for every
`n ≥ 1`, every nondegenerate `q` and every finite Galois extension `L/F` in the same
universe, every cocycle `ξ : Cocycle (σ.normOneIsometryGroup q) (GaloisCocycle.cover F L)`
with `ξ.LocallyTrivial` satisfies `ξ.IsTrivial`. Local triviality means triviality after
pullback to the full cover `Spec (F_v ⊗_F L) → Spec F_v` at every place `v`, archimedean
places included.

`NumberFieldQuaternionicSpinKernelHasseStatement`: over a number field `F`, for `n ≥ 4`, a
nondegenerate `q`, a group scheme `G` with `π : G ⟶ σ.isometryGroup q` and
`σ.IsSpinCover q π`, and a finite Galois extension `L/F`, every cocycle
`α : Cocycle (kernel π) (GaloisCocycle.cover F L)` whose image `α.map (kernelι π)` in `G`
is locally trivial has trivial image `α.map (kernelι π)` in `G`. Here `kernel π` is the
full scheme-theoretic kernel of `π`. It equals the kernel of the central isogeny onto the
identity component `O(q)⁰` supplied by `IsSpinCover`; geometrically it is the central
subgroup `μ₂` of the double cover `Spin → SU`. So the statement concerns the classes
coming from `H¹(F, μ₂)` in the exact sequence of the double cover.

## Sources

Let `h` be a nondegenerate skew-hermitian form over a quaternion division algebra over a
field `K`, `U` its unitary group, `SU` its special unitary group and `Spin` its spin group.
Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), §5.11, printed p. 101
(PDF p. 107), writes the cohomology sequence of `1 → μ₂ → Spin → SU → 1` (his sequence
(4)). He states that over a number field the map `H¹(K, SU) → ∏_v H¹(K_v, SU)` is
injective, "as in the case of quadratic forms". The first Hasse statement is the
trivial-kernel part of that injectivity, for cocycles split by a finite Galois extension
inside the scheme-theoretic norm-one group. The second statement is the part of the
injectivity of `H¹(K, Spin) → ∏_v H¹(K_v, Spin)` (Kneser, §5.10, printed pp. 95–98, PDF
pp. 101–104) that concerns the image of `H¹(K, μ₂)`.

## The reduction theorem

`numberFieldQuaternionicSpinHasse_of_kernels` proves
`NumberFieldQuaternionicSpinHasseStatement` from the two statements. Let `ξ` be a
locally trivial cocycle of a spin cover `π : G ⟶ O(q)` on a finite Galois cover, and let
`p : G ⟶ O(q)⁰` be the central isogeny with `p ≫ identityComponentι = π` supplied by
`IsSpinCover`.

1. `Quaternionic.FirstKindInvolution.connectedIsometryIsoNormOne` identifies `O(q)⁰` with
   the norm-one group. The reduced norm restricted to `O(q)⁰` and composed with `p` is a
   character of the semisimple group `G`. Semisimple groups are perfect
   (`semisimplePerfect`), so this character is trivial. The central isogeny `p` is flat and
   surjective, hence an epimorphism, so the reduced norm is already trivial on `O(q)⁰`. The
   inclusion of `O(q)⁰` therefore factors through the norm-one group. The norm-one group
   is connected (`quaternionicNormOneIsometryConnectedness`), so its inclusion factors
   through the identity component. The two factorizations are inverse isomorphisms.
2. The image of `ξ` under `p` followed by this isomorphism is a locally trivial cocycle of
   the norm-one group (`LocallyTrivial.map`), hence trivial by the norm-one Hasse
   statement.
3. `Cocycle.isTrivial_of_kernelHasse` takes a central isogeny `p` and a locally trivial
   cocycle whose image under `p` is trivial. It lifts the trivializing point through `p`
   after a finite Galois refinement (`IsCentralIsogeny.exists_finiteGalois_coefficient_lifts`)
   and twists the refined cocycle into the kernel (`Cocycle.kernelTwist`). The twisted
   cocycle is locally trivial in the source, because it differs from the refined cocycle by
   the lifted point. If every such kernel cocycle is trivial in the source, the twisted
   cocycle is trivial. Then the refined cocycle is trivial, and fpqc descent along the
   refinement (`Cocycle.IsTrivial.of_refine_fpqcCover`) gives triviality on the original
   cover. This is the argument of the scalar spin reduction in
   `Langlands.GroupScheme.Rational.NumberFieldScalarSpinHasseReduction`.
4. The kernels of the composite central isogeny and of `π` are identified, compatibly with
   their inclusions in `G`, by two instances of `kernelPostcompIso`, one for the
   isomorphism and one for the monomorphism `identityComponentι`. The central spin
   statement then supplies the kernel hypothesis of step 3.
