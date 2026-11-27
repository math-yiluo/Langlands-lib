# Evaluation after the equivariant change from étale to quasi-étale sheaves

`EquivariantQuasiEtaleObjectEvaluationStatement` gives the evaluation
clause of Berkovich's Corollary 1.4.3. For each equivariant quasi-étale
test object `f : U(G) → X(G)`, it asserts a natural isomorphism in the
étale module sheaf `F` on `X(G)`,

\[
\Gamma(U(G)_{\mathrm{ét}}, f^*F) \simeq (\mu^*F)(U(G)).
\]

The left-hand functor evaluates on the identity `U(G) → U(G)`, the
terminal object of the equivariant étale site over `U(G)`. The
right-hand functor evaluates the actual change-of-site inverse image
on the given test object of the equivariant compact-probe site. Both
functors take values in modules over the same commutative ring `R`.
The proposition uses Hausdorff analytic spaces over a fixed complete
ultrametric normed field with continuous actions by analytic
automorphisms. The open subgroup quotients fit in the geometric
universe, as in the unit clause of Corollary 1.4.3. The statement
expresses existence of the isomorphism natural in `F` at each `U(G)`.

The functor `equivariantEtaleBaseChangeInverseImage` is constructed by
left Kan extension along the opposite of the actual étale pullback of
test objects and sheafification. The pullback functor initially
allows different groups of operators and restricts the target action
along the group homomorphism of the given morphism. In the evaluation
clause this homomorphism is the identity of `G`.
The projection from each pulled-back étale test object gives a
pullback square for every morphism of test objects by pullback
cancellation. These squares show that base change preserves finite
limits, using the identity object for the terminal case. They also
show that base change preserves jointly surjective covering families,
by lifting pairs of points through analytic pullbacks of étale maps.
This gives continuity and the module sheaf adjunction used to form
the inverse image. The coefficient universe bounds both sites and
their morphism universes.

Berkovich's formula in §1.2 gives the inverse image by the colimit over
étale test objects followed by sheafification. Corollary 1.4.3 gives
the value on each quasi-étale object. Its comparison uses the
commuting square of the two changes of site with pullback to `U(G)`.
The unit comparison on `U(G)` identifies étale sections after
pullback, and restriction on the quasi-étale site evaluates on the
object `U(G) → X(G)`.

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*, §1.2,
printed and PDF p. 3, and Corollary 1.4.3, printed and PDF p. 10.
The retained PDF has SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`,
in registered folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
with SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
