# Proof of the real-controlled reduction to a quadratic opposite-Borel torus

`Langlands.GroupScheme.numberFieldQuadraticOppositeBorelTorus` proves
`NumberFieldQuadraticOppositeBorelTorusStatement.{u}` with its given hypotheses.

Let `G` be semisimple over the number field `F`, and let `Q/F` be a
quadratic Galois extension over which `G` is quasi-split. A semisimple
group is connected reductive. The theorem `exists_quadraticOppositeBorelTorus`
(module `Rational/QuadraticOppositeBorelExistence`) then gives a maximal
torus `t : T ⟶ G` over `F` with `IsQuadraticOppositeBorelTorus Q t`. This
means that `T_Q = B ∩ σ(B)` for a geometric Borel subgroup `B` of `G_Q`
and the nonidentity automorphism `σ` of `Q/F`.

For this one torus, the theorem
`IsQuadraticOppositeBorelTorus.exists_realLocallyTrivialRepresentative`
(module `Rational/QuadraticOppositeBorelRealControl`) takes a cocycle `ξ`
of `G` on the cover `Spec Q → Spec F`, trivial on the full pullback at
every real place. It returns a cocycle `δ` of `T` on the same cover with
`δ.map t` cohomologous to `ξ` and `δ` again trivial at every real place.
Its proof puts a twisted value of `ξ` in the open cell `U · T_Q · U⁻` of
the Borel pair. The middle coordinate of that value is a torus cocycle.
Weak approximation at the complex places of `Q` above real places of `F`
controls this coordinate locally, and at a real place of `F` with a real
place of `Q` above it the pullback cover has a section.

The completion `Global.placeCompletion F (.inl w)` of the statement is by
definition the completion `w.Completion` used by that theorem, so its
hypothesis and conclusion apply without change. The proof does not use
that `Q` is totally imaginary.

This follows V. Platonov and A. Rapinchuk, *Algebraic Groups and Number
Theory* (1994), Lemma 6.17, printed pp. 329–330, for the torus, and
Lemma 6.28, printed pp. 369–370, for the reduction of cocycles. The
registered source is `platonov-rapinchuk-1994-algebraic-groups-number-theory`
with SHA-256
`c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`.
