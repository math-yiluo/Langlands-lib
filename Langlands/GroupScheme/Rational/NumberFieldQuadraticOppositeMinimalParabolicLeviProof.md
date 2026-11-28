# Proof of the real-controlled reduction to a quadratic opposite minimal parabolic Levi

`Langlands.GroupScheme.numberFieldQuadraticOppositeMinimalParabolicLevi` proves
`NumberFieldQuadraticOppositeMinimalParabolicLeviStatement.{u}` (module
[`NumberFieldQuadraticOppositeMinimalParabolicLevi`](NumberFieldQuadraticOppositeMinimalParabolicLevi.md))
with its given hypotheses.

Let `G` be semisimple over the number field `F` and `Q/F` a quadratic Galois extension. A
semisimple group is connected reductive, and a number field is infinite. The theorem
`exists_quadraticOppositeMinimalParabolicLevi` (module
[`QuadraticOppositeMinimalParabolicExistence`](QuadraticOppositeMinimalParabolicExistence.md))
gives a closed subgroup `t : C ⟶ G` over `F` with
`IsQuadraticOppositeMinimalParabolicLevi Q t`: `C_Q = P ∩ σ(P)` is a rational Levi subgroup of
a minimal parabolic subgroup `P` of `G_Q`, for the nonidentity automorphism `σ` of `Q/F`.

For this one subgroup,
`IsQuadraticOppositeMinimalParabolicLevi.exists_realLocallyTrivialRepresentative` (module
[`QuadraticOppositeMinimalParabolicRealControl`](QuadraticOppositeMinimalParabolicRealControl.md))
takes a cocycle `ξ` of `G` on `Spec Q → Spec F`, trivial on the full pullback at every real
place, and returns a cocycle `δ` of `C` on the same cover with `δ.map t` cohomologous to `ξ`
and `δ` again trivial at every real place. Its proof places a twisted value of `ξ` in the open
cell `U(χ) · C_Q · U(-χ)` of a cocharacter `χ` with `P = P(χ)` and `C_Q = Z(χ)`; the middle
coordinate is a cocycle of `C`, controlled at the real places by weak approximation and by an
open neighbourhood of `1` in `C(ℂ)` whose Galois cocycles are coboundaries.

The completion `Global.placeCompletion F (.inl w)` of the statement is by definition the
completion `w.Completion` used by that theorem. The proof does not use that `Q` is totally
imaginary.

This follows V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (1994),
Lemmas 6.17' and 6.28' (printed p. 383), whose proofs follow those of Lemma 6.17 (printed
pp. 329–330) and Lemma 6.28 (printed pp. 369–370). The registered source is
`platonov-rapinchuk-1994-algebraic-groups-number-theory` with SHA-256
`c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`.
