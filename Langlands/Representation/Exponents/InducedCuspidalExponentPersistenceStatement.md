# Persistence of cuspidal exponents of real-twisted inductions

Authors: Worker 960 and Worker 1041.

`Langlands.GLInducedCuspidalExponentPersistenceStatement` is one closed
Prop-valued definition. It is a statement only and supplies no proof. It is
an internal, derived `GL_n` consequence of the Bernstein–Zelevinsky
geometrical lemma (BZ 1977, 2.12 with Lemma 2.11, and the cuspidal-support
consequences in Theorem 2.9, Corollary 2.13 and step (1) of 2.14), extracted
for the parameter argument of Silberger 1978, Proposition 6.1, printed
pp.102–103. It is not the literal wording of a numbered theorem.

## Data

The prime `p`, actual `F : PadicField.{uF} p`, compatible topological data
`T` and positive rank `n` are arbitrary. A coarse ordered shape `B` has a
refinement `S`, with fine shape `C = B.flatten S`. The fine representation
`ω` on `C.Levi F.Carrier` (universe `uV`) is irreducible and
`CuspidalSupport.IsLeviCuspidal C`. The parameter `v : Fin C.length → ℝ`
is arbitrary; no positivity, unitarity or regularity is assumed.

The coarse representation `π` on `B.Levi F.Carrier` (universe `uW`) is
irreducible and receives an actual surjective intertwiner from

```lean
RelativeJacquetMultiplicity.innerInduced T B S
  (RelativeJacquetMultiplicity.fineTwist T B S ω v 0)
```

the existing normalized induction, inside the coarse Levi, of `ω` twisted by
the fine determinant parameter `-v` and pulled back along
`(Geometric.flattenedLeviEquiv F.Carrier B S).symm`. No temperedness or
square-integrability of `π` is assumed.

The coarse real parameter `t : Fin B.length → ℝ` is arbitrary. The
representation `RealTwistFamilies.induced T B π t` is the existing upper
normalized induction to `GL_n` of `π` twisted by `t`. A second shape `E`
(arbitrary, not required to equal `C`) carries a representation `τ`
(universe `uM`) that is `IsLeviCuspidal E` and is an actual opposite-Jacquet
class exponent along `E` of that induction:
`T.IsOppositeJacquetClassExponent E (RealTwistFamilies.induced T B π t) τ`,
that is, `τ` is irreducible, admissible and a quotient of an actual
subrepresentation of the lower-radical normalized opposite Jacquet module.

## Conclusion

There exist one permutation `s : Equiv.Perm (Fin n)` and one proof
`hs : CuspidalSupport.ConjugatesLevi (F := F.Carrier) C E s` such that, for
this same `s, hs`:

1. `τ` is equivalent to the inverse-conjugation transport along `s, hs` of
   `ω` twisted by `RealTwistFamilies.nestedParameter B S v t`, whose value at a
   fine index `k` is `-v k + t (block of k)`:

   ```lean
   Nonempty ((RealTwistFamilies.transported T B C E s hs ω
       (RealTwistFamilies.nestedParameter B S v) t).ρ.Equiv τ.ρ)
   ```

2. The same transport at the untwisted coarse parameter occurs in the
   untwisted outer induction of `π`:

   ```lean
   RealTwistFamilies.Occurs T B C E π s hs ω
     (RealTwistFamilies.nestedParameter B S v) 0
   ```

   Since `nestedParameter B S v 0 = -v` and `induced T B π 0` is the
   untwisted induction, this says that the transport of `ω` twisted by `-v`
   is itself an opposite-Jacquet class exponent along `E` of the induction
   of `π`.

## Why it is true

By exactness of normalized Jacquet functors and the BZ geometrical lemma,
the opposite Jacquet module along `E` of the induction of `π ⊗ χ_t` has a
finite filtration indexed by Weyl double cosets `w`, whose graded piece for
`w` is a normalized induction to `E.Levi` of the `w`-transport of a Jacquet
module of `π ⊗ χ_t`. (BZ state the lemma for standard upper parabolic
subgroups; the lower-radical Jacquet module along `E` is carried to an upper
one along the reversed shape by conjugation with the longest permutation.)
A cuspidal irreducible subquotient `τ` can only come
from a piece in which the inducing Levi is all of `E.Levi`, so `τ` is the
`w`-transport of a cuspidal subquotient `σ' ⊗ χ_t` of a Jacquet module of
`π ⊗ χ_t` along `w⁻¹ E w ⊆ B`. Because `χ_t` is a character of the coarse
Levi, the Jacquet module of `π ⊗ χ_t` is that of `π` twisted by `χ_t`. As
`π` is a quotient of the inner induction of `ω ⊗ ν^{-v}`, exactness and
BZ 2.13(c) inside the coarse Levi give `σ' ≅ w'(ω ⊗ ν^{-v})` for a block permutation `w'`
of `B`. Since `χ_t` is invariant under `w'`, with `s = w w'` one gets
clause 1. The same filtration piece, at the untwisted parameter, contains
`w(σ') ≅ s(ω ⊗ ν^{-v})` as a subquotient of the opposite Jacquet module of
the induction of `π`; this is clause 2.

The essential point is that clause 2 uses the label `s` coming from the
actual filtration piece responsible for `τ`. It is not deduced from mere
equivalence of the twisted transports, from pointwise finite spectra, or
from collisions of Weyl labels: a different `s'` with the same transport at
`t` need not occur at `0`. This target makes no almost-everywhere or
continuation claim and no claim about other labels or other parameters.

## Role

The statement is intended for the proof of the supported regular two-sided
Weyl and cone comparison, `GLSupportedRegularWeylConeComparisonStatement`: an outer
quotient `J` of the twisted induction of a tempered `π` has a cuspidal
opposite-Jacquet exponent, and persistence at `0` lets temperedness of the
untwisted induction bound its real part.

## Sources

- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
  reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472:
  2.12 (Geometrical Lemma) and Lemma 2.11, printed p.448; Theorem 2.9,
  printed p.448; Corollary 2.13 and step (1) of the proof 2.14, printed
  p.449 (cuspidal support of subquotients of inductions). Registered ID
  `bernstein-zelevinsky-1977-induced-i`.
- A. J. Silberger, *The Langlands quotient theorem for p-adic groups*, Math.
  Ann. 236 (1978), 95–104, proof of Proposition 6.1, printed pp.102–103.
  Registered ID
  `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`.
  Silberger's proof argues that every class exponent of the Langlands
  quotient is an analytic continuation of a class exponent of the inducing
  classes; this target does not state that continuation property and
  records only the pointwise persistence above, at the untwisted parameter.
