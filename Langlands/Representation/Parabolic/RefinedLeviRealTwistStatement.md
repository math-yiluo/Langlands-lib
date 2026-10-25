# Refined induction and coarse real-character twists

`Langlands.RefinedLeviRealTwistStatement` is an unproved proposition. It
specifies the restriction of an actual coarse block determinant character,
its compatibility with normalized refined induction on actual smooth
functions, and transport of every specified fine-to-coarse quotient map.

Fix a p-adic field `F`, its topological data `T`, an ordered block shape `B`,
a refinement `S`, a representation `ω` of the flattened Levi, fine real
parameters `v₀`, and coarse real parameters `t`. Put

- `χt = T.leviRealPowerCharacter B t`;
- `τt = RelativeJacquetMultiplicity.fineTwist T B S ω v₀ t`;
- `It = RelativeJacquetMultiplicity.innerInduced T B S τt`.

The fine twist has exponent
`-v₀ k + t ((B.flattenBlockEquiv S).symm k).1` on fine block `k`.
The first conjunct says that, for every element `q` of the actual refined
upper parabolic inside the coarse Levi, `χt q.val` equals the flattened
Levi determinant character with exponent
`t ((B.flattenBlockEquiv S).symm k).1`, evaluated on the inverse flattened
Levi equivalence applied to the actual refined Levi projection of `q`.
Thus the coarse exponent repeats on each fine block inside its parent.
The actual determinant absolute value uses the existing q-to-negative-valuation
convention.

The second conjunct supplies an actual equivariant complex linear equivalence
`E : (T.leviRealPowerTwist B t I0.ρ).Equiv It.ρ`. Here `I0` means `It` at
the zero coarse parameter, so the fine exponents in `I0` remain `-v₀`.
The same equivalence must satisfy both pointwise formulas

```text
(E f)(m)       = χt(m) • f(m),
(E.symm f)(m)  = χt(m)⁻¹ • f(m).
```

Evaluation is `Induction.eval` on the actual induced smooth-function
carriers. These functions have a uniform open right stabilizer; the
representation acts by right translation and its upper covariance uses the
canonical positive half-modulus. The assertion keeps these carriers and
normalization rather than replacing them by isomorphic abstract spaces.

Finally, for every representation `π` of the coarse Levi and every specified
surjective intertwiner `q₀ : I0.ρ.IntertwiningMap π.ρ`, the same `E` must give
a surjective intertwiner

```text
qₜ : It.ρ.IntertwiningMap (T.leviRealPowerTwist B t π.ρ)
```

with `qₜ(f) = q₀(E.symm f)` for every induced vector `f`. The assertion
therefore transports the given quotient map, with its actual underlying
function. It does not merely assert existence of an unrelated quotient.

The field, fine representation carrier, and quotient representation carrier
universes `uF`, `uV`, and `uW` are independent. The proposition includes every
rank, including zero, every ordered refinement, arbitrary real parameter
families, and arbitrary representations. It adds no smoothness,
irreducibility, admissibility, cuspidality, unitarity, analytic temperedness,
regularity, positive-root, or positive-rank premise. The induction
construction already takes smooth vectors even when the inducing
representation is arbitrary.

The original convention and twist compatibility are in Bernstein and
Zelevinsky, *Induced representations of reductive p-adic groups I* (1977),
§1.8(a), printed p.444, and Proposition 1.9(f), printed p.445. The ordered
block and refinement conventions for general linear groups are in §2.2,
printed p.446. These pages were read directly and the covariance and twist
formulas were inspected in the page images. The retained registered source
is `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
No source errata file was present in the supplied Library notes.

This exact coordinate formulation, both evaluation formulas, specified-map
transport, independent universes, arbitrary inputs, and rank-zero scope are
internal derived content. They are not attributed verbatim to that article.
A future proof can specialize the published
`Induction.smoothInductionTwistEquiv`: first establish the block determinant
restriction, then combine the restricted coarse character with the existing
negative fine character and commute the scalars with the positive
half-modulus. Twisting `q₀` and composing with `E.symm` gives the specified
map. The interface originated in Worker 373's shared proposition draft; the
present pair retains its entire type.

This module proves none of these assertions. It supplies neither support
existence nor analytic recovery, second adjointness, induction exactness,
induction in stages, or a Langlands classification theorem.
