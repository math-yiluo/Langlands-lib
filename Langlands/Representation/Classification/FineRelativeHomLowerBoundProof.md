# Algebraic lower bound for the actual relative Hom spaces: proof

Authors: Workers 526, 359, 435, 845 and 1127. Worker 359 supplied the
original nonzero-map argument used by the imported injection proof, and
Worker 526 implemented its actual surjection transport and this assembly.
The private Hom transport constructions follow the published
quotient-detection proof of Workers 845, 526 and 435 and originated in
Worker 435's assembly draft. Worker 1127 adapted the draft for submission,
removing an unneeded heartbeat option and revising this explanation. The
imported injection theorem is by Worker 796, with Workers 526 and 359 as
coauthors. Imported published results retain their own provenance.

`Langlands.fineRelativeHomLowerBound` proves exactly the published
`Langlands.FineRelativeHomLowerBoundStatement.{uF,uV,uW,uZ}`. The field,
fine, coarse and ambient carrier universes are independent. The statement
and all its imports are used unchanged. This is an internal algebraic
deduction, not a literal theorem of Silberger or another source.

## Data

Fix the data of the statement: positive ambient rank `n`, a shape `B` with
refinement `S`, an irreducible cuspidal fine representation `ω` (carrier
universe `uV`), arbitrary fine and coarse real vectors `v₀,t`, an
irreducible admissible coarse representation `π` (universe `uW`), and a
nontrivial ambient representation `J` (universe `uZ`) with an actual
surjection `q` from the outer induction of the coarse twist of `π` by
`t`. Write `τ_s := fineTwist T B S ω v₀ s`, and

```text
α := Rep.of (T.leviRealPowerTwist (B.flatten S)
       (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ),
```

the twist of `ω` on the flattened product Levi, so that `τ_t` is `α`
pulled back along the inverse of
`e := Geometric.flattenedLeviEquiv F.Carrier B S`.

## Admissibility and finite dimensionality

The public `Langlands.relativeCosocleAdmissibility`, at universes
`{uF, uW, uZ}`, makes `J` admissible: its third clause applies to the
admissible `π`, the vector `t`, and the surjection `q`. No irreducibility
or admissibility hypothesis on `J` is added.

Two instances of the public `Langlands.fineOppositeJacquetHomFinite`, at
universes `{uF, uV, uW, uZ}`, give finite dimensionality. Its second
clause at parameter `t`, applied to the admissible `J`, gives `Hout`, the
fine Hom from `τ_t` into the normalized composed opposite Jacquet module of
`J` itself. Its first clause at parameter `0`, applied to `π`, gives
`Hin`, the fine Hom from `τ_0` into the normalized refined opposite Jacquet
module of `π`.

The public `Langlands.fineTwistIrreducibleAdmissible` gives two further
admissibility facts. At parameter `0` its second conjunct makes `τ_0`
admissible. At parameter `t` its third conjunct says that `α` is
Levi-cuspidal, and the admissibility component of that conjunction makes
`α` admissible.

## The injection `Hin → Hout`

Both second-adjointness instances come from the public
`Langlands.Parabolic.normalizedSecondAdjointness`. Its three universe
parameters are, in order, those of the field, of the representation being
induced, and of the target representation.

* The refined clause, instantiated at `{uF, uV, uW}` for `B` and `S`,
  gives a linear equivalence `Einner` from intertwiners
  `innerInduced T B S τ_0 → π` to `Hin`, applied to the admissible `τ_0`
  and `π`. Here `innerInduced` is the normalized refined induction
  `T.normalizedRefinedInduced B S`.
* The standard clause, instantiated at `{uF, uV, uZ}` for the flattened
  shape `B.flatten S`, applied to the admissible `α` and `J`, gives a
  linear equivalence from intertwiners
  `RelativeRecovery.fineAmbientInduced T B S ω v₀ t → J` to intertwiners
  from `α` into the standard opposite Jacquet module
  `CuspidalJacquetMultiplicity.oppositeJacquet T (B.flatten S) J`. The
  fine ambient induction is by definition the normalized upper induction
  of `α` along `B.flatten S`.

The positive-rank premise `0 < n` is exactly the one needed by both
clauses. Only the equivalences are used; the naturality clauses are
discarded.

To turn the second equivalence into one landing in `Hout`, the proof uses
the public `Langlands.Parabolic.flattenedOppositeJacquetComparison`,
instantiated at `{uF, uF, uZ}`; its first universe belongs only to the
unused ring-level subgroup identity. Its second clause applied to `J`
gives a representation equivalence `φ` between the normalized composed
opposite Jacquet module of `J`, pulled back along `e`, and the standard
opposite Jacquet module above. Two private linear equivalences then
transport the Hom space:

* `homPostcompEquiv α.ρ φ.symm` postcomposes intertwiners with `φ⁻¹`, and
  its inverse postcomposes with `φ`. Its inverse identities are those of
  `φ`.
* `homChangeGroup e α.ρ (T.normalizedComposedOppositeJacquet B S J.ρ)`
  keeps the underlying linear map and transports the intertwining equation
  along the group equivalence `e`. Its inverse uses `e⁻¹`. Its target is
  the Hom space from `α.ρ.comp e.symm`, which is `τ_t` by definition of
  `fineTwist`, so it is `Hout`.

Their composite with the standard equivalence is a linear equivalence
`Eambient` from intertwiners `fineAmbientInduced T B S ω v₀ t → J` to
`Hout`.

Between the two adjunction equivalences the proof uses the actual public
linear map

```text
C := RelativeHomComparison.fineAmbientHomMap T B S ω v₀ t hω π J q,
```

`f ↦ q ∘ i_P(f_t) ∘ E_flat⁻¹`, from intertwiners `innerInduced T B S τ_0 → π`
to intertwiners `fineAmbientInduced T B S ω v₀ t → J`. Its smoothness
premise `hω` on `ω` is the smoothness component of the admissibility
contained in the given cuspidality hypothesis. It is injective by the published
`Langlands.RelativeHomComparison.fineAmbientHomMapInjective`, applied to the
given irreducible `π`, nontrivial `J` and surjective `q`. The complete map
is

```text
Hin --Einner⁻¹--> Hom(innerInduced T B S τ_0, π)
    --C--> Hom(fineAmbientInduced T B S ω v₀ t, J) --Eambient--> Hout.
```

Each equivalence is injective, so their composite with `C` is injective
on the entire Hom space. With the two finite-dimensional instances already
proved, `LinearMap.finrank_le_finrank_of_injective` gives
`Module.finrank ℂ Hin ≤ Module.finrank ℂ Hout`.

## Conventions and scope

The actual carriers, residue-normalized determinant characters, negative
fine plus restricted positive coarse exponent, upper induction by right
translation with positive-half covariance, and inverse-half opposite
Jacquet normalizations are inherited from the unchanged public
constructions. There is no unitarity, temperedness, chamber, order,
middle-data, support, semisimplicity, finite-length, nonzero-Hom,
finite-dimensionality or chosen-equivalence premise. Both Hom spaces may
be zero. The proof uses no Jordan–Hölder count, unrestricted Silberger
Lemma 5.3, continuation argument or downstream classification.

This theorem supplies the finite-dimensional lower inequality. It does
not prove the reverse inequality, quotient reflection, analytic
continuation, whole-induction isolation, a relative cosocle theorem or the
parent exact relative comparison.
