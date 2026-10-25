# Pointed pullback of invariant actual Tate-frame orbits

This is an internal construction from `AdelicFrameBaseChange`, the actual finite
étale fundamental-group pullback, and the published proposition
`RationalMonodromyBaseChange`. The latter remains an explicit argument `hbc`.
This file proves the resulting conditional construction and its compatibility
laws; it does not prove that proposition. It supplies the pointed pullback part
of the ambient frame-orbit infrastructure used toward PEL level structures.

## Generic fixed-orbit pullback

Let `G`, `Γ`, and `Δ` be groups, with right `G`-actions on `X` and `Y`, left
`Γ`- and `Δ`-actions respectively, and commuting left and right actions on each
space. Let `α : Γ →* Δ` and let `e : X ≃ Y` commute with the right actions and
satisfy `e (γ • x) = α γ • e x`. For every subgroup `U` of `G`,
`InvariantOrbit.pullback` maps the `Δ`-fixed classes in `Y/U` to the `Γ`-fixed
classes in `X/U`. Its underlying map is the inverse of `RightOrbit.equiv U e`.
Thus the construction acts on fixed quotient classes, without requiring a fixed
representative of a class.

To prove invariance, apply the injective forward orbit equivalence to the desired
identity and use equivariance and the old class's invariance under `α γ`.
`pullback_val` identifies the underlying inverse equivalence, and
`pullback_injective` follows from its injectivity and subtype extensionality.
Neither surjectivity of `α` nor surjectivity on the fixed subsets is asserted.

For subgroups `U` and `U'`, a translator `g` satisfying
`g⁻¹ * u * g ∈ U'` for all `u ∈ U` defines the map from `U`-orbits to
`U'`-orbits by right multiplication by `g`. `pullback_translate` proves that
pullback commutes with this map. Its proof applies the forward orbit equivalence
and uses the published `RightOrbit.map_translate` square.

## Actual full Tate frames

Take an actual base morphism `b : S' ⟶ S`, an abelian scheme `A/S`, a
field-valued point `t` of `S'`, a rational algebra `D` acting through
`i : D →ₐ[ℚ] End0 A`, and a source module `V` over
`D ⊗[ℚ] Global.FiniteAdeles ℚ`. The right action is supplied by a representation
`ρ` of `G` on `V`. The same full scalar comparison `h` is used at both endpoints.

The actual pulled-back endomorphism action is
`(AbelianScheme.rationalBaseChangeEnd b A).comp i`. The frame equivalence is
`adelicFrameBaseChange b A h i V t`, from frames of the pullback at `t` to
frames of `A` at `t ≫ b`. The group homomorphism is the actual
`fundamentalGroupMap b t (t ≫ b) rfl ht hs`, from the fundamental group of `S'`
to that of `S`. `adelicFrameBaseChange_monodromy` proves its left equivariance
by evaluating a frame on a vector and applying `hbc` to that rational Tate
vector. Right equivariance is the existing `adelicFrameBaseChange_right`.

`adelicFrameOrbitPullback` consequently maps fixed full frame-orbit classes of
`A` to fixed classes of its pullback. The lemmas with suffixes `_val`,
`_injective`, `_translate`, and `_forget` identify its underlying inverse
`adelicFrameRightOrbitBaseChange`, prove injectivity, and prove compatibility
with the existing actual level-translation and level-forgetting maps. Forgetting
is the translator `1` for an inclusion `U ≤ U'`.

## Prime-to-modulus frames and hypotheses

The declarations with prefix `primeToAdelicFrame` implement the same construction
for every natural modulus `m`, selecting orders `n` with `Nat.Coprime n m` before
rationalization. They use the module over
`D ⊗[ℚ] Global.PrimeToFiniteAdeles m`, with one common full comparison `h` and
its coupled `hAway : PrimeToRationalProfiniteIntegerAdeleComparison h m` at both
endpoints. No independence from changing these witnesses is claimed. The
underlying inverse orbit comparison is `primeToAdelicFrameRightOrbitBaseChange`.
The proofs are the same specialization of generic fixed-orbit pullback.

Both versions retain finite-fibre witnesses `ht` and `hs`, the named
`TorsionFiniteEtaleStatement`, and invertibility of all retained positive torsion
orders on each of `S` and `S'`. These are conditional geometric inputs. The
field is not required to be algebraically closed by this interface. Connectedness
and local noetherianness are not needed for this conditional pointed construction.

These are ambient tensor-linear frame orbits. This unit imposes no Weil-pairing
or similitude condition, chooses no Tate-twist trivialization, and makes no
canonical unpointed-functor claim. Identity and composite base changes are not
proved on the fixed subsets in this unit. Its provenance is the explicit generic
quotient argument specialized to the existing actual Tate and finite étale
constructions; no new literature theorem is attributed to a source.
