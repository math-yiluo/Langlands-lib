# Pointed maps on invariant Tate-frame orbits

This module specializes the published constructions in
`PointedFrameOrbitPullback` and `PointedFrameOrbitCoherence` using the rational
conjunct `pointedMonodromyBaseChange.2.2` of the proved pointed-monodromy
theorem. Its two maps and their laws have no supplied
`RationalMonodromyBaseChange` argument. This is an internal derived construction:
all mathematical work is imported by Lean name, and the definitions supply the
proved equivariance to the existing fixed-orbit construction.

## Maps and retained inputs

For a base morphism `b : S' ⟶ S`, an abelian scheme `A/S`, and a field-valued
point `t` of `S'`, `adelicFrameOrbitPullbackMap` maps monodromy-fixed full
Tate-frame orbit classes of `A` at `t ≫ b` to those of its actual pullback
at `t`. The pulled-back algebra action is
`(AbelianScheme.rationalBaseChangeEnd b A).comp i`. The map on the underlying
right-orbit sets is the inverse of `adelicFrameRightOrbitBaseChange`.
Invariance follows from the proved equivariance along the actual
`fundamentalGroupMap b t (t ≫ b) rfl ht hs`. This construction uses fixed
quotient classes; it does not require a fixed representative.

`primeToAdelicFrameOrbitPullbackMap` gives the same map for a natural modulus
`m`, selecting positive orders coprime to `m` before rationalization. The full
version uses `D ⊗[ℚ] Global.FiniteAdeles ℚ`; the prime-to-modulus version uses
`D ⊗[ℚ] Global.PrimeToFiniteAdeles m`. Both use a specified rational algebra
action `i` on `A`, a source module `V`, and a group representation `ρ` defining
the right action. They apply to every subgroup `U` of that group.

Both maps retain finite-fibre witnesses on the two bases, the proposition
`TorsionFiniteEtaleStatement`, and invertibility on each base of every retained
positive torsion order. They use one common full scalar comparison `h` at both
endpoints; the prime-to-modulus map additionally uses its coupled `hAway`.
These geometric and scalar inputs have not been discharged. The field is
arbitrary; this formal pointed compatibility requires no additional
algebraic-closedness, connectedness or local-noetherianness assumption.

## Compatibility laws

For each map, `_val` identifies the underlying inverse orbit equivalence and
`_injective` proves injectivity. `_translate` proves compatibility with the
right translator `g`, under the condition `g⁻¹ * u * g ∈ U'` for every
`u ∈ U`. `_forget` gives the corresponding square for `U ≤ U'`.

The `_id` theorem compares pullback along the identity with equality transport
of the field-valued point after applying the actual identity base-change
comparison for the abelian scheme. The `_comp` theorem compares direct
pullback along `c ≫ b`, followed by the actual comparison from direct to
successive abelian-scheme pullback, with pullback first along `b` and then
along `c`. Its direct side includes the inverse point-equality transport
arising from associativity. It retains all fibre-finiteness witnesses and
invertibility inputs on the three bases.

Each proof applies the corresponding previously proved conditional law with
`pointedMonodromyBaseChange.2.2`. The new maps are abbreviations of the old
maps at this proof, so these applications establish the displayed identities
without a second quotient or monodromy construction.

## Scope and provenance

The source convention for the imported pointed-monodromy theorem is documented
in `PointedMonodromyBaseChangeStatement.md`: Edixhoven–van der Geer–Moonen,
*Abelian Varieties*, Chapter X (10.30), printed pages 151–152. This module adds
only the explicit specialization of that Library theorem to the existing
ambient frame-orbit maps and their coherence laws; it attributes no new
geometric theorem to the literature.

The objects are ambient tensor-linear frame orbits. This unit does not impose
the Weil-pairing similitude condition or choose a Tate-twist trivialization.
It does not prove surjectivity of the fundamental-group map or of the map on
fixed orbits, independence from scalar-comparison witnesses, or canonical
independence from the geometric base point. It therefore supplies pointed
frame-orbit functoriality, rather than a completed unpointed PEL level functor.
