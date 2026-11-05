# Actual smooth affine models over finite S-integer rings

Worker 1572 authored this internal construction for simultaneous reductive and
parabolic spreading. It derives the result from published Library descent
proofs and Mathlib's actual S-integer subalgebras; it introduces no additional
geometric hypothesis or external source assertion.

For every number field `F : Type u` and supplied smooth affine group scheme
`G` over `Spec F`, `smoothIntegralModelData F G` chooses a finite set `S` of
finite places and an actual `IntegralModel R F G`, where
`R = (S : Set (FinitePlace F)).integer F`, whose structural map is smooth.
The model includes an affine, flat, locally finite type group scheme and a
group-scheme isomorphism from its actual generic fibre to the original `G`.
All rings and schemes remain in the arbitrary common universe `u`.

The implemented proof has the following steps.

1. `exists_integer_contains_finset` covers finitely many field coefficients by
   a finite union of sets of places, using
   `Langlands.Global.exists_mem_numberFieldSIntegers` and
   `numberFieldSIntegers_mono` from `AdelicSIntegersColimitProof`.
   `exists_integer_contains_subalgebra` applies `Algebra.adjoin_le` to a
   finite generating set over the actual ring of integers `𝓞 F`.
2. `exists_smoothIntegralModel` first invokes
   `AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation`
   with coefficient base `𝓞 F`. It gives an affine finitely presented scheme
   model over a finitely generated subalgebra `T₀` with an actual pullback
   square identifying its generic fibre with the underlying scheme of `G`.
3. `NoetherianApproximation.smoothSubalgebraDescent` enlarges to `T₁` so the
   pulled-back structural map is smooth. Pullback pasting supplies the
   pullback square required by `Langlands.GroupScheme.subalgebraDescent`,
   which then enlarges to `T₂`, descends the group law on that supplied
   underlying scheme, and returns a group-scheme isomorphism with `G` after
   base change. Smoothness and affineness are carried by these pullbacks.
4. Transitivity of finite type shows that `T₂` is finite type over `𝓞 F`.
   An explicit surjective algebra map to its restriction of scalars supplies
   the finite generation needed in step 1. The resulting containment in `R`
   defines the actual ring map `T₂ → R` by sending a field element to itself.
   Its composite with `R → F` is the original inclusion `T₂ → F`.
5. The final model is the actual group-scheme pullback from `T₂` to `R`.
   `baseChangeCompIso`, the literal composite equality of the ring maps, and
   the descended group isomorphism construct its `genericIso`. Pullback
   stability gives smoothness and affineness; smoothness supplies flatness
   and local finite type. Finally, classical choice packages this existence
   proof as `smoothIntegralModelData`.

This unit constructs one smooth affine model at a time. It does not yet
extend a supplied homomorphism, prove closed immersion, or establish
reductivity, parabolicity or connectedness of all field-valued fibres. These
remain obligations of the unchanged `ReductiveParabolicSpreading.ExistenceStatement`.
