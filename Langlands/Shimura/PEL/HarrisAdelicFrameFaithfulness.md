# Faithfulness of actual Harris actions witnessed by pointed adelic frames

This internal consequence of the constructed Harris source and actual
Tate-module action proves faithfulness in the pointed situation needed
for level pullback. It does not assume faithfulness survives an arbitrary
base change.

The arithmetic fields, algebra and schemes have universe zero. The
central simple Harris algebra is the actual `A` in
`CentralSimpleUnitaryData E F A n`, with signature charts `C`. The
source is the actual scalar extension of its regular module,
`Global.FiniteAdeles ℚ ⊗[ℚ] A`, with the existing tensor-algebra action.
For an actual abelian scheme `B/S`, the action
`i : A →ₐ[ℚ] End0 B` is an arbitrary actual unital rational algebra
homomorphism. An input frame is the existing tensor-algebra-linear
`Tate.AdelicFrame` from this source to the actual full rational Tate
module at the actual point `s : Spec Ω ⟶ S`. No pairing condition,
polarization, Lie chart or prior injectivity of `i` is assumed.

`rationalEnd_nontrivial_of_adelicFrame` proves that `End0 B` is
nontrivial. Simplicity supplies nontriviality of `A`, so the
nondegenerate constructed Harris trace form takes the value one
after finite-adelic scalar extension, by
`hodgeRationalPELConditions.baseChange_attains_one`. This supplies a
nonzero source vector `x`: if `x` were zero, the value-one equation
would give `0 = 1` in the actual finite adeles. Evaluating at the
existing finite place above `2` gives a contradiction in its actual
completion. This uses the published finite-place construction,
not an added nontriviality assumption on the finite adeles.
If the rational identity of `B` equalled
zero, the existing unital `Tate.rationalEndAction` evaluated on
`eta x` would imply `eta x = 0`. Injectivity of the actual linear
frame would imply `x = 0`, a contradiction.

`action_injective_of_adelicFrame` now applies the simple-ring theorem
that a unital ring homomorphism from a simple ring to a nontrivial
ring is injective. The simple ring is exactly the original Harris
algebra, and the map is exactly `i.toRingHom`; no Tate realization
faithfulness theorem is needed.
`adelicFrameActionEmbedding` bundles precisely `i` as an embedding;
its application formula is reflexivity.

For an actual base morphism `b : T ⟶ S` and an actual point
`t : Spec Ω ⟶ T`,
`action_baseChange_injective_of_adelicFrame` assumes an actual frame
for `B` at `t ≫ b`. It applies the inverse of the existing
`Tate.adelicFrameBaseChange` to obtain a frame of the actual changed
abelian scheme with action `(rationalBaseChangeEnd b B).comp i`,
then applies the preceding result. Thus the faithful map is the
actual pulled-back rational action. An original faithfulness
premise is unnecessary.
The theorem ending in `of_nonempty_adelicFrame` assumes only
`Nonempty` of that actual frame type and extracts a frame in the
proof, so the resulting injectivity assertion carries no chosen
frame as data.

The provenance is internal: the proof combines the constructed
nondegenerate Harris source form, the actual unital rational Tate
action, the existing pointed frame comparison, and the simple-ring
injectivity theorem. It proves no existence of an adelic frame or
satisfying abelian scheme. In particular the point and actual
frame hypotheses remain essential to this route; the theorem
does not assert faithful pullback over empty or arbitrary unpointed
bases. It supplies no preservation of the full polarization
predicate, mixed Tate-level square, quotient coherence,
representability or scheme level.
