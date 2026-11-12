# Uniform fibre estimates and integral lifts with the original coefficient action

Author: Worker 109.

This internal adapter derives uniform original-coefficient fibre estimates
and actual integral lifts from the **explicit premise**
`SpaceUniformLangWeilStatement.{u}`. It does not prove that premise. It
composes the actual base-composition, fibre-cardinality and Henselian-lifting
constructions; no additional external literature assertion is claimed as
proved. All rings, schemes and fields retain arbitrary universe `u`.

The coefficient ring `C : Type u` is a commutative algebra over
`ULift.{u} ℤ`. The affine structure map
`Spec C ⟶ Spec (ULift ℤ)` is assumed locally of finite type. The target
space `B` over `Spec C` is quasi-separated and satisfies the arithmetic
atlas condition `FiniteTypeOverRing C B`. The morphism `f : Y ⟶ B` is
separated, quasi-compact and point-surjective and has geometrically
connected fibres. A supplied actual `EtaleMorphismChart f` has a separately
surjective source chart and a scheme map smooth of the fixed relative
dimension `d : ℕ`. These hypotheses, including fixed dimension, remain
explicit in all three declarations.

`exists_bound` composes the coefficient base with `Spec (ULift ℤ)`.
`quasiSeparated_space` and `finiteTypeOverRing_space` supply the target
hypotheses over the integers. The affine base map supplies its automatic
quasi-separatedness and quasi-compactness; local finite type is the explicit
assumption above. `morphismChart` retains the same underlying chart scheme
map and its smooth relative dimension. The composed morphism is separated,
quasi-compact, point-surjective and has geometrically connected fibres by
the corresponding base-composition transport lemmas. Thus the assumed
integer-base estimate applies to actual composed algebraic spaces, giving
one positive real constant before any finite field is chosen.

For an arbitrary finite field `κ : Type u` and arbitrary original algebra
action `C → κ`, the proof equips `κ` with the composite `ULift ℤ`-action.
The scalar-tower equation is proved from that composite. It imposes no
extra choice or condition on the original `C`-action. `ringPointLift` sends
the original target point to a point of the composed target, and
`card_ringPointFibre` identifies its actual composed source fibre with the
original fibre retaining that action. Hence the same constant `c > 0`
satisfies

`|Nat.card(fibre at x) - (Nat.card κ)^d| ≤ c * (Nat.card κ)^(d - 1/2)`

for every such finite field, action and target point. The constant depends
on the given family and chart, and is chosen before all those data.

`exists_uniform_surjectivity` reconstructs original smoothness from the
supplied chart. It applies the published
`UniformLangWeilHenselianLifts.surjective_of_bound` with the bound just
obtained. The result is one positive constant giving surjectivity on
original `C`-relative `R`-points for every Henselian local ring `R`, every
finite-field quotient `φ : R →ₐ[C] κ` that is surjective, and every
cardinality satisfying `c^2 < Nat.card κ`. The original actions on both
rings and their quotient compatibility are retained. No topology on the
coefficient rings or on those point sets is needed.

`pointLifts` uses classical choice on this uniform surjectivity conclusion
to package the positive constant and an actual original-coefficient source
point above every integral target point under the same hypotheses. Its
returned subtype includes the exact original fibre equation. The constant
is chosen before the local ring, residue field, algebra actions, quotient
map and target point.

The exact Lang-Weil premise, the fixed-dimensional chart and the family
hypotheses are not discharged by this module. Spreading a generic map,
handling varying fibre dimensions, and the adelic-topology assembly remain
separate obligations. The unchanged unconditional adelic smooth-openness
target is not proved here.
