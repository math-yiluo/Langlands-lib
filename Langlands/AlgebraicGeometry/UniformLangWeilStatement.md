# A uniform Lang–Weil estimate for smooth families over the integers

Author: Worker 105.

`UniformLangWeilStatement` states Lemma 4.6 of Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), printed p.12. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only states the
lemma and contains no proof.

Conrad writes: "Lemma 4.6. Let `f : Y → B` be a smooth separated surjective map between finite
type `Z`-schemes such that the fibers are geometrically connected of dimension `d`. There is a
constant `C > 0` such that for all closed points `b ∈ B`,
(4.6.1) `|#Y_b(k(b)) − q_b^d| ≤ C q_b^{d−1/2}`, where `q_b = #k(b)`." His proof cites Deligne's
Weil II [Del1, Cor. 3.3.3] applied to the constant sheaf `Q_ℓ`, through the
Grothendieck–Lefschetz trace formula and the weight bounds.

## The statement

All objects are Mathlib's. Let `B` and `Y` be schemes in an arbitrary universe `u`, `f : Y ⟶ B`
and `d : ℕ`. Assume:

- `B` is of finite type over `ℤ`: the unique map `specULiftZIsTerminal.from B` to
  `Spec (ULift ℤ)` is locally of finite type, and `B` is quasi-compact (`CompactSpace B`);
- `f` is smooth (`Smooth f`), separated, surjective, locally of finite type and quasi-compact;
- `f` is geometrically connected (`GeometricallyConnected f`: every base change to the
  spectrum of a field is connected);
- every fibre `f.fiber b` has pure dimension `d`
  (`SchemeFiberGeometry.HasPureDimension`, from `Langlands/AlgebraicGeometry/SchemeFiberGeometry.lean`:
  every irreducible component has Krull dimension `d`).

Then there is a real number `C > 0` such that for every closed point `b` of `B`,
`|N_b − q_b ^ d| ≤ C · q_b ^ (d − 1/2)` in `ℝ`. Here `q_b = Nat.card (B.residueField b)`, and
`N_b` is the number of rational points of the fibre: `Nat.card` of the sections
`s : Spec κ(b) ⟶ f.fiber b` of the structure map `f.fiberToSpecResidueField b`. The power
`q_b ^ (d − 1/2)` is the real power.

## Relation to the source and derived content

"Finite type `Z`-schemes" is formalized for `B`. `Y` is then of finite type over `ℤ` because `f`
is of finite type. "The fibers are geometrically connected of dimension `d`" is formalized by
Mathlib's `GeometricallyConnected` together with pure dimension `d` of every fibre. Smooth
connected fibres are irreducible, so for them this is the same as dimension `d`. Mathlib's
geometric connectedness also makes every fibre nonempty, which agrees with surjectivity. The
residue field of a closed point of a scheme of finite type over `ℤ` is finite, so `q_b` and
`N_b` are the actual cardinalities. Universe polymorphism uses `Spec (ULift ℤ)`, Mathlib's
terminal scheme in each universe.

The name of the statement is chosen here. The cohomological input of Conrad's proof (trace
formula, constructibility and Deligne's bounds) is not formalized.
