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

## Status: an open obligation

The lemma is not proved in the Library. It is not an external input: the parent formalization
program of Conrad's paper keeps it as an open obligation that must be proved. The proof route
Conrad cites is Deligne's weight theorem, *La conjecture de Weil. II* [Del1, Cor. 3.3.3]:
- registered source `deligne-1980-weil-ii`, SHA-256
  `99d3c62a83fd9fb41af17d165e4a63d7120a7edf3c5c4a409fa50f2e64b1cd20`;
- file `/home/taskhub/central-library/Deligne--La conjecture de Weil II--1980.pdf`;
- Corollaire 3.3.3 begins on printed p.205 (PDF p.69).

Corollaire 3.3.3 concerns a morphism `f : X → Y` of schemes of finite type over `Z` and an
integral sheaf `F` on `X` (*faisceau entier*) that is mixed of weights at most `n`. It states
that each higher direct image with proper supports `R^i f_! F` is mixed with weights between
`0` and `n + i`. When `i` exceeds the maximal fibre dimension `d`, the weights lie between
`2(i − d)` and `n + i`. The upper bound alone, without integrality, is Théorème 3.3.1 (printed
p.204). Conrad applies this to the constant sheaf `Q_ℓ`, which is integral and pure of weight
`0`. Together with the constructibility of the sheaves `R^i f_! Q_ℓ` and the
Grothendieck–Lefschetz trace formula, this gives (4.6.1). Another
possible route is the Lang–Weil estimate with bounds that are uniform in the degrees of the
fibres. Conrad's Theorem 5.9 needs the same estimate for algebraic spaces of finite
presentation over `Z`, which is stated separately.

