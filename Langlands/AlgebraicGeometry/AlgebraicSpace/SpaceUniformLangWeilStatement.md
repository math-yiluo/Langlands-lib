# A uniform Lang–Weil estimate for smooth families of algebraic spaces over the integers

Author: Worker 208.

`SpaceUniformLangWeilStatement` states the algebraic-space form of Lemma 4.6 of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011). The registered source
is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only states the
result and contains no proof.

In the proof of Theorem 5.9 (printed p.17) Conrad writes: "The argument for the scheme case
carries over except for the step of checking surjectivity at the level of rational points over
the finite residue fields at all but finitely many places. For this we just need Lemma 4.6 to
be valid for algebraic spaces of finite presentation over Z." Lemma 4.6 (printed p.12) reads:
"Let `f : Y → B` be a smooth separated surjective map between finite type `Z`-schemes such that
the fibers are geometrically connected of dimension `d`. There is a constant `C > 0` such that
for all closed points `b ∈ B`, (4.6.1) `|#Y_b(k(b)) − q_b^d| ≤ C q_b^{d−1/2}`, where
`q_b = #k(b)`." Conrad sketches the space case on p.17: étale cohomology, the trace formula
and Deligne's Riemann Hypothesis [Del1, Thm. 3.3.1] carry over to separated algebraic spaces of
finite type over a finite field through stratifications by schemes. The scheme form is
`Langlands.AlgebraicGeometry.UniformLangWeilStatement`.

## The statement

The algebraic spaces, their presheaves and `hom f` are those of
`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`; the base is `Spec (ULift ℤ)`, Mathlib's
terminal scheme in the universe `u`. Let `B` and `Y` be algebraic spaces over it, `f : Y ⟶ B`
and `d : ℕ`. Assume:

- `B` is quasi-separated (`IsQuasiSeparated`) and of finite type over `ℤ`
  (`FiniteTypeOverRing (ULift ℤ) B`: a surjective étale atlas by a scheme that is locally of
  finite type and quasi-compact over `Spec ℤ`);
- `f` is smooth of relative dimension `d`: there are schemes `U` and `V` over `Spec ℤ`, an étale
  surjective `a : h_U ⟶ Y`, an étale `b : h_V ⟶ B` and a scheme morphism `φ : U ⟶ V` with
  `SmoothOfRelativeDimension d φ.left` (Mathlib) and `a ≫ hom f = h_φ ≫ b`;
- `f` is separated, quasi-compact and surjective (`IsSeparatedMorphism`,
  `IsQuasiCompactMorphism`, `IsSurjectiveMorphism`);
- `f` has geometrically connected fibres (`HasGeometricallyConnectedFibres`).

These properties are those of `Langlands/AlgebraicGeometry/AlgebraicSpace/SpaceMorphismProperties.lean`.
Then there is a real `C > 0` such that for every finite field `κ : Type u` (with its unique
`ℤ`-algebra structure) and every `κ`-point `x : RingPoints (ULift ℤ) B κ`,
`|N_x − (#κ) ^ d| ≤ C · (#κ) ^ (d − 1/2)` in `ℝ`. Here `#κ = Nat.card κ`, and `N_x` is `Nat.card`
of the `κ`-points `y : RingPoints (ULift ℤ) Y κ` with `RingPoints.map f y = x`, the rational
points of the fibre of `f` over `x`. The power `(#κ) ^ (d − 1/2)` is the real power.

## Relation to the source and derived content

"Finite presentation over `Z`" for `B` is quasi-separated and of finite type, since `ℤ` is
noetherian. `Y` is then of finite presentation over `ℤ` because `f` is separated and of finite
type. "The fibers are geometrically connected of dimension `d`" is formalized by geometric
connectedness of the fibres together with relative dimension `d` of a smooth chart square. For
a smooth morphism this is the same as pure dimension `d` of every fibre: the relative dimension
of a smooth chart map at a point is the local dimension of the fibre there, and étale maps
preserve local dimension. This avoids a dimension theory of algebraic spaces, which the Library
does not have. The relative-dimension square implies `IsSmoothMorphism f`.

Conrad's Lemma 4.6 counts rational points over the residue field of each closed point `b`. For
algebraic spaces the statement here counts instead the `κ`-points over every `κ`-point of `B`,
for every finite field `κ`. For a scheme `B` and a closed point `b`, the canonical
`κ(b)`-point gives Conrad's count. The stronger form is what Deligne's argument gives directly,
since it bounds each fibre over a finite field by Betti numbers that are bounded uniformly over
`B`. It is also the form the proof of Theorem 5.9 uses: there the base is a model over a ring
of `S`-integers, and the residue field at a place `v` is the field of definition of the point.

The name of the statement is chosen here. The cohomological input of Conrad's argument
(étale cohomology of algebraic spaces, the trace formula, constructibility and Deligne's
bounds) is not formalized. The statement is an open obligation of the Conrad formalization,
like its scheme form.
