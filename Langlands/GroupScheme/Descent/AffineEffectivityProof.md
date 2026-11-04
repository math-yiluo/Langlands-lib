# Proof of finite-Galois effective descent for affine group schemes

Author: Worker 1534.

This module proves the published proposition
`Langlands.GroupScheme.AffineGroupSchemeFiniteGaloisDescentStatement.{u}` from
`Langlands.GroupScheme.Descent.AffineEffectivityStatement`, in arbitrary
universe `u`. The main theorem is
`Langlands.GroupScheme.affineGroupSchemeFiniteGaloisDescent`. It is the pair of
the two component theorems below. The proof uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

The statement module is unchanged and is imported as is. The proof adds no
hypothesis, and in particular no smoothness, reducedness, finite-type,
commutativity or supplied-solution premise.

## Declarations

- `affineGroupSchemeFiniteGaloisObjectDescent` proves
  `AffineGroupSchemeFiniteGaloisObjectDescentStatement.{u}`.
- `affineGroupSchemeFiniteGaloisHomDescent` proves
  `AffineGroupSchemeFiniteGaloisHomDescentStatement.{u}`.
- `affineGroupSchemeFiniteGaloisDescent` proves their conjunction
  `AffineGroupSchemeFiniteGaloisDescentStatement.{u}`.

## Implemented proof

Both components first introduce the fields `k L : Type u`, their instances
and the actual morphism

```text
p : Spec L ⟶ Spec k := Spec.map (CommRingCat.ofHom (algebraMap k L)).
```

The published lemma `Langlands.GroupScheme.fieldExtension_fpqc k L` proves
that this exact morphism is surjective, flat and quasi-compact. The proof adds
these three facts to the local context, where instance search uses them.

### Object effectivity

Let `H : GroupScheme (Spec L)` satisfy `IsAffineHom H.X.hom`, and let
`datum : Descent.Datum p H` be an actual Čech datum. Mathlib's
`isAffine_of_isAffineHom` turns this premise into `IsAffine H.X.left`, because
the field spectrum `Spec L` is affine. Mathlib also provides the instances
`IsAffine (Spec L)` and `IsAffine (Spec k)`.

These are all the hypotheses of the published construction
`Langlands.GroupScheme.Descent.Datum.affineSolution` in
`Descent.AffineDatumGroup`: affine base and cover, an affine group scheme over
the cover, and a flat surjective cover map. It constructs a
`Descent.Solution datum` by faithfully flat affine descent. The solution
consists of a group scheme `solution.obj` over `Spec k`, an actual group-scheme
isomorphism `(baseChange p).obj solution.obj ≅ H`, and its compatibility with
`datum`. The published instance `Datum.affineSolution_isAffine` states that
`solution.obj.X.left` is affine. Mathlib's instance `isAffineHom_of_isAffine`
then proves `IsAffineHom solution.obj.X.hom`, since `Spec k` is affine. So
the object, its affineness and the compatible pullback isomorphism are all
constructed in the proof; none of them is an input.

### Homomorphism descent

Let `C D : GroupScheme (Spec k)` and let
`f : (baseChange p).obj C ⟶ (baseChange p).obj D` be compatible with the
canonical data of `C` and `D`. The published theorem
`Langlands.GroupScheme.Descent.FpqcHomDescent.existsUnique_hom` applies to any
flat, surjective and quasi-compact `p`. It gives exactly
`∃! g : C ⟶ D, (baseChange p).map g = f`. Its construction descends the
underlying scheme morphism through the fpqc effective epimorphism
`C ×_(Spec k) Spec L ⟶ C`. It then reflects the group-law equations along the
faithful pullback functor. The compatibility premise is an equation of actual
group-scheme morphisms over the double overlap, so every test scheme is
covered, including nonreduced ones. The two affineness premises of the
statement are not needed in this component.

## Hypotheses not used by the proof

The proof never uses `FiniteDimensional k L` or `IsGalois k L`. Both published
constructions need only that `p` is flat and surjective, plus quasi-compact for
homomorphisms. `fieldExtension_fpqc` proves these facts for every field
extension. The proof therefore shows the stated conjunction for all such `L/k`.
This is a remark about the proof; the theorem states only the published
finite-Galois target, and nothing stronger is claimed in Lean.

## Provenance and scope

The mathematical source of the statement is described in the Markdown of
`Descent.AffineEffectivityStatement`: Milne, *Algebraic Groups* (2017),
Appendix A.64, A.66 and A.81. The implemented route differs from that sketch.
It does not split `L ⊗[k] L` into Galois components and uses no semilinear
Galois action. It uses only the published faithfully flat affine descent and
fpqc homomorphism descent constructions named above.

This module supplies no cover datum and no universal-cover existence theorem.
It changes no file of `SimplyConnected.CoverExistenceStatement` or of any pair
it imports. Descending semisimplicity, simple connectedness or central-isogeny
properties remain separate obligations.
