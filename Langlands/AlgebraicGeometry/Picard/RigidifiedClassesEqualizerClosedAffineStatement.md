# The agreement locus over an affine base with identity parameter

`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedAffineStatement.{u}` is the
proposition:

```lean
∀ (R : CommRingCat.{u}) (A : AbelianScheme (Spec R))
  (q r : RigidifiedClasses A (Over.mk (𝟙 (Spec R)))),
  ∃ (Z : Scheme.{u}) (ι : Z ⟶ Spec R), IsClosedImmersion ι ∧
    ∀ (T' : Over (Spec R)) (h : T' ⟶ Over.mk (𝟙 (Spec R))),
      (∃ g : T'.left ⟶ Z, g ≫ ι = h.left) ↔
        RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
            (unitSection_comp A) h q =
          RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
            (unitSection_comp A) h r
```

This unit only defines the proposition. It proves nothing.

## Meaning

Let `R` be a commutative ring and `A` an abelian scheme over `Spec R`. Take the parameter
object `T = Over.mk (𝟙 (Spec R))`, that is, `Spec R` over itself. For two rigidified
isomorphism classes `q` and `r` on the chosen total space `Spec R ×_{Spec R} A`, the
proposition gives a closed immersion `ι : Z ⟶ Spec R`. A morphism `h : T' ⟶ T` in
`Over (Spec R)` factors through `ι` exactly when the pullbacks of `q` and `r` to `T'` are
equal classes. So `Z` represents the subfunctor of `Spec R` on which the two classes agree.

## Relation to the general statement

This is the published
`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedStatement.{u}` with the base
`S = Spec R` and the parameter object `T = Over.mk (𝟙 (Spec R))`; then `T.left = Spec R`. All
other quantifiers, the conclusion and the universe are unchanged. The module records this with
an `example` deriving the present proposition from the general one by
`fun R A q r => h (Spec R) A (Over.mk (𝟙 (Spec R))) q r`. The converse, deriving the general
statement from this one, is the remaining reduction (base change along `T.hom` and gluing over
an affine open cover of `T.left`); it is not part of this unit.

## Exact interface

All names are the published ones from the imported module
`Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedStatement`; nothing is
redefined.

- `AbelianScheme (Spec R)`, `unitSection A` and `unitSection_comp A` are the published bundle,
  its identity point and the identity `unitSection A ≫ A.X.hom = 𝟙 (Spec R)`.
- `RigidifiedClasses A T` is the quotient by isomorphism of the actual category of line bundles
  on the chosen total space `T ×_{Spec R} A`, each rigidified along the section induced by the
  unit section.
- `RigidifiedLineBundle.classesPullback … h` is `Quotient.map` of the actual relative
  rigidified pullback functor along `h`.
- `IsClosedImmersion` is Mathlib's closed-immersion property.

The ring `R` is arbitrary: no noetherian or finiteness hypothesis. The classes `q` and `r`
are arbitrary; there is no Picard-zero condition. The test objects `T'` are arbitrary objects
of `Over (Spec R)`. `Z` lies in universe `u`.

## Provenance

Derived. It is the specialisation above of the published general statement, whose Markdown
derives it from the Stacks Project, *More on Morphisms*, Section 37.33, Lemma 37.33.1 (tag
0BDP, label `lemma-diagonal-picard-flat-proper`) and Lemma 37.33.4 (tag 0BF0, label
`lemma-get-a-closed`); registered source `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`,
commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, file `more-morphisms.tex`. Here those lemmas
are applied with the affine base `Spec R` to the structure morphism `A.X.hom` itself (via the
chosen total space over the identity object), with `E = L ⊗ M⁻¹` for representatives `L`, `M`
of `q`, `r`.

The affine specialisation is introduced as the cohomological core of the proof of the general
statement (task `e3d4a3ab-f378-42af-87c5-0cd4caec7b2e`): the remaining passage to arbitrary `S`
and `T` is formal.
