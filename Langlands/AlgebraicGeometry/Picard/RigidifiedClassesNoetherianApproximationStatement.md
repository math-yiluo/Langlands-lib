# Noetherian approximation of the agreement of two rigidified classes

`Langlands.AbelianScheme.RigidifiedClassesNoetherianApproximationStatement.{u}` is the
proposition:

```lean
∀ (R : CommRingCat.{u}) (A : AbelianScheme (Spec R))
  (q r : RigidifiedClasses A (Over.mk (𝟙 (Spec R)))),
  ∃ (R₀ : CommRingCat.{u}) (_ : IsNoetherianRing R₀) (φ : R₀ ⟶ R)
    (A₀ : AbelianScheme (Spec R₀)) (q₀ r₀ : RigidifiedClasses A₀ (Over.mk (𝟙 (Spec R₀)))),
    ∀ (T' : Over (Spec R)) (h : T' ⟶ Over.mk (𝟙 (Spec R))),
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
          (unitSection_comp A) h q =
        RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
          (unitSection_comp A) h r ↔
      RigidifiedLineBundle.classesPullback A₀.X.hom (unitSection A₀)
          (unitSection_comp A₀)
          (Over.homMk (T'.hom ≫ Spec.map φ) :
            Over.mk (T'.hom ≫ Spec.map φ) ⟶ Over.mk (𝟙 (Spec R₀))) q₀ =
        RigidifiedLineBundle.classesPullback A₀.X.hom (unitSection A₀)
          (unitSection_comp A₀)
          (Over.homMk (T'.hom ≫ Spec.map φ) :
            Over.mk (T'.hom ≫ Spec.map φ) ⟶ Over.mk (𝟙 (Spec R₀))) r₀
```

This unit only defines the proposition. It proves nothing.

## Meaning

Let `R` be an arbitrary commutative ring, `A` an abelian scheme over `Spec R`, and `q`, `r` two
rigidified isomorphism classes on the chosen total space `Spec R ×_{Spec R} A` over the
identity object `Over.mk (𝟙 (Spec R))`. The proposition provides a noetherian commutative ring
`R₀` in the same universe, a ring map `φ : R₀ ⟶ R`, an abelian scheme `A₀` over `Spec R₀` and
two rigidified classes `q₀`, `r₀` over the identity object of `Spec R₀`, such that agreement is
detected over `R₀`. Every test object `T'` over `Spec R` is also an object
`Over.mk (T'.hom ≫ Spec.map φ)` over `Spec R₀`, with structure morphism
`Over.homMk (T'.hom ≫ Spec.map φ)` to the identity object of `Spec R₀`. The proposition says that
the pullbacks of `q` and `r` to `T'` are equal exactly when the pullbacks of `q₀` and `r₀` to
`T'`, viewed over `Spec R₀` in this way, are equal.

The proposition asks only for this agreement equivalence. It does not ask for an isomorphism
`A ≅ Spec R ×_{Spec R₀} A₀`, nor for `q` and `r` to be the base changes of `q₀` and `r₀`.
Those are the expected way to prove it: if `A`, `q` and `r` are base changes of `A₀`, `q₀` and
`r₀` along `Spec.map φ`, then for every `T'` the chosen total spaces
`T' ×_{Spec R} A` and `T' ×_{Spec R₀} A₀` are canonically isomorphic, compatibly with the unit
sections and the rigidified pullbacks, and the equivalence follows.

## Use

Together with the noetherian case
`RigidifiedClassesEqualizerClosedNoetherianAffineStatement` applied to `R₀`, `A₀`, `q₀`, `r₀`,
this proposition yields the affine statement `RigidifiedClassesEqualizerClosedAffineStatement`
(statement task `40213915-546f-4273-91e7-aff363d3ca2a`) by pulling the closed immersion
`Z₀ ⟶ Spec R₀` back along `Spec.map φ`. That derivation is not part of this unit.

## Exact interface

All names are the published ones from the imported module
`Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedStatement` and Mathlib;
nothing is redefined.

- `AbelianScheme (Spec R)`, `unitSection A` and `unitSection_comp A` are the published bundle,
  its identity point and the identity `unitSection A ≫ A.X.hom = 𝟙 (Spec R)`.
- `RigidifiedClasses A T` is the quotient by isomorphism of the actual category of line bundles
  on the chosen total space `T ×_{Spec R} A`, each rigidified along the section induced by the
  unit section.
- `RigidifiedLineBundle.classesPullback … h` is `Quotient.map` of the actual relative
  rigidified pullback functor along `h`.
- `IsNoetherianRing`, `Spec.map`, `Over.mk` and `Over.homMk` are Mathlib's.

The ring `R` is arbitrary: no noetherian or finiteness hypothesis. The classes `q` and `r` are
arbitrary; there is no Picard-zero condition. The test objects `T'` are arbitrary objects of
`Over (Spec R)`. `R₀` lies in universe `u`.

## Provenance

Derived. It is the standard noetherian-approximation step specialised to the agreement predicate
of the published general statement
`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedStatement.{u}`. The supporting results
are in the Stacks Project, Chapter 32 "Limits of Schemes", registered as
`stacks-limits-of-schemes-a04446e5` (file `limits.tex`, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`). Write `Spec R` as the limit of the spectra of the
finitely generated `ℤ`-subalgebras of `R`, which are noetherian (Section 32.5, tag 01Z1). Then:

- the finitely presented scheme `A`, its group-law morphisms and the identities between them
  descend to some stage (Lemma 32.10.1, tag 01ZM; Proposition 32.6.1, tag 01ZC);
- smoothness and properness descend (Lemma 32.8.9, tag 0C0C; Lemma 32.13.1, tag 081F);
- the line bundles representing `q` and `r`, and their rigidification isomorphisms, descend
  (Lemma 32.10.2, tag 01ZR; Lemma 32.10.3, tag 0B8W);
- geometric connectedness of the fibres holds after shrinking the stage to an open and closed
  part, since the number of geometric connected components of the fibres of a proper, flat,
  finitely presented morphism with geometrically reduced fibres is locally constant (Stacks
  Project, *More on Morphisms*, Section 37.53 "Stein factorization", tag 0E0N, label
  `lemma-proper-flat-geom-red` in `more-morphisms.tex`, registered
  `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`).

These references explain why the proposition should hold. The unit itself states only the
agreement equivalence above.

The approximation is introduced as one half of the cohomological core of the proof of the
general statement (task `e3d4a3ab-f378-42af-87c5-0cd4caec7b2e`), whose other half is the
noetherian case `RigidifiedClassesEqualizerClosedNoetherianAffineStatement`.
