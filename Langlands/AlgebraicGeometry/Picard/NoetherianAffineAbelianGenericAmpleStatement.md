# Generic ampleness on abelian schemes over noetherian affine domains

Author: Worker 1318.

`Langlands.AlgebraicGeometry.Picard.NoetherianAffineAbelianGenericAmpleStatement.{u}`
is a proposition with one universe parameter. It quantifies over every
noetherian commutative integral domain `R : Type u`, every actual Library
abelian scheme `A` over `Spec R`, and every actual line bundle `L` on its
total scheme. Its premise says that the pullback of `L` along the canonical
projection

```lean
pullback.fst A.X.hom
  (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
```

is ample. Its conclusion is `L.IsAmple` on `A.X.left`, for the Library's
absolute ampleness predicate. The fraction field is Mathlib's canonical
`FractionRing R`; the generic restriction is an actual sheaf pullback on
an actual scheme pullback.

No normality, finite type over the integers, polarization, dual scheme,
symmetry of `L`, or relative dimension is assumed. The base is affine and
integral, and the morphism is the smooth proper geometrically connected
structure morphism of an abelian scheme. This is a statement definition;
it proves neither the implication nor the existence of any line bundle.

## Source and derived formulation

G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties* (1990),
registered source
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
SHA-256 `f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`,
Chapter I, Remark 1.10(b), printed p.7 (PDF p.19), states that for an
invertible sheaf on an abelian algebraic space the fibrewise ample locus
is closed as well as open. The proof of Theorem 1.9, printed p.6 (PDF p.18),
uses fibrewise ampleness to conclude relative ampleness. Worker 1318 read
these pages of the registered copy. No source-specific errata note was
found in the current Library's `notes/errata/` directory.

The Lean proposition is a derived affine integral specialization, rather
than a verbatim statement from the book. The spectrum of a domain is
irreducible. Its closed fibrewise ample locus must be the whole spectrum
if it contains the generic point. Relative ampleness then gives absolute
ampleness over the affine base, the usual affine-base interpretation of
relative ampleness. This paragraph explains why the target is
mathematically appropriate; the module does not implement that argument.
An actual proof must supply the specialization and globalization steps.
In particular, openness alone would only give ampleness over an open
neighbourhood of the generic point.

## Intended use

`NormalFiniteTypeAbelianAmpleExistenceReduction` combines this proposition
with the separately defined
`Langlands.AbelianScheme.NormalFiniteTypeTwoAxisExtensionProperty` and the
published field ample diagonal correspondence. The normal extension
input constructs a total line bundle with ample generic restriction;
the present criterion must still be proved to conclude total ampleness.
This criterion assumes that a total line bundle has already been supplied,
so it is distinct from existence of such a bundle over a normal base.
