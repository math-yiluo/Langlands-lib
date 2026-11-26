# Proof: uniqueness of ordinary polarized full-level data over a discrete valuation ring

The module `Langlands.AbelianScheme.PolarizedFiniteLevel.DiscreteValuationDatumUniquenessProof`
proves `DiscreteValuationDatumUniquenessStatement.{u}` as the theorem
`Langlands.AbelianScheme.PolarizedFiniteLevel.discreteValuationDatumUniqueness`.

Throughout, `R` is a domain with fraction field `K`, and
`ι = Spec.map (CommRingCat.ofHom (algebraMap R K)) : Spec K ⟶ Spec R`. From
`exists_abelianHom_extension` on, `R` is also a discrete valuation ring.

## Helpers

- `overHom_eq_of_genericFibre`. Let `Y` be flat over `Spec R` and `Z` separated
  over `Spec R`, and let `u w : Y ⟶ Z` be morphisms over `Spec R`. If
  `pullback.fst Y.hom ι ≫ u.left = pullback.fst Y.hom ι ≫ w.left`, then `u = w`.
  This follows from the Library's `genericFibre_map_injective` (module
  `Langlands.AbelianScheme.RelativeHomNeronExtension`). The two pulled-back
  morphisms are compared with `pullback.hom_ext`: the first components agree by
  the hypothesis and the second components agree automatically.
- `abelianHom_eq_of_baseChange`. Two homomorphisms `f f' : A ⟶ B` of abelian
  schemes over `Spec R` are equal if `(baseChange ι).map f = (baseChange ι).map f'`.
  Composing the hypothesis with `pullback.fst B.X.hom ι` gives the hypothesis of
  the previous helper for the underlying morphisms over `Spec R`. Abelian schemes
  are flat (smooth) and separated (proper). Then `Grp.hom_ext` gives equality of
  the group homomorphisms, and so of `f` and `f'`.
- `abelianSchemePropertyBundle_self`. An abelian scheme over `Spec R` satisfies
  FLT's `GoodReductionJacobian.AbelianSchemePropertyBundle`. Smoothness and
  properness are instances. Connected fibres come from
  `isConnected_preimage_singleton`. The group law is
  `GoodReductionJacobian.relativeGroupLawOfGrpObj` applied to the group-object
  structure of the abelian scheme.
- `exists_abelianHom_extension` (DVR). Every homomorphism
  `(baseChange ι).obj A ⟶ (baseChange ι).obj B` is `(baseChange ι).map φ` for some
  `φ : A ⟶ B`. This is the Library's `baseChange_map_surjective` (same module),
  applied to the underlying group schemes, with the property bundle of `B` from
  the previous helper.
- `exists_abelianIso_extension` (DVR). Every isomorphism `e` of the generic fibres
  is `(baseChange ι).map` of an isomorphism `A ≅ B`. Extend `e.hom` to `φ` and
  `e.inv` to `ψ`. The composites `φ ≫ ψ` and `ψ ≫ φ` have the same base change
  as the identities, because `baseChange ι` is a functor and `e` is an
  isomorphism. So they are identities by `abelianHom_eq_of_baseChange`.

## Main theorem

Let `a b : Datum P (Spec R) g d n` and let `e : PolarizedIso (a.pullback ι) (b.pullback ι)`.
By `exists_abelianIso_extension` applied to `e.abelianIso`, there is an
isomorphism `φ : a.abelian ≅ b.abelian` with `(baseChange ι).map φ.hom = e.abelianIso.hom`.
It remains to check the two conditions of `PolarizedIso` for `φ`.

1. Polarization. Both sides of
   `a.polarization = φ.hom ≫ b.polarization ≫ a.dualWitness.map P b.dualWitness φ.hom`
   are homomorphisms of abelian schemes over `Spec R`. By
   `abelianHom_eq_of_baseChange` it suffices to compare their base changes along
   `ι`. Compose both with the isomorphism `(a.dualWitness.baseChangeIso P ι _).hom`
   (cancelled by `cancel_mono`). The left side becomes the polarization of
   `a.pullback ι` (definition of `Datum.pullback`). Rewrite it with
   `e.polarization_eq`. Then the Library's `DualWitness.baseChangeIso_naturality`
   (module `PullbackCoherence`) and `(baseChange ι).map φ.hom = e.abelianIso.hom`
   identify both sides; the last step is definitional.
2. Level sections. Fix `i`. The Library's `pullbackTuple_map` (module
   `LevelCoherence`), with `(baseChange ι).map φ.hom = e.abelianIso.hom` and
   `e.level_eq i`, gives that the pulled-back tuples
   `pullbackTuple ι (mapTuple φ.hom a.level.sections)` and
   `pullbackTuple ι b.level.sections` agree at `i`. The Library's
   `pullbackTuple_fst` turns this into
   `ι ≫ x.left = ι ≫ y.left`, where `x` and `y` are the sections of `b.abelian`
   underlying `mapTuple φ.hom a.level.sections i` and `b.level.sections i`. By
   the Library's `GroupScheme.Tate.toSection_injective` (module
   `Langlands.AbelianScheme.Tate.Integral`: an `n`-torsion point is determined
   by its underlying section) it suffices to show `x = y` as morphisms over
   `Spec R` from `Over.mk (𝟙 (Spec R))`. This object is flat (the identity
   morphism of `Spec R` is flat) and `b.abelian` is separated, so
   `overHom_eq_of_genericFibre`
   reduces this to an equality after composing with
   `pullback.fst (𝟙 (Spec R)) ι`. By `pullback.condition` this first projection
   equals `pullback.snd (𝟙 (Spec R)) ι ≫ ι`. So the required equality follows
   from `ι ≫ x.left = ι ≫ y.left`.

The hypothesis `IsUnit (n : R)` of the statement is not used.

## Relation to the literature

The statement's Markdown derives it from Bosch–Lütkebohmert–Raynaud, *Néron
Models*, §1.2 Definition 1 and Proposition 8. The Lean proof follows the same
three steps. Extension of homomorphisms over a discrete valuation ring is the
Library's `baseChange_map_surjective`, and uniqueness of extensions is the
Library's `genericFibre_map_injective`. This proof does not use the Néron model
formalism itself.
