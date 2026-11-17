# Finite-type factorization of morphisms from affine schemes

This is a derived interface for the finite-type approximation step in the
construction of common affine neighbourhoods in
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §6.4 Lemma 4.
It specializes published affine-limit and subalgebra-stage constructions;
it does not transcribe a separately numbered result from that source.

Let `R` and `A` be commutative rings in any universe, with an `R`-algebra
structure on `A`. Let `p : X ⟶ Spec R` be locally of finite presentation.
For an `R`-morphism `f : Spec A ⟶ X` and a finite subset `s` of `A`,
`exists_fg_subalgebra_morphism_factorization` produces a finitely
generated `R`-subalgebra `T` containing `s`, and a morphism
`g : Spec T ⟶ X` over `Spec R`. It proves the equation
`Spec.map T.val.toRingHom ≫ g = f`.

`FiniteTypeAffineFactorization` packages this subalgebra, its finite
generation, the finite-subset containment, the morphism, the factorization
equation and its equation over the base.
`finiteTypeAffineFactorization` constructs that data from the hypotheses.
The base ring need not be noetherian; the hypothesis here is local finite
presentation rather than local finite type.

The proof indexes all finitely generated `R`-subalgebras containing `s`.
This index is nonempty and directed under inclusion, and its union is
`A`. The published `SubalgebraStages.specCone` limit result identifies
`Spec A` as the inverse limit of their affine spectra. Mathlib's
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` then factors
the morphism through one stage and supplies its base equation. Every
stage is affine, so the compactness, quasi-separatedness and affine
transition hypotheses of the limit theorem hold.
