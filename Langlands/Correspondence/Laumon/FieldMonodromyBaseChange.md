# Change of field for lisse monodromy

Let \(L/K\) be an extension of fields with separable closures \(\Omega_L\) and
\(\Omega_K\) and a \(K\)-embedding \(\iota\colon\Omega_K\to\Omega_L\).
`fieldMonodromyBaseChange` identifies the geometric stalk of a lisse
\(\overline{\mathbf Q}_\ell\)-sheaf on \(\operatorname{Spec}K\) with the
geometric stalk of its inverse image on \(\operatorname{Spec}L\).
`fieldMonodromyBaseChange_commutes` proves that it intertwines the actions of
automorphisms \(\sigma\in\operatorname{Gal}(\Omega_K/K)\) and
\(\tau\in\operatorname{Gal}(\Omega_L/L)\) satisfying
\(\iota\sigma=\tau\iota\).

The construction uses the geometric stalks and Galois action of
[`FieldMonodromy`](FieldMonodromy.md), which formalizes the fibre description
of Laumon (1987), (2.1.2)–(2.1.2.1). Extend \(\iota\) to the algebraic
closures and pull back sections along the induced map of spectra. The lift
of the second geometric point through the universal cover of the first
identifies this restriction as an isomorphism by `isIso_ptRes_app` and
`isIso_liftRes_app`. The composition isomorphism `upperStarStalkIso` then
identifies the resulting stalk with the stalk of the inverse image.

`LisseMonodromy.mono_galoisToAut_hom_app` identifies the action of an
automorphism on a geometric stalk with restriction along its map of spectra.
It expresses `galoisToAut` using the inverse fibre reparametrization and
applies `mono_reparam`. The square of automorphisms and field embeddings
commutes after passage to the algebraic closures because those closures are
purely inseparable over the separable closures. Functoriality of restriction
and compatibility with `upperStarComp` give the square on global sections.
Applying `WeilCoefficients.toModuleCat` gives the claimed identity on stalk
vectors.
