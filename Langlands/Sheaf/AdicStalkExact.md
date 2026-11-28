# Exactness of the stalk functor on `ℓ`-adic sheaves

Module `Langlands.Sheaf.AdicStalkExact`. At a geometric point `t : Spec Ω̄ ⟶ Y` of a scheme `Y`,
weil-conjectures's stalk functor `AlgebraicGeometry.ProEtale.adicStalkFunctor l t` on `ℓ`-adic
sheaves (forget the module structure over the constant sheaf, pull back to `Spec Ω̄`, take global
sections) preserves finite limits and epimorphisms by the instances of
`WeilConjectures.SixFunctors.ProEtale.Adic.SubobjectStalk`. Preservation of epimorphisms rests
on exactness of global sections on the spectrum of an algebraically closed field.

For any short exact sequence `S` of `ℓ`-adic sheaves on `Y`,
`AlgebraicGeometry.ProEtale.adicStalkMap_shortExact` shows that the `ℚ̄_ℓ`-linear stalk maps
`adicStalkMap t S.f` and `adicStalkMap t S.g` are injective and surjective respectively, and
the range of the first is the kernel of the second.
A functor preserving zero morphisms, epimorphisms and kernels preserves homology
(Mathlib's `Functor.preservesHomology_of_preservesEpis_and_kernels`), so the image of `S` is
exact. In a module category this gives the equality of range and kernel
(`ShortComplex.moduleCat_exact_iff_range_eq_ker`).

The declaration depends only on `propext`, `Classical.choice` and `Quot.sound`.
