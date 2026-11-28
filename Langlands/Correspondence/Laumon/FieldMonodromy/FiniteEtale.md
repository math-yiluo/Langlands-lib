# Proof of `FiniteEtaleFieldMonodromyStatement`

Module `Langlands.Correspondence.Laumon.FieldMonodromy.FiniteEtale`, namespace
`Langlands.Henniart.Laumon`.

The theorem `finiteEtaleFieldMonodromy` proves
`Langlands.Henniart.Laumon.FiniteEtaleFieldMonodromyStatement` (module
`Langlands.Correspondence.Laumon.FieldMonodromy`) at its universe parameter `u`, with no
hypothesis: for every field `K` with separable closure `Ω`, every commutative ring `Λ`, and in
the change-of-field clause every extension `L / K` with separable closure `Ω_L` and `K`-embedding
`ι : Ω → Ω_L`. This is Laumon (1987), Remarque (2.1.2.1), p. 152, at the level of finite étale
covers and étale sheaves of modules: Stacks Project, Lemma 58.6.3 (Tag 0BNE) and
Theorem 59.56.3 (Tag 03QT).

## The proof

The statement is a conjunction; each part is a result of another module.

1. **Homeomorphism.** `fieldGaloisToAut_isHomeomorph K Ω` (module
   `Langlands.Correspondence.Laumon.FieldMonodromy.GaloisAut`): `Gal(Ω/K)` is a fundamental group
   of the finite étale fibre functor at `fieldGeometricPoint K Ω`, so Mathlib's
   `CategoryTheory.PreGaloisCategory.toAut_isHomeomorph` applies.
2. **Sheaves of `Λ`-modules.** The equivalence `e` is
   `Langlands.Geometry.FieldEtaleModuleSheaves.equivalence K Ω Λ` and the isomorphism `i` is
   `Langlands.Geometry.FieldEtaleModuleSheaves.forgetIso K Ω Λ` (module
   `Langlands.Geometry.FieldEtaleModuleSheaves`), with `Ks = Ω`: the representation attached to
   `F` is its stalk at the Galois point `Spec Ω → Spec K` with the transport-of-structure action,
   identified with the stalk at `AlgebraicGeometry.Scheme.pointSmallEtale (Spec Ω → Spec K)`.
   The germ formula is `forgetIso_hom_app_ρ`.
3. **Change of field.** The isomorphism `c` is the component at `F` of
   `Langlands.Geometry.FieldEtaleStalkChange.sheafFiberIso K Ω Ω_L ι (ModuleCat Λ)` (module
   `Langlands.Geometry.FieldEtaleStalkChange`), which sends the germ at a lift `x` to the germ at
   `Spec ι ≫ x` (`toPresheafFiber_sheafFiberIso_hom_app`); a lift `y` with
   `y = Spec ι ≫ x` is that lift by extensionality of morphisms over `Spec K`. For
   `τ ∈ Gal(Ω_L/L)` and `σ ∈ Gal(Ω/K)` with `ι ∘ σ = τ ∘ ι`, the germ formula of part 2 sends the
   germ at `x` to the germ at `Spec σ ≫ x`, which `c` sends to the germ at
   `Spec ι ≫ Spec σ ≫ x`. This lift is `Spec τ ≫ Spec ι ≫ x`, since
   `Spec ι ≫ Spec σ = Spec (ι ∘ σ) = Spec (τ ∘ ι) = Spec τ ≫ Spec ι`.

The separable closures enter through `IsSepClosure.sep_closed` and `IsSepClosure.separable`,
which provide the instances `IsSepClosed Ω`, `Algebra.IsSeparable K Ω` and `IsSepClosed Ω_L` used
by the three modules; the statement binds `IsSepClosed Ω` and `IsSepClosed Ω_L` by the same
terms.

## Axioms

Under `#print axioms`, `finiteEtaleFieldMonodromy` depends only on `propext`, `Classical.choice`
and `Quot.sound`.
