# Coefficient naturality of the actual Čech-to-H¹ comparison

This internal extension of the published `AbelianSheafCechH1` construction
proves naturality in the coefficient sheaf on a fixed topological space.
The space is any `T : TopCat.{u}` and the abelian sheaves have values in
`AddCommGrpCat.{u}`. The index type is in an independent universe `w`.
No new external-source translation is asserted.

`mapCocycles U φ` applies a presheaf morphism componentwise to ordered
one-cocycles. The published identity `Cech.d_map` proves that cocycles
remain closed and that coboundaries map to coboundaries. Thus `mapHom U φ`
is an additive homomorphism on the existing quotient `CechH1`. Its
computation on quotient representatives and its identity and composition
laws are proved without any covering or finiteness hypothesis.

For a morphism `φ : S ⟶ S'` of short complexes of abelian sheaves,
`mapRepresentative φ r` maps the primitive by `φ.τ₂` and the global
quotient section by `φ.τ₃`. The two commuting squares and `Cech.d_map`
verify the equations for a representative of the mapped one-cochain.
When both sequences are short exact, `mapRepresentative_value` identifies
its value with `Sheaf.H.map φ.τ₁ 1` of the original value. This uses
Mathlib's actual connecting-homomorphism naturality `Sheaf.H.δ_naturality`
and the naturality of its degree-zero section equivalence. It requires
neither a cover hypothesis nor flasqueness.

On a finite full cover, if both middle sheaves are flasque,
`quotientClassHom_naturality` follows by quotient induction. On a cocycle,
the existing independence-of-representative computation lets us use the
mapped representative, whose value is the actual cohomological image.

For an arbitrary sheaf map `φ : F ⟶ G`, `injectiveScMap φ` extends
`φ ≫ Injective.ι G` across the monomorphism `Injective.ι F` using the
injectivity of `Injective.under G`. The induced cokernel map completes
a morphism between the exact chosen injective sequences. Its first
component is exactly `φ`. The published injective flasqueness result
therefore lets the preceding theorem specialize to

```text
comparisonHom G U hcov (mapHom U φ.hom x)
  = Sheaf.H.map φ 1 (comparisonHom F U hcov x).
```

The target `Sheaf.H` and its map are Mathlib's actual Ext-defined
cohomology. The result concerns a finite full cover on a fixed space.
Naturality under maps of spaces, line-bundle reduction and deformation,
and the actual fppf Picard sheaf representability theorem remain separate
obligations.
