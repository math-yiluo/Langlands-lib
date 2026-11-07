# Split maximal tori over strictly Henselian local rings: the reduction

This module reduces `StrictHenselianSplitMaximalTorusStatement.{u}` to two inputs
that are not yet proved in the Library. It proves this as a conditional theorem.
It does not prove the target unconditionally.

## Main statement

`StrictHenselianSplitMaximalTorusReductionStatement.{u}` is the proposition

```
RelativeSplitTorusLiftingStatement.{u} → H → StrictHenselianSplitMaximalTorusStatement.{u}
```

where `H` is written inline as the pointed Henselian étale-section property. For
every `R : Type u` with `[CommRing R] [HenselianLocalRing R]`, every scheme `U`,
every étale `p : U ⟶ Spec R` and every
`b : Spec ((Spec R).residueField (closedPoint R)) ⟶ U` with
`b ≫ p = fromSpecResidueField (closedPoint R)`, there is a section
`σ : Spec R ⟶ U` with `σ ≫ p = 𝟙` and `fromSpecResidueField (closedPoint R) ≫ σ = b`.
`H` only claims existence, not uniqueness. It is a standard property of Henselian
local rings (The Stacks Project, Lemma 10.153.3, Tag 04GG). That citation is
context only, and nothing here proves `H`.

The theorem `strictHenselianSplitMaximalTorusReduction` proves the proposition.
Both inputs stay explicit hypotheses:

- `RelativeSplitTorusLiftingStatement` (module
  `Langlands.GroupScheme.Torus.RelativeLiftingStatement`). A closed split torus in a
  residue fibre of a smooth affine group lifts to a closed split torus over an étale
  neighbourhood that has a residue-field-valued point. The lift recovers the given
  inclusion.
- `H`, as above.

The conclusion is exactly the Library proposition
`StrictHenselianSplitMaximalTorusStatement.{u}`, with the same actual residue-field
fibres.

## Proof

Fix a strictly Henselian `R`, a reductive `G` over `Spec R`, the closed point `x₀`,
and `f₀ = fromSpecResidueField x₀`.

1. **Closed fibre.** `isSepClosed_residueField_closedPoint` shows that the
   scheme-theoretic residue field at `x₀` is separably closed. It transfers the
   hypothesis on `IsLocalRing.ResidueField R` through
   `Ideal.bijective_algebraMap_quotient_residueField` and
   `Scheme.Spec.residueFieldIso`. The transfer along a ring isomorphism of fields is
   `isSepClosed_of_ringEquiv`.
   `exists_isMaximalTorus_isSplitTorus_of_isSepClosed` then gives a maximal torus
   `i₀ : T₀ ⟶ G₀` of the closed fibre `G₀ = (baseChange f₀).obj G`, and `T₀` is
   split. It combines the published `TorusExistence.exists_isMaximalTorus` with
   `SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites`, using
   `CoalgebraDescent.separablyClosedGroupLikeSpanning`. `G₀` is smooth and affine
   because pullbacks preserve these properties.
2. **Lifting.** The lifting hypothesis, applied to `G`, `x₀`, `T₀` and the closed
   immersion `i₀`, gives an étale `p : U ⟶ Spec R`, a point `b` over `f₀`, a split
   torus `T` over `U` with a closed subgroup `i : T ⟶ (baseChange p).obj G`, and an
   isomorphism `e` comparing `(baseChange b).map i` with `i₀`.
3. **Section.** `H` gives `σ` with `σ ≫ p = 𝟙` and `f₀ ≫ σ = b`.
4. **Descended torus.** `IsSplitTorus.baseChange σ` gives an isomorphism
   `e' : (baseChange σ).obj T ≅ splitTorus (Spec R) I`. The torus is
   `splitTorus.commGroupScheme (Spec R) I`, with inclusion
   `e'.inv ≫ (baseChange σ).map i ≫ (sectionPullbackIso p σ hσ G).hom`.
   `sectionPullbackIso` identifies `(baseChange σ).obj ((baseChange p).obj G)` with
   `G`, using `baseChangeCompIso`, `σ ≫ p = 𝟙` and `baseChangeIdIso`. The inclusion
   is a closed subgroup by `IsClosedSubgroup.baseChange`, `comp_iso` and `iso_comp`.
   The torus is split through the identity isomorphism.
5. **Closed-fibre maximality.** `baseChange_map_sectionPullback` shows that the
   further pullback along `f₀` of the descended inclusion is
   `A.hom ≫ (baseChange (f₀ ≫ σ)).map i ≫ B.hom` for isomorphisms `A` and `B`. It
   uses the naturality lemma `baseChangeCompIso_hom_naturality`. The lifting
   compatibility rewrites `(baseChange (f₀ ≫ σ)).map i` as `e.hom ≫ i₀` followed by
   isomorphisms. `IsMaximalTorus.of_eq_iso_comp_comp_iso` then transfers maximality
   from `i₀`.
6. **All fibres.** `localClosedFibreMaximalPropagation`, from
   `Langlands.GroupScheme.Torus.LocalMaximalPropagation`, carries closed-fibre
   maximality to every residue-field fibre. It needs only that `R` is local.

## Provenance

This is internal derived infrastructure. It composes Library results and the two
stated hypotheses, and adds no external mathematical assertion. In Conrad,
*Reductive group schemes* (2014), Corollary 3.2.7 (maximal tori exist étale-locally)
uses the smooth surjective scheme of maximal tori from Theorem 3.2.6. Over a
strictly Henselian base, Henselian sections and the splitting of tori
(Proposition B.3.4) then give a split maximal torus. The Lean route avoids the
scheme of maximal tori. It finds a split maximal torus on the separably closed
closed fibre, lifts it over an étale neighbourhood, descends it along a Henselian
section, and spreads maximality from the closed fibre. The lifting step and the
section step are separate hypotheses.
