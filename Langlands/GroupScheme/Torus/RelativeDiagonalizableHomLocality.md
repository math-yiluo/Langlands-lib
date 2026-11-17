# Homomorphisms between diagonalizable groups over a base are locally monomial

Let `X` be any scheme and let `Λ, Λ'` be abelian groups in the scheme universe.
`D_X(Λ)` is the Library's `diagonalizable X Λ`, the base change of `D(Λ)` from
`Spec ℤ` (with `ℤ` lifted to universe `u`). This module treats homomorphisms
`D_X(Λ) → D_X(Λ')` of group schemes over `X`.

## Statements

- `diagonalizableMap X g : D_X(Λ) ⟶ D_X(Λ')` is the homomorphism induced by an
  additive map `g : Λ' →+ Λ`. It is the base change along `X → Spec ℤ` of
  `Diagonalizable.restrictMap`, the restriction of characters along `g`.
  `diagonalizableMap_id` and `diagonalizableMap_comp` state functoriality:
  `D(id) = 𝟙` and `D(g) ≫ D(h) = D(g ∘ h)` for `h : Λ'' →+ Λ'`.
- `baseChange_map_diagonalizableMap`: for `b : Y ⟶ X`, the base change of
  `D_X(g)` along `b` is `D_Y(g)`, conjugated by the Library's canonical
  comparison `diagonalizableBaseChangeIso b`.
- `exists_opens_baseChange_map_eq` (local rigidity): assume `Λ'` is finitely
  generated. Then every homomorphism `u : D_X(Λ) ⟶ D_X(Λ')` and every point `x`
  of `X` admit an open `U ∋ x` and an additive map `g : Λ' →+ Λ` such that the
  restriction of `u` to `U` is `D_U(g)`, again up to `diagonalizableBaseChangeIso`.
  `exists_opens_of_openImmersion` is the same statement for the points in the
  image of an open immersion `j : Spec A ⟶ X`.
- `diagonalizableMap_injective`: if `X` is nonempty, then `g ↦ D_X(g)` is injective.

For an affine base, in namespace `Langlands.GroupScheme.Diagonalizable`:

- `exists_away_baseChange_map_eq_restrictMap`: let `R` be a commutative ring and
  let `N` be finitely generated as an additive monoid. For a homomorphism
  `f : D_R(M) → D_R(N)` and a prime `p` of `R`, there are `g : N →+ M` and `r ∉ p`
  such that the base changes of `f` and of `restrictMap R g` to `R[1/r]` agree.
  This generalizes the Library's `exists_away_eq_restrictMap` from isomorphisms
  to homomorphisms.
- `baseChange_map_eq_restrictMap_of_scalarExtension_eq`: if the Hopf coordinates
  of `f`, after scalar extension to an `R`-algebra `C`, equal the degree map of
  `g`, then the base changes of `f` and `restrictMap R g` to `C` agree.
- `bialgHomOfHom f` is the bialgebra map `R[N] → R[M]` that corresponds to `f`
  under the full faithfulness of `hopfSpec`. By `bialgHomOfHom_hom_left`, its
  spectrum is the underlying scheme map of `f`.

The remaining declarations are proof helpers. `pointsEquiv X Λ T` identifies the
points of `D_X(Λ)` over an `X`-scheme `T` with the homomorphisms
`Multiplicative Λ →* Γ(T, 𝒪_T)ˣ`. The other helpers state how this identification
interacts with `D(g)`, base change and transport (`ActsBy` and the lemmas around it).

## Proof

All global statements are proved through character-valued points. By
`hom_ext'`, two homomorphisms out of `D_X(Λ)` agree when they agree on these points
over every `X`-scheme. `pointsEquiv` is `baseChangePointsEquiv` along `X → Spec ℤ`
followed by the Library's `characterPointsEquiv` over `Spec ℤ`. On these points,
`D_X(g)` is precomposition with `g` (`pointsEquiv_diagonalizableMap`, from
`Diagonalizable.pointsEquiv_restrictMap`).

- Functoriality: `diagonalizableMap_id` is proved on points.
  `diagonalizableMap_comp` follows from `restrictMap_comp`.
- Base change: `pointsEquiv_baseChangeIso_hom` shows that
  `diagonalizableBaseChangeIso` preserves character-valued points. Its proof uses
  `baseChangePointsEquiv_base_comp` for the composite pullback,
  `characterPoints_eqToHom` for the `eqToHom` that changes the structure map to
  the terminal `Spec ℤ`, and the naturality of `characterPointsEquiv`.
  `baseChange_map_eq_of_actsBy` then turns "`u` acts by precomposition with `g` on
  all points coming from `Y`" into the equation of (1).
- Uniqueness is the Library's `Diagonalizable.restrictMap_baseChange_injective`
  for the `Spec ℤ`-scheme `X`. Our `diagonalizableMap` is definitionally the base
  change used there.
- Affine locality, adapted from `DiagonalizableAutomorphismLocality` with the
  isomorphism `bialgEquivOfIso` replaced by the homomorphism `bialgHomOfHom`. Write
  `F` for the Hopf coordinates of `f` and `κ(p)` for the residue field. The
  character map is `g := mapDomainOfBialgHom (scalarExtension F κ(p))`, and `r` is
  `generatorCoefficientProduct F g s` for a finite generating set `s` of `N`. The
  Library's `field_character_coefficient` shows that `r` maps to `1` in `κ(p)`, so
  `r ∉ p`. The Library's `scalarExtension_eq_mapDomain_of_isUnit` shows that over
  `R[1/r]` the scalar-extended coordinates equal the degree map of `g`.
  `baseChange_map_eq_restrictMap_of_scalarExtension_eq` turns this into equality of
  base-changed morphisms through `HopfMorphismBaseChange.tensorSpecIso_naturality`.
  All of these come from `DiagonalIsomorphismLocus`; the
  certificate there is stated for arbitrary bialgebra maps.
- Global locality: pick an affine open `j : Spec A ⟶ X` from `X.affineCover`
  through `x`. Transport `u` along `j` and `relativeModelIso` to a homomorphism
  `fA : D_A(Λ) → D_A(Λ')`, and apply the affine result at the prime of the chosen
  point. This gives `g` and `r`. Take `U` to be the range of
  `Spec A[1/r] → Spec A → X`. For each `U`-scheme `T`, the corresponding `X`-scheme
  is isomorphic, by `Over.isoMk (Iso.refl _)` and `isoOpensRange_inv_comp`, to one
  that comes through `Spec A[1/r]`. On points over that scheme, `fA` acts by
  precomposition with `g` (`characterPoints_of_baseChange_eq`). `actsBy_of_transport`,
  `ActsBy.of_iso` and `baseChange_map_eq_of_actsBy` conclude.

The proof uses only the standard axioms.

## Provenance

This is internal infrastructure for Task 6943 (Conrad, *Reductive group schemes*,
Proposition B.3.8: groups of multiplicative type are closed subgroups of tori).
It records, in the form that proof needs, the standard fact that over any base,
homomorphisms between diagonalizable groups with finitely generated character
groups are given Zariski-locally by homomorphisms of character groups. For
`Λ' = ℤ` this is the identification `Hom_{S-gp}(D_S(M), G_m) = Γ(S, M_S)` that
Conrad uses, for example in Remark 6.1.2. The definitions and statements were
written for this task. Their content is exactly the Lean statements above. The
interfaces (diagonalizableMap with functoriality, base change, local rigidity,
uniqueness) were agreed with Worker 386, who assembles the proof of Task 6943.

`diagonalizableMap` is imported from [`RelativeDiagonalizableExactQuotient`](RelativeDiagonalizableExactQuotient.md); the point formulas here use that same base-change definition.
