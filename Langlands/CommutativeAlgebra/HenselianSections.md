# Sections of etale and smooth algebras over a Henselian local ring

Author: Worker 633.

This module is `Langlands.CommutativeAlgebra.HenselianSections`; all
declarations lie in the namespace of the same name. It proves that a point of
an etale or smooth algebra or scheme over a Henselian local ring `R`, with
values in the residue field, lifts to an `R`-section through that point. It
supplies the Henselian section step for the strictly Henselian split maximal
torus target `Langlands.GroupScheme.StrictHenselianSplitMaximalTorusStatement`.

Throughout, `R` is a commutative Henselian local ring (`HenselianLocalRing R`)
and `K` is a field with an `R`-algebra structure whose algebra map
`R → K` is surjective. Thus `K` is a residue field of `R` presented as a
quotient, but it is not required to be literally `R ⧸ 𝔪`. `R` and `K` lie in
one universe `u`.

## Declarations

- `isUnit_of_algebraMap_ne_zero`: if `R → K` is surjective and
  `r : R` has nonzero image in `K`, then `r` is a unit.
- `exists_lift_of_isStandardEtale`: if `S` is a standard etale `R`-algebra
  (`Algebra.IsStandardEtale R S`, any universe) and `φ : S →ₐ[R] K`, then
  there is `σ : S →ₐ[R] R` with `(Algebra.ofId R K).comp σ = φ`.
- `exists_lift_of_etale`: the same conclusion for an etale `R`-algebra `S`
  (`Algebra.Etale R S`, any universe).
- `exists_lift_of_smooth`: the same conclusion for a smooth `R`-algebra `S`
  (`Algebra.Smooth R S`) in universe `u`.
- `exists_section_of_smooth_of_surjective`: let `U : Scheme.{u}`, let
  `p : U ⟶ Spec R` be smooth, and let `b : Spec K ⟶ U` satisfy
  `b ≫ p = Spec.map (algebraMap R K)`. Then there is
  `σ : Spec R ⟶ U` with `σ ≫ p = 𝟙 _` and
  `Spec.map (algebraMap R K) ≫ σ = b`.
- `exists_section_of_smooth`: the same, with `K` replaced by the scheme
  residue field `(Spec R).residueField (IsLocalRing.closedPoint R)` and
  `Spec.map (algebraMap R K)` replaced by
  `(Spec R).fromSpecResidueField (IsLocalRing.closedPoint R)` in both
  equations.
- `exists_section_of_etale`: the same as `exists_section_of_smooth` for an
  etale `p`.
- `HenselianEtaleSectionStatement`: the proposition, at universe `u`, that for
  every commutative Henselian local ring `R : Type u`, every
  `U : Scheme.{u}`, every etale `p : U ⟶ Spec R` and every
  `b : Spec ((Spec R).residueField (closedPoint R)) ⟶ U` with
  `b ≫ p = (Spec R).fromSpecResidueField (closedPoint R)`, there exists
  `σ : Spec R ⟶ U` with `σ ≫ p = 𝟙 _` and
  `(Spec R).fromSpecResidueField (closedPoint R) ≫ σ = b`.
- `henselianEtaleSection : HenselianEtaleSectionStatement.{u}`, proved by
  `exists_section_of_etale`.

The equation `fromSpecResidueField ≫ σ = b` says that `σ` sends the closed
point to the image point of `b` and induces the given map on residue fields.
No finiteness or affineness hypothesis on `U` beyond smoothness or etaleness
of `p` is imposed.

## Implemented proof

`isUnit_of_algebraMap_ne_zero`. Mathlib's `IsLocalRing.ker_eq_maximalIdeal`
identifies the kernel of the surjection `R → K` with the maximal ideal. An
element with nonzero image is therefore outside the maximal ideal, hence a
unit.

`exists_lift_of_isStandardEtale`. Choose a standard etale presentation `P`
of `S` (Mathlib's `StandardEtalePresentation`: `S ≅ R[X]_g ⧸ (f)` with
`f` monic). The value `φ(P.x) ∈ K` is a root of `f` at which `g` is
nonzero, and `HasMap.isUnit_derivative_f` shows that `f'` is nonzero there.
The equivalence of items 1 and 3 in Mathlib's `HenselianLocalRing.TFAE`
(lifting simple roots along a surjection onto a field) supplies `a : R` with
`f(a) = 0` and image `φ(P.x)`. The image of `g(a)` in `K` is `g(φ(P.x)) ≠ 0`,
so `g(a)` is a unit by the previous lemma, and `a` defines a map `P.HasMap a`.
Let `σ` be the presentation lift at `a` composed with `P.equivRing`. Both
`σ` followed by `R → K` and `φ` send `P.x` to `φ(P.x)`, so `P.hom_ext`
proves the required equality.

`exists_lift_of_etale`. The kernel `Q` of `φ` is prime. Etaleness of
`S` at `Q` follows from formal etaleness of `S → S_Q` and composition.
Mathlib's `Algebra.IsEtaleAt.exists_isStandardEtale` provides `f ∉ Q` such
that `S_f` is standard etale over `R`. Since `φ(f) ≠ 0`, `φ` extends to an
`R`-algebra map `S_f → K` by `IsLocalization.Away.lift`. The standard etale
case gives a section of `S_f`; precomposition with `S → S_f` gives `σ`, and
the localization factorization proves the equation.

`exists_lift_of_smooth`. Let `𝔪` be the maximal ideal. The surjections
`R → K` and `R → κ(𝔪)` both have kernel `𝔪`, giving an injective
`R`-algebra map `e : K → κ(𝔪)` (built from
`Ideal.quotientKerAlgEquivOfSurjective` and `Ideal.Quotient.liftₐ`). The
Library lemma
`Langlands.CommutativeAlgebra.PointedEtaleLocalSections.exists_etale_factor_of_smooth`,
applied to `e ∘ φ`, provides an etale `R`-algebra `R'` and maps
`ψ : S → R'`, `ρ : R' → κ(𝔪)` with `ρ ∘ ψ = e ∘ φ`. The etale case
applied to `ρ` gives `τ : R' → R`; then `σ = τ ∘ ψ`, and the equation is
checked after applying the injective `e`.

`exists_section_of_smooth_of_surjective`. Spec of a field has one point.
Choose an affine open `V ⊆ U` containing its image. Then `b` factors through
`V.fromSpec : Spec Γ(U, V) ⟶ U` by `IsOpenImmersion.lift`. Full faithfulness
of `Spec` (`Spec.preimage`) gives ring maps `g : R → Γ(U, V)`, with
`Spec.map g = V.fromSpec ≫ p`, and `φ : Γ(U, V) → K`, with `Spec.map φ`
the factored point. Since `V.fromSpec ≫ p` is smooth between affine
schemes, `HasRingHomProperty.Spec_iff` and `RingHom.smooth_algebraMap`
show that `Γ(U, V)` is a smooth `R`-algebra via `g`. Faithfulness of
`Spec.map` and the hypothesis on `b` give `g ≫ φ = algebraMap R K`, so
`φ` is an `R`-algebra map. The smooth algebra case gives a section `τ`.
Then `σ = Spec.map τ ≫ V.fromSpec` satisfies `σ ≫ p = 𝟙`, because `τ`
retracts `g`, and passes through `b`, because `τ` followed by `R → K` is
`φ`.

`exists_section_of_smooth`. Take
`K = (closedPoint R).asIdeal.ResidueField`, whose algebra map from `R` is
surjective because the closed point is a maximal ideal.
`Scheme.Spec.residueFieldIso` identifies it with the scheme residue field,
and `Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField` identifies
`fromSpecResidueField` with `Spec.map` of the algebra map through this
isomorphism. Composing `b` with the isomorphism transports the hypothesis and
conclusion of the previous theorem. `exists_section_of_etale` uses that an
etale morphism is smooth. `henselianEtaleSection` applies it with the etale
hypothesis as a local instance.

## Provenance and scope

These are derived infrastructure results, with no new external assertion.
The etale case is the standard characterization of Henselian local rings by
sections of etale algebras: The Stacks Project, Lemma 10.153.3
(Tag 04GG), conditions (7) and (8) (https://stacks.math.columbia.edu/tag/04GG).
That reference is mathematical context only. The Lean proofs use Mathlib's
`HenselianLocalRing.TFAE` root-lifting criterion and standard etale local
structure, rather than the listed condition (8). The smooth case reduces to the
etale case through the published Library lemma `exists_etale_factor_of_smooth`.
The scheme forms reduce to the algebra forms on an affine open neighbourhood of
the given point.

`HenselianEtaleSectionStatement` records the exact interface that the
strictly Henselian torus assembly uses. It states existence only, not
uniqueness, of the section.
