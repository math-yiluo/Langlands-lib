# Constructing pointed etale local sections of smooth morphisms

Author: Worker 1683.

`Langlands.AlgebraicGeometry.pointedEtaleSection.{u}` constructs actual
`PointedEtaleSectionData` through a prescribed rational point. For a smooth `f : X → S`, a point `s : S`, and a supplied morphism
`x₀ : Spec κ(s) → X` above the canonical residue point, it constructs a
scheme `U`, an etale morphism `p : U → S`, and morphisms
`b : Spec κ(s) → U` and `a : U → X`, with all three equations

- `b ≫ p = S.fromSpecResidueField s`;
- `a ≫ f = p`;
- `b ≫ a = x₀`.

The proof is uniform in the arbitrary universe `u` and retains arbitrary
bases and possibly nonseparated schemes. Neither `f` nor `p` is required
to be globally surjective. The existence proof below uses the affine
witness `Spec R'`. The exported `pointedEtaleSection` chooses from a data
type with no affineness field, so it does not guarantee that its chosen
neighbourhood is affine.

## Implemented construction

`PointedEtaleSectionData f s x₀` records the neighbourhood scheme, its
projection, its point, the section map, etaleness and the three exact
equations. The helper `exists_pointed_etale_section` proves existence
with `f`, `s`, and `x₀` as explicit arguments. The constructor
`pointedEtaleSection` applies classical choice to that existence proof
to produce actual data. It requires only smoothness and the given
compatibility equation of `x₀`.

Let `x` be the image of the unique point of `Spec κ(s)` under `x₀`. Its
image under `f` is `s` by the given equation for `x₀`. Mathlib's local
standard-smooth presentation theorem gives affine opens `V` of `X` and
`W` of `S`, with `x ∈ V`, `s ∈ W`, and `V` mapping into `W`. Put
`A = Γ(X, V)` and `R = Γ(S, W)`. The ring map
`α = f.appLE W V` makes `A` a smooth `R`-algebra.

Let `q` be the prime of `R` corresponding to `s` in the affine chart. The
open immersion `Spec R → S` induces an isomorphism of the scheme residue
fields at `q` and `s`. Compose this with Mathlib's
`Scheme.Spec.residueFieldIso`, comparing the scheme residue field with
`q.asIdeal.ResidueField`, to obtain
`e : S.residueField s ≅ q.asIdeal.ResidueField`. Naturality of canonical
residue-field morphisms proves that `Spec.map e.inv`, followed by the
canonical `Spec κ(q) → Spec R → S`, is exactly the given canonical
`Spec κ(s) → S`. This is the equation called `hbase` in Lean.

The range of `x₀` consists of the single point `x` and lies in `V`, so the
universal property of the open immersion lifts `x₀` to
`xV : Spec κ(s) → Spec A`. Precompose with `Spec.map e.hom` to get
`z : Spec κ(q) → Spec A`. Cancel the target chart's open immersion to
verify that `z` is over the canonical `Spec κ(q) → Spec R`. Full
faithfulness of `Spec` identifies it with an `R`-algebra map
`φ : A →ₐ[R] κ(q)`.

The algebraic helper
`PointedEtaleLocalSections.exists_etale_factor_of_smooth` constructs an
etale `R`-algebra `R'`, an `R`-algebra map `ψ : A → R'`, and an
`R`-algebra map `ρ : R' → κ(q)` with `ρ.comp ψ = φ`. Its proof, including
the finite lifting of the supplied coordinates, is explained in the
companion `Langlands/CommutativeAlgebra/PointedEtaleLocalSections.md`.

Take `U = Spec R'`. The morphism `p` is `Spec R' → Spec R → S`; the
morphism `a` is `Spec R' → Spec A → X`; and `b` is
`Spec κ(s) → Spec κ(q) → Spec R'`, using `e.inv` and `ρ`.
The map `p` is etale because its first factor is the spectrum of an etale
ring map and its second factor is an open immersion. The equation for
`b ≫ p` follows from `ρ` being an `R`-algebra map and `hbase`. The
equation for `a ≫ f` follows from `ψ` being an `R`-algebra map and the
commuting affine-chart square. Finally, the exact ring equation
`ρ.comp ψ = φ`, the definition of `z`, and cancellation of the two inverse
maps of `e` yield `b ≫ a = x₀`. Thus the original point is recovered as a
scheme morphism, including its residue-field map.

## Provenance and remaining consumer obligations

This proves the derived rational-point refinement of The Stacks Project,
Lemma 37.38.6 (Tag 055U), described in the target statement's companion.
Its route uses polynomial specialization and etale base change, rather
than the source's complete-intersection construction. The implementation
uses only `propext`, `Classical.choice`, and `Quot.sound`.

The theorem supplies the pointed geometry input to relative split-torus
lifting. It does not construct the relative Hom scheme or its smoothness,
prove the open locus of closed group-scheme embeddings, or establish
openness of the reductive geometric identity-component locus. Those
consumer obligations remain separate.
