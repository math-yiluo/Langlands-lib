# Galois coverings on a site and Galois descent

Worker 749. This module is a derived categorical helper for the planned proof of
`AnalyticEtaleGaloisCoinducedLocalAcyclicStatement`. It supplies the descent part of a
Galois–Čech system (`Langlands.Cohomology.GaloisCartan`) for Galois coverings on an
arbitrary site. It imports only Mathlib.

## Background and provenance

Milne, *Étale Cohomology* (1980), III Example 2.6, printed pp. 99–100 (source
`milne-1980-etale-cohomology`), treats a finite Galois covering `Y → X` with group `G`.
There the map `Y × G → Y ×_X Y` is an isomorphism. For a sheaf `P`, the Čech complex of
the covering is then isomorphic to the complex of inhomogeneous cochains of `G` with
values in `P(Y)`. Degree zero of that comparison is Galois descent: `P(X)` is the module
of `G`-invariants of `P(Y)`.

This module states the Galois condition without fibre products or coproducts in the site
category, as two local conditions on arrows into `V'`. It proves only the descent
statement. The statements and proofs are internal, and use Mathlib's sheaf condition for
a covering family.

## Galois coverings

Let `C` be a category with a Grothendieck topology `J`, let `Γ` be a group and let
`V' V : C`. The helper `GaloisCovering.transitivitySieve deck f g` is the sieve of arrows
`h` into `U` for which `h ≫ g = h ≫ f ≫ deck γ` for some `γ`.

`GaloisCovering J Γ V' V` consists of the following.

- An arrow `p : V' ⟶ V` whose single-arrow family covers `V`:
  `Sieve.ofArrows (fun _ : Unit => V') (fun _ => p) ∈ J V`.
- Deck transformations `deck : Γ → (V' ⟶ V')` with `deck 1 = 𝟙 V'`,
  `deck (γ * δ) = deck δ ≫ deck γ` and `deck γ ≫ p = p`.
- `locally_transitive`: if `f g : U ⟶ V'` satisfy `f ≫ p = g ≫ p`, then
  `transitivitySieve deck f g` covers `U`. Locally, `g` is a deck translate of `f`.
- `locally_free`: if `f ≫ deck γ = f` for some `f : U ⟶ V'`, then `γ = 1` or the empty
  sieve covers `U`.

On representable presheaves, `locally_transitive` says that
`Γ × y(V') → y(V') ×_{y V} y(V')`, `(γ, f) ↦ (f ≫ deck γ, f)`, is locally surjective.
`locally_free` amounts to local injectivity of that map, since `Γ` is a constant presheaf and `deck γ ≫ deck γ⁻¹ = 𝟙`.
Together they say that the map becomes an isomorphism after sheafification.

## Descent

Let `R` be a commutative ring and `F` a sheaf of `R`-modules on `(C, J)`.

- `eq_of_sieve`: two sections over `U` are equal if their restrictions agree along every
  arrow of a covering sieve. The proof uses `Presheaf.IsSheaf.hom_ext` with the test
  module `R` (`sectionHom x` is the map `r ↦ r • x`). The helper lemmas are
  `sectionHom_apply_one`, `sectionHom_comp` and `map_map_apply`.
- `map_eq_map_of_invariant`: let `x` be a section over `V'` fixed by restriction along
  every deck transformation. If `a ≫ p = b ≫ p`, then `x` has the same restriction along
  `a` and along `b`. Proof: on the sieve from `locally_transitive`, the two restrictions
  agree by invariance; then apply `eq_of_sieve`.
- `map_p_injective`: restriction along `p` is injective. This is
  `Presheaf.IsSheaf.hom_ext_ofArrows` for the covering family `{p}`.
- `exists_map_p_eq`: every deck-invariant section over `V'` is the restriction of a
  section over `V`. By `map_eq_map_of_invariant`, the family `{x}` is compatible, and
  `Presheaf.IsSheaf.amalgamateOfArrows` glues it.

Descent uses `locally_transitive` and the covering condition only, not `locally_free`.

## The representation on sections

Here `R` lies in the universe of `Γ`.

- `representation G F : Representation R Γ (F.obj.obj (op V'))` lets `γ` act by
  restriction along `deck γ⁻¹`. This is a left action by `deck_one` and `deck_mul`, and
  `representation_apply` unfolds it.
- `rep G F : Rep R Γ` is the bundled representation.
- `representation_invariant_iff`: invariance under the representation is the same as
  invariance under restriction along every deck transformation.

With `map_p_injective` and `exists_map_p_eq`, restriction along `p` identifies `F(V)`
with the invariants of `rep G F`. These are the augmentation hypotheses of a
`GaloisCechSystem` at one Galois covering.

## Scope

No vanishing of group cohomology is proved here, not even for injective sheaves. That
comparison (Milne III Lemma 2.4 and Example 2.6) is separate work. Nothing analytic is
asserted. Constructing Galois coverings of analytic spaces, and checking their local
conditions, are separate obligations.
