# Quasi-split inner forms from root-datum and adjoint-quotient existence

Module `Langlands.GroupScheme.Rational.QuasiSplitInnerFormExistenceReduction`.

This supporting unit reduces the host proposition
`QuasiSplitInnerFormExistenceStatement.{u}` to two Library propositions that
are stated but not yet proved in the Library:

- `RootDatumExistenceStatement.{u}` (module `Reductive.RootDatumStatement`): a
  split maximal torus of a connected reductive field group has a reduced root
  datum indexed by a finite type;
- `AdjointQuotientExistenceStatement.{u}` (module `Adjoint.ExistenceStatement`):
  every connected reductive field group has an actual adjoint quotient by its
  full scheme-theoretic centre.

It does not prove either proposition, so it does not prove the host statement
by itself. Every other ingredient is a proved Library result or a supporting
module listed below.

## Statements

- `quasiSplitInnerFormExistence_of_rootDatum_adjoint hroot hadj`: for
  `hroot : RootDatumExistenceStatement.{u}` and
  `hadj : AdjointQuotientExistenceStatement.{u}`,
  `QuasiSplitInnerFormExistenceStatement.{u}` holds. So for every field
  `k : Type u` and every group scheme `H` over `Spec k` with
  `IsConnectedReductive H`, there is a `QuasiSplitInnerForm H`.
- `quasiSplitInnerFormOfRootDatumAdjoint hroot hadj H hH` (definition): the same
  hypotheses give a chosen `QuasiSplitInnerForm H`, obtained by
  `Classical.choice` from the theorem.

A `QuasiSplitInnerForm H` (module `Rational.QuasiSplitInnerForm`) consists of:

- a quasi-split ground-field model;
- an adjoint quotient of the model whose target is quasi-split;
- a finite Galois extension field in `Type u`;
- a local group isomorphism from the model to `H` over the Galois cover; and
- an adjoint-valued natural cocycle with the discrepancy equation for the
  actual inner action.

## Proof

Let `H` be a connected reductive group over a field `k`.

1. *Torus and splitting field.* `maximalTorusExistence` (module
   `Torus.ExistenceProof`) gives a maximal `k`-torus `i₀ : T₀ ⟶ H`.
   `torusFiniteGaloisSplitting` (module `Torus.FiniteGaloisSplittingProof`)
   gives a finite Galois extension `K/k` over which `T₀` splits.
2. *Split group over `K`.* `IsConnectedReductive.baseChange_of_algebraicExtension`
   (module `Reductive.AlgebraicExtensionAscent`) shows that `H_K` is connected
   reductive. `maximalTorusBaseChange` (module `Torus.MaximalBaseChangeProof`)
   shows that `(i₀)_K : (T₀)_K ⟶ H_K` is a maximal torus, and it is split.
3. *Pinning.* `hroot` gives a finite index type `J` and a reduced root datum `P`
   of `(i₀)_K`. `SplitPinning.ofRootDatum` (module `Reductive.PinningConstruction`)
   with the root lines of `splitRootLieLine` (module
   `Reductive.SplitRootLieLineProof`) gives a split pinning `p` of `H_K`. Its
   torus is definitionally `(T₀)_K` and its inclusion is `(i₀)_K`. The inclusion
   is a closed immersion, hence a monomorphism.
4. *Galois action.* `δ := IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus
   k K i₀ _ _ hP` (module `Reductive.RootDatumGaloisCoroots`) is the actual
   Galois action `Gal(K/k) →* Aut(P)`. On characters it is transport along
   `Spec σ`. Let `ρ := p.basedRootDatumProjection.comp δ` (module
   `Reductive.BasedRootDatumProjection`) be its based representative, a
   homomorphism into the based automorphisms of `p`.
5. *Hypotheses of the twist theorem.* For each `σ`, take
   `τ σ := CommGroupScheme.descentBaseChangeIso (fieldMap k K) (Spec σ) _ T₀`,
   the canonical descent identification of the torus.
   - The square `hτ` is the Library naturality
     `descentBaseChangeIso_naturality` for `i₀`.
   - The character equation `hδ`, `(δ σ).weightEquiv χ =
     (τ σ).inv ≫ characterLattice.baseChange (Spec σ) p.torus χ`, holds by
     `rfl`: both sides unfold to `characterLattice.transport`.
   - The Weyl agreement `hw` is `basedRootDatumProjection_correction`.
6. *Quasi-split model.* `s := (p.galoisQuasiSplitSolution ρ).group` (supporting
   module `Reductive.PinnedGaloisBorel`) is an actual descent solution of the
   pinned Galois datum, with `s.iso : (s.obj)_K ≅ H_K`. By
   `isQuasiSplit_galoisQuasiSplitSolution`, `s.obj` is quasi-split.
7. *Adjoint quotients.* `hadj` gives an adjoint quotient `q : s.obj ⟶ A` over
   `k` and an adjoint quotient `q'` of `H_K` over `K`. The Library theorem
   `adjointQuotientQuasiSplitStatement` (module `Adjoint.QuasiSplitProof`)
   shows that `A` is quasi-split.
8. *Assembly.* `SplitPinning.hasInnerDiscrepancy_solution` (supporting module
   `Rational.PinnedGaloisInnerTwist`), applied to `τ, hτ, δ, hδ, hw, q', s, q`,
   shows that `LocalGroupIso.ofBaseChangeIso s.iso` over `ringTest k K` has all-test
   inner discrepancy for `hq.innerAction`. `QuasiSplitInnerForm.ofInnerDiscrepancy`
   (module `Rational.InnerDiscrepancy`) then assembles the quasi-split inner
   form. Its model is `s.obj`, its adjoint quotient is `q`, its carrier is `K`
   and its local isomorphism is `ofBaseChangeIso s.iso`. The cocycle is the
   unique natural adjoint cocycle representing the discrepancies.

## Provenance

The structure follows the standard construction of the quasi-split inner form
by a pinning, as in Conrad, *Reductive group schemes* (2014),
Proposition 7.2.11 (printed/PDF p.258; source
`conrad-2014-reductive-group-schemes`), which is the source cited by the host
statement. A finite Galois extension splits a maximal torus. The Galois action
on the root datum is corrected by Weyl elements to a based action. The pinned
descent of the split form along this action is quasi-split, and it is an inner
form of the given group. The Lean route, including the reduction to the two
named existence propositions, is internal to this Library.
