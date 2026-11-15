# Zero-value root jumps over `F` and over the maximal unramified extension

This module states one unproved, universe-polymorphic, Prop-valued statement,
`UnramifiedZeroJumpFieldComparisonStatement`. At an `Aut(K/F)`-fixed point `x`, it compares
the filtration jumps at value `0` of a relative root `α` over `F` with the jumps of its base
change `α_K` over `K = F^ur`. Both sides use the same split torus `S`. The statement is the
remaining input of `unramifiedZeroJumpLiftMultipliable_of_fieldComparison` (module
`UnramifiedZeroJumpLiftMultipliableReduction`), which derives the Library statement
`UnramifiedZeroJumpLiftMultipliableStatement` from it.

## Setting

The binders up to `C`, the V 6 hypothesis `IntegerValuation.IsOmegaCompatible`, and the lets
`fixed` and `φ` are copied verbatim from `UnramifiedZeroJumpLiftMultipliableStatement`
(module `UnramifiedAffineRootRestrictionReduction`). In summary:

- `F` is a nonarchimedean local field and `K = inertiaFixedField F` is its maximal unramified
  extension. `Aut(K/F)` is `inertiaFixedField F ≃ₐ[F] inertiaFixedField F`. Write
  `b = algebraBaseMap F K`, and `S_K`, `G_K`, `T_K`, `iS_K`, `iT_K`, `f_K` for the base
  changes along `b`.
- `G` is connected reductive over `F`, `iS : S.toGrp ⟶ G` is a maximal split torus, and
  `T` is an `F`-torus with `iT : T.toGrp ⟶ G` and `f : S ⟶ T`, `groupHom f ≫ iT = iS`.
  `hiT` says that `T_K` is a maximal split torus of `G_K`, and `hE` is the opposite-factor
  hypothesis for `(G_K, T_K)`.
- `D : KPApartmentData` is an equipollence class of valuations of the root datum of
  `(G_K, T_K)`, with `C : CentralizerDatum` and V 6.
- `fixed x` says that `x : D.Apartment` is fixed by every `σ ∈ Aut(K/F)`.
- `φ x : RootFunctionFamily S G` is `torusFieldRestrictedRootFunctionFamily` of the
  valuation `x.val`: the restricted valuation of `(G, S)` over `F`.

The statement adds one let:

- `ψ x : RootFunctionFamily S_K G_K` is `torusRestrictedRootFunctionFamily` of `x.val` along
  `f_K : S_K ⟶ T_K`. This is the torus restriction of the valuation `x.val` of `(G_K, T_K)`
  to the split torus `S_K` of `G_K`, over the same field `K`. The proof arguments are those
  that `torusFieldRestrictedRootFunctionFamily` passes internally. By the definition of
  `torusFieldRestrictedRootFunctionFamily`, `φ x` is
  `RootFunctionFamily.fieldRestrict (ψ x)`, the restriction of `ψ x` to `F`-points:
  `(φ x) α g = (ψ x) α_K (rationalExtend F K G g)` for every character `α` of `S` and
  `g ∈ G(F)`, where `α_K = characterLattice.baseChange b S α`.

## The statement

For every `x : D.Apartment` with `fixed x`, all `φx : RootFunctionFamily S G` and
`ψx : RootFunctionFamily S_K G_K` with `φ x = φx` and `ψ x = ψx`, and every
`α ∈ relativeRoots iS`:

```
IsRootFiltrationJump iS φx α 0 ↔
  IsRootFiltrationJump iS_K ψx (characterLattice.baseChange b S α) 0
```

`IsRootFiltrationJump i y c r` is the published predicate of module
`RootJumpLiftNonMultipliable`:

```
¬ (rootFiltration i y c r ⊆
    {g | g ∈ rootGroupPoints i c ∧ (r : WithTop ℝ) < y c g} *
      (doubleRootGroupPoints i c : Set (rationalPoints _)))
```

In KP's notation this is `U_{c,y,r} ⊈ U_{c,y,r+} · U_{2c}`. At `r = 0` it is, by unfolding
the definition, exactly the jump condition written out in the statements of
`UnramifiedAffineRootRestrictionReduction`. So the statement says:

> `U_{α,φx,0} ⊈ U_{α,φx,0+} · U_{2α}(F)` if and only if
> `U_{α_K,ψx,0} ⊈ U_{α_K,ψx,0+} · U_{2α_K}(K)`.

Here `U_{2α_K}(K)` is `doubleRootGroupPoints iS_K α_K`, the root group of `2α_K` for the
torus `S_K` when `2α_K` is a root of `(G_K, S_K)`, and trivial otherwise.

The variables `φx`, `ψx` and the two equations are a technical device. Substituting the
equations gives the statement with `φ x` and `ψ x` in place of `φx` and `ψx`, and the
statement with variables follows from that one by rewriting. With the variables, a user
can pass its own expression of the two families and prove the equations by `rfl`. Lean
then compares the two expressions as whole families. Without the variables, Lean has to
compare the values `y c g` inside the filtration sets. These values are projections of
the families, and the comparison unfolds the families completely, which exceeds the
heartbeat limit.

## Source and provenance

This is an internal statement, not a numbered statement of Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023). It is a consequence of KP Proposition 9.4.28 (printed
pages 359–360, PDF pages 390–391, setting 9.4.27 on printed page 359) at the fixed point
`x`, together with a comparison over the single field `K`:

- **Over `F`.** By KP 9.4.28, at the fixed point `x` the relative affine roots of `(G, S)`
  that vanish at `φ x` are the restrictions of the absolute affine roots of `(G_K, T_K)`
  that vanish at `x`. So `α` has a jump at `0` for `φ x` if and only if some root `χ` of
  `(G_K, T_K)` with `f_K ≫ χ = α_K` has a jump at `0` for `x.val`. These are the
  Library statements `UnramifiedZeroJumpLiftReducedStatement`,
  `UnramifiedZeroJumpLiftMultipliableStatement` and `UnramifiedZeroJumpDescentStatement`.
- **Over `K`.** `α_K` has a jump at `r` for the torus restriction `ψ x` if and only if
  some root `χ` of `(G_K, T_K)` with `f_K ≫ χ = α_K` has a jump at `r` for `x.val`. The
  forward direction is `exists_rootJump_lift_of_torusRestrictedJump` (module
  `UnramifiedZeroJumpLiftMultipliableReduction`). The converse is not yet in the Library.

The jump condition is KP's condition (Definition 6.3.4, printed pages 217–218, PDF pages
248–249) for the affine functional with derivative `c` and value `0` at the point to be an
affine root, with `U_{2c}` the full group of points of the root group of `2c`, as in the
statements of `UnramifiedAffineRootRestrictionReduction`.

The statement does not assume that `φ x` lies in any particular equipollence class, and it
claims nothing about values other than `0`.

## Expected proof

KP prove 9.4.28 through parahoric group schemes (Proposition 9.4.23, printed page 357,
PDF page 388), which are not in the Library. A direct proof is expected to use Galois
descent along `K/F` for the quotient `U_{α,0} / U_{α,0+} · U_{2α}`:

- Forward direction. Suppose `α_K` has no jump at `0` for `ψ x`. Take an `F`-point `g` of
  `U_{α,φx,0}`. Its image in `G(K)` lies in `U_{α_K,ψx,0}`, so it factors as `u · z` with
  `u` of value `> 0` and `z ∈ U_{2α_K}(K)`. Because `g` is `Aut(K/F)`-invariant,
  `σ ↦ z⁻¹ σ(z)` is a cocycle with values in the depth-`> 0` part of `U_{2α_K}(K)`. The
  vanishing of its first cohomology moves the factorization to `F`-points. When
  `2α ∉ Φ(S)` the group `U_{2α}` is trivial and no descent is needed.
- Converse direction. A nonzero class in the `K`-quotient gives a nonzero
  `Aut(K/F)`-invariant class, by Lang's theorem or Hilbert 90 for the vector group over the
  residue field.

Both directions use the same descent input. The statement is not proved or assumed anywhere
in the Library.
