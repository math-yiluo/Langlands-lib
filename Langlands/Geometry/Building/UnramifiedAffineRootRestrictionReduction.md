# Unramified descent of affine roots from zero-value root jumps

This module states three unproved Prop-valued statements, each universe polymorphic in
`u`, about filtration jumps of root groups at value `0`. It proves that together they imply
the Library statement
`Langlands.Geometry.Building.UnramifiedAffineRootRestrictionStatement` (relative affine
roots are exactly the nonconstant restrictions of absolute affine roots).

The three statements are:

- `UnramifiedZeroJumpLiftReducedStatement`: zero-value jumps lift, for relative roots `α`
  with `2α ∉ Φ(S)`;
- `UnramifiedZeroJumpLiftMultipliableStatement`: zero-value jumps lift, for relative roots
  `α` with `2α ∈ Φ(S)`;
- `UnramifiedZeroJumpDescentStatement`: zero-value jumps descend.

The reduction theorem is `unramifiedAffineRootRestriction_of_zeroJumps`.

## Setting

All three statements use the setting of `UnramifiedAffineRootRestrictionStatement`. Their
binders up to `C`, the V 6 hypothesis `IntegerValuation.IsOmegaCompatible`, and the lets
`fixed` and `φ` are copied verbatim from that statement. In summary:

- `F` is a nonarchimedean local field and `K = inertiaFixedField F` is its maximal unramified
  extension. `Aut(K/F)` is `inertiaFixedField F ≃ₐ[F] inertiaFixedField F`.
- `G` is connected reductive over `F`, `iS : S.toGrp ⟶ G` is a maximal split torus, and
  `T` is an `F`-torus with `iT : T.toGrp ⟶ G` and `f : S ⟶ T`, `groupHom f ≫ iT = iS`.
  `hiT` says that `T_K` is a maximal split torus of `G_K`, and `hE` is the opposite-factor
  hypothesis for `(G_K, T_K)`.
- `D : KPApartmentData` is an equipollence class of valuations of the root datum of
  `(G_K, T_K)`, normalized by the order of `MaximalUnramified.valuation F`. It comes with
  `C : CentralizerDatum` and V 6.
- `fixed x` says that the point `x : D.Apartment` is fixed by every `σ ∈ Aut(K/F)`
  (`RootFunctionFamily.galoisAction`).
- `φ x : RootFunctionFamily S G` is the torus-then-field restriction
  `torusFieldRestrictedRootFunctionFamily` of the valuation `x`.

## The jump condition

For a valuation `y` of a root datum with root `c`, the statements say that **`c` has a
filtration jump at value `0` for `y`** when

```
¬ (rootFiltration i y c 0 ⊆
    {g | g ∈ rootGroupPoints i c ∧ ((0 : ℝ) : WithTop ℝ) < y c g} *
      (doubleRootGroupPoints i c : Set (rationalPoints _)))
```

In KP's notation this is `U_{c,y,0} ⊈ U_{c,y,0+} · U_{2c}`. The middle set is the
expanded form of the filtration subgroup `U_{c,y,0+}`, and the product is the pointwise
product of sets. This is the condition that defines affine roots in
`KPApartmentData.affineRoots` (KP Definition 6.3.4), evaluated at a point where the affine
function is `0` (see `KPApartmentData.mem_affineRootGroup_iff` and
`KPApartmentData.mem_affineRootGroupPlus_iff`). For `D` the valuation is `x.val` with
`x : D.Apartment` over `K`. For the relative root system it is `φ x` over `F`.

## The statements

Each statement holds for every `x : D.Apartment` with `fixed x`.

- **`UnramifiedZeroJumpLiftReducedStatement`.** Let `α ∈ relativeRoots iS` with
  `2 • α ∉ relativeRoots iS`. If `α` has a jump at `0` for `φ x`, then some
  `χ ∈ relativeRoots iT_K` satisfies
  `f_K ≫ χ = characterLattice.baseChange (algebraBaseMap F K) S α`, that is, `χ` restricts
  to `α`, and `χ` has a jump at `0` for `x.val`.
- **`UnramifiedZeroJumpLiftMultipliableStatement`.** The same, for `α` with
  `2 • α ∈ relativeRoots iS`.
- **`UnramifiedZeroJumpDescentStatement`.** Let `χ ∈ relativeRoots iT_K` and
  `α ∈ relativeRoots iS` with `f_K ≫ χ = characterLattice.baseChange (algebraBaseMap F K) S α`.
  If `χ` has a jump at `0` for `x.val`, then `α` has a jump at `0` for `φ x`.

Here `iT_K`, `T_K` and `f_K` are the base changes of `iT`, `T` and `f` along
`algebraBaseMap F (inertiaFixedField F)`.

The two lift statements differ only in the hypothesis on `2α`. The split follows the
expected proofs. The non-multipliable case can be derived from the Library's root-jump
results. The multipliable case is expected to need an `H^1`-vanishing input that the
Library does not yet contain.

## Source and provenance

These are internal, pointwise formulations of the two parts of Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), Proposition 9.4.28 (printed pages 359–360, PDF pages
390–391), in the setting of KP 9.4.27 (printed page 359, PDF page 390). They are not
verbatim numbered statements of the book.

- KP 9.4.28(1) says that every relative affine root `ψ` with derivative `a` is the
  restriction of an absolute affine root. Evaluated at a point of the lower apartment where
  `ψ` vanishes, this is the lift statement: the jump of `a` at `0` comes from a jump at `0`
  of a root of `(G_K, T_K)` restricting to `a`. It is split into the two lift statements
  according to whether `2a` is a root.
- KP 9.4.28(2) says that a nonconstant restriction of an absolute affine root is a relative
  affine root. Evaluated at a point where the restriction vanishes, this is the descent
  statement.

KP prove 9.4.28 from Proposition 9.4.23 (printed page 357, PDF page 388). 9.4.23 identifies
the roots of the reductive quotient of the special fiber of the parahoric group scheme at a
point with the derivatives of the affine roots that vanish there. The value `0` in the
statements is this "vanishing at the point" normalization. The parahoric special fibers
are not in the Library, so the statements are left unproved here.

KP 9.4.28 is about `A^Γ`, the set of `Aut(K/F)`-fixed points of `A`. The statements are
made at every such point `x`, with `φ x` as the corresponding valuation of the relative
root datum. They do not assume that `φ x` lies in any particular equipollence class. They
claim no more than KP 9.4.28 at `x`:

- The lift statements assert the existence of *one* root `χ` restricting to `α`. KP
  9.4.28(1) gives an absolute affine root `ψ_b` for *every* root `b` restricting to `α`,
  and `ψ_b` vanishes at `x` because its restriction vanishes at `φ x`.
- In the descent statement, `χ` restricts to the root `α`, so the absolute affine root with
  derivative `χ` that vanishes at `x` has a nonconstant restriction. By KP 9.4.28(2) that
  restriction is a relative affine root with derivative `α` that vanishes at `φ x`.

## The reduction proof

All of the affine-root argument is in the generic theorem
`restrictedRoots_affineRoots_eq_of_zeroJumps`, over arbitrary fields `k ⊆ K`, an
apartment `D` of `(G_K, T_K)`, an apartment `DS` of `(G, S)` and an affine map
`a : DS.Apartment →ᵃ[ℝ] D.Apartment` whose linear part is induced by
`torusFieldTranslationMap`. Its hypotheses are lift and descent of zero-value jumps between
`w` and `a w` for every point `w` of `DS`. It proves
`AffineRootSystem.restrictedRoots a D.affineRoots = DS.affineRoots` by `ext ψ`:

- `⊆`: let `ψ'` be an affine root of `D` with derivative `rootForm β`, and suppose that
  `ψ'.comp a` is nonconstant. Through `hlin`, the linear part of `ψ'.comp a` pulled back to
  `V(S)` is the pairing with `f_K ≫ β`. So `f_K ≫ β ≠ 0`, and
  `exists_relativeRoot_comp_eq_baseChange` gives a relative root `α₀` with
  `f_K ≫ β = α₀_K`. Then `rootForm_comp_torusFieldTranslationMap_of_comp_eq` and
  `Submodule.linearMap_qext` show that the derivative of `ψ'.comp a` is `rootForm α₀`.
  Let `w₀` be a zero of `ψ'.comp a` (`AffineRootSystem.exists_apply_eq_zero`). The jump of `β` at
  `ψ'(a w₀) = 0` becomes, through `mem_affineRootGroup_iff`, a zero-value jump for
  `a w₀`. Descent gives a zero-value jump of `α₀` for `w₀`, and that is the affine-root
  condition for `ψ'.comp a` at `w₀`.
- `⊇`: let `ψ` be an affine root of `DS` with derivative `rootForm α`. Its linear part is
  nonzero (`rootForm_ne_zero_of_isSplitTorus`), so it has a zero `w₀`. The lift gives a root
  `χ` restricting to `α` with a zero-value jump for `a w₀`. Then
  `D.affineFunctional χ (a w₀) 0` is an affine root of `D`. Its composite with `a` has the
  derivative of `ψ` and vanishes at `w₀`, so it equals `ψ` (`AffineMap.ext_linear`).

`restrictedRoots_affineRoots_eq_of_fixedZeroJumps` restates these hypotheses in the shape
of the three statements: an abstract predicate `fixed`, an abstract restriction map `φ`,
`∀ w, fixed (a w)` and `∀ w, w.val = φ (a w)`. It then splits the lift case by whether
`2α` is a root. The main theorem `unramifiedAffineRootRestriction_of_zeroJumps` introduces
the binders of `UnramifiedAffineRootRestrictionStatement` and specializes the three
statements. It then applies the wrapper, with the target's hypotheses
`∀ w, fixed (a w)`, `∀ w, w.val = φ (a w)` and the linear-part condition.

The wrapper has a technical reason. The statements and the target are separate `def`s, so
their nested proofs (for example inside the `Algebra F (inertiaFixedField F)` instance) are
different auxiliary lemmas. Comparing `φ x α g` across the two versions inside the jump sets
unfolds `torusFieldRestrictedRootFunctionFamily` and is very slow. With `φ` abstract, the
two versions are compared once, at the top level, in `hval`. The main theorem uses
`set_option maxHeartbeats 2000000` and about 966k heartbeats.

## Small lemmas

- `rootForm_ne_zero_of_isSplitTorus`: the root form of a relative root of a split torus is
  nonzero, by `eval_injective`.
- `AffineRootSystem.exists_apply_eq_zero`: a real affine functional with nonzero linear part
  vanishes somewhere.
- `eval_descentCocharacterMap_of_comp_eq`: if `f_K ≫ χ = α_K`, then evaluating `χ` on
  pushed-forward real cocharacters is evaluating `α`.
- `rootForm_comp_torusFieldTranslationMap_of_comp_eq`: under the same condition, the root
  form of `χ` pulled back along `torusFieldTranslationMap` is the root form of `α`.
- `exists_relativeRoot_comp_eq_baseChange`: a nonzero restriction `f_K ≫ β` of a root of
  `(G_K, T_K)` is the base change of a relative root of `(G, S)`. It uses
  `rootRestriction` and `mem_roots_baseChange_iff`.

The nonzero root-form and root-form pullback wrappers reuse `SpecialCompact.rootForm_ne_zero_of_split` and `rootForm_comp_torusFieldTranslationMap`, respectively; their hypotheses and conclusions are retained. Nonconstant affine-function zero existence uses `AffineRootSystem.exists_apply_eq_zero` directly.
