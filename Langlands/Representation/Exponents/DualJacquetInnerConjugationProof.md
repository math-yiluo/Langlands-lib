# Inner-conjugation invariance of the actual opposite-dual Jacquet spectrum

Author: Worker 276.

The theorem `Langlands.glDualJacquetInnerConjugation.{uF,uV}` has the complete
unapplied type `Langlands.GLDualJacquetInnerConjugationStatement.{uF,uV}` from
`Langlands.Representation.Exponents.DualJacquetInnerConjugationStatement`. The
companion `Langlands.glDualJacquetInnerConjugationNonunitary.{uF,uV}` has the
type `Langlands.GLDualJacquetInnerConjugationNonunitaryStatement.{uF,uV}` from
the same module. For every prime `p`, field `F`, topological data `T`, rank `n`
(including zero), conjugate block pair `P`, complex representation `A` of
`GL_n(F)` and split-centre character `χ` for `P.shape`, they prove

- `T.IsDualJacquetExponent P.shape (P.pullbackRep A) χ ↔ T.IsDualJacquetExponent P.shape A χ`;
- `T.IsUnitaryDualJacquetExponent P.shape (P.pullbackRep A) χ ↔ T.IsUnitaryDualJacquetExponent P.shape A χ`.

Both sides use the same character `χ` on the same ordered block shape
`P.shape`. No irreducibility, admissibility, smoothness of `A`, temperedness,
criticality or finiteness hypothesis is added. The field and representation
carrier universes stay independent.

## The inner-action equivalence

Write `g = P.conjugator`. `P.pullbackRep A` has the carrier of `A` and the
action `h ↦ A.ρ (g * h * g⁻¹)`. The definition
`Langlands.Exponents.ConjugateBlockPair.pullbackEquiv P A :
A.ρ.Equiv (P.pullbackRep A).ρ` is the linear map `A.ρ g` with inverse
`A.ρ g⁻¹`. The two inverse laws follow from `map_mul`, `inv_mul_cancel`,
`mul_inv_cancel` and `map_one`. It intertwines because
`A.ρ g * A.ρ h = A.ρ (g * h * g⁻¹) * A.ρ g`. Both sides are rewritten with
`map_mul` and the group identity `g * h = (g * h * g⁻¹) * g` is closed by
`group`. The simp lemma `pullbackEquiv_apply` records that it evaluates as
`A.ρ g`.

The context names the Library equivalence `Langlands.innerPullbackEquiv`. That
equivalence pulls back along the inverse inner automorphism, so it does not
match `pullbackRep` definitionally. The proof does not use it.

## Transport of the full transpose dual along an equivalence

The rest of the proof is general. It applies to any two representations
`A A' : Rep ℂ (GeneralLinear n F.Carrier)`, any block shape `B` and any
equivalence `e : A.ρ.Equiv A'.ρ`. All declarations are in the namespace
`Langlands.PadicField.TopologicalData`.

- `comp_symm_mem_subgroupInvariantDual`: if `f : Module.Dual ℂ A` is invariant
  under a subgroup `N`, then `f ∘ e⁻¹` is an `N`-invariant functional on `A'`.
  The proof uses the intertwining identity `e⁻¹ (A'.ρ x w) = A.ρ x (e⁻¹ w)`,
  which is Mathlib's `Representation.IntertwiningMap.isIntertwining` applied to
  `e.symm.toIntertwiningMap`.
- `dualJacquetTransport T B e` is a linear map from
  `Module.Dual ℂ (T.splitCentreOppositeJacquet B A)` to
  `Module.Dual ℂ (T.splitCentreOppositeJacquet B A')`. It is the composite of
  three maps: the published identification `splitCentreDualJacquetSourceEquiv`
  from the full algebraic dual of the normalized opposite Jacquet module to
  the opposite-unipotent-invariant source functionals; the restriction of
  `e.symm.dualMap` (`f ↦ f ∘ e⁻¹`) to invariant functionals, using the previous
  lemma; and the inverse of the identification for `A'`. This is the full
  transpose dual. The ordinary smooth contragredient is not used.
- `dualJacquetTransport_apply_mk`: on quotient classes, the transported
  functional evaluates as
  `φ' (splitCentreOppositeJacquetMk B A' w) = φ (splitCentreOppositeJacquetMk B A (e⁻¹ w))`.
  The proof rewrites through `splitCentreDualJacquetSourceEquiv` and
  `LinearEquiv.apply_symm_apply`.
- `dualJacquetTransport_injective`: the transport is injective. The quotient
  map `splitCentreOppositeJacquetMk B A` is surjective, so two functionals are
  equal if they agree on every class `mk v`. Evaluating the transported
  functionals at `mk (e v)` and using `e⁻¹ (e v) = v` recovers their values at
  `mk v`.
- `dualJacquetTransport_mem_eigenspace`: the transport maps
  `commutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ 1` into the
  corresponding space for `A'`, with the same `χ`. The published
  `mem_dualJacquet_eigenspace_iff` rewrites membership as the unnormalized
  source equation
  `φ (mk (A.ρ (leviEmbedding (blockScalarLevi a)) v)) = δ(a)⁻¹ * χ a * φ (mk v)`
  for every split-centre element `a` and vector `v`, where `δ` is
  `T.leviHalfModulus B`. The proof evaluates the transported functional by
  `dualJacquetTransport_apply_mk`. It commutes `e⁻¹` past the action of the
  embedded block scalar by the intertwining identity, and then applies the
  source equation for `A` at `e⁻¹ w`. The half-modulus factor and the
  character are the same on both sides because the shape and `χ` are the
  same.

## Exponents

`isDualJacquetExponent_of_equiv` proves that
`T.IsDualJacquetExponent B A χ` implies `T.IsDualJacquetExponent B A' χ`. The
open-kernel condition on `χ` is reused unchanged. For the nonvanishing of the
eigenspace, choose a nonzero `φ` in the eigenspace for `A`. Such a `φ` exists
because the eigenspace is not `⊥`: otherwise every member would be zero and
the eigenspace would equal `⊥` by `eq_bot_iff`. Its transport lies in the
eigenspace for `A'` and is nonzero by injectivity. Hence that eigenspace is not
`⊥` either.

`isDualJacquetExponent_iff_of_equiv` gets the converse by applying the same
lemma to `e.symm`. `isUnitaryDualJacquetExponent_iff_of_equiv` adds the norm-one
condition `∀ a, ‖(χ a : ℂ)‖ = 1`. That condition depends only on `χ`, so the
equivalence follows from `and_congr_left'`.

## Closing theorems

`glDualJacquetInnerConjugationNonunitary` introduces the binders of the
nonunitary statement and applies `isDualJacquetExponent_iff_of_equiv` with
`B = P.shape` and `e = P.pullbackEquiv A`. `glDualJacquetInnerConjugation`
does the same for the unitary statement with
`isUnitaryDualJacquetExponent_iff_of_equiv`. Neither theorem changes the
character: both sides of each equivalence use literally the same `χ`, and no
inversion or conjugation of `χ` is used.

## Provenance and scope

This is derived internal linear algebra: transport of an eigen-equation along
an isomorphism of representations. The motivation in S79 §0.3 (pp. 5–6) and
the paragraph before Corollary 4.5.11 (p. 189) supplies no Lean proof, and
nothing here is attributed to them as a verbatim theorem. The module proves
only the stated transport. It does not prove critical-to-minimal reduction,
finiteness of the spectrum, or any discrete-series or tempered support
result. It uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
