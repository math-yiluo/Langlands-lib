# Local monodromy at a closed point of a curve

Laumon (1987), (2.2.1), pp. 155–156: for a smooth connected curve `X` over `k` and a closed
point `x`, `G_x` is the Galois group of the henselian trait `X_(x)`, `I_x` its inertia group,
and for a sheaf `F` the stalk `F_η̄` with its `G_x`-action is the local monodromy of `F` at `x`.
The rank at `x` is `r_x(F) = dim F_x̄`; for `F = j_* G` with `G` lisse on a dense open, this is
the dimension of the inertia invariants. Lemme (2.4.2.1), p. 162, uses the same pullback to
the henselian trait for the ends of the Fourier lines. Laumon (0.4), p. 134, fixes the notation
`X_(x)` for the henselization and the geometric points `x̄`, `η̄_x`. This module states the
corresponding identifications for arithmetic lisse sheaves of weil-conjectures on an integral
curve over a finite field: the local monodromy as a restriction of the generic monodromy, its
comparison with the Library's local Galois groups at a completion, and the stalks of `j_* F` at
the closed point with their Galois action. These are the local restriction and completion
comparisons (b2) of the
[design note on Laumon's local Fourier bijection](../../../notes/henniart/laumon-local-fourier-weil-conjectures-design.md)
at a general closed point.

## The generic and local monodromy

Let `C` be an integral scheme, `U` a nonempty open, `F` a lisse sheaf
`AlgebraicGeometry.ProEtale.LisseSheaf ℓ U`, `K = K(C)` the function field and
`Ω = SeparableClosure K`.

- `intermediateField_isSepClosure` records that `Ω` is a separable closure of every
  intermediate field of `Ω/K`.
- `genericPoint_mem_open` proves that `U` contains the generic point of `C`, and
  `curveGenericPoint C U : Spec K → U` is Mathlib's `Scheme.Opens.fromSpecStalkOfMem` there.
- `genericMonodromy C U ℓ F` is the monodromy representation of `Ω ≃ₐ[K] Ω` on the stalk of `F`
  at the geometric generic point: `fieldMonodromyRepresentation` of
  `Langlands.Correspondence.Laumon.FieldMonodromy` applied to the pullback of `F` to `Spec K`.
  An element `σ` acts by transport along `Spec σ`, i.e. by pullback of sections along `Spec σ`
  (weil-conjectures's `galoisToAut` and `reparamStalkIso`).
- For an affine open `W` and a prime `Q` of the integral closure `B` of `Γ(C, W)` in `Ω`,
  `placeDecompositionField C W Q` is the fixed field `K_Q` of the stabilizer of `Q` in the
  Galois group (the decomposition group; Serre, *Local Fields*, I §7, p. 21). For `Q` maximal
  above a closed point `z`, `K_Q` is the fraction field of the henselian trait `X_(z)` of
  Laumon (0.4), and its completion is the completion of `K` at `z`.
- `henselianPoint C U W Q : Spec K_Q → Spec K → U` is the punctured henselian neighbourhood
  `η_z^h`, and `boundaryMonodromy C U ℓ W F Q` is the monodromy of the pullback of `F` to it, a
  representation of `Ω ≃ₐ[K_Q] Ω`: Laumon's local monodromy as pullback to `η_z^h` followed by
  the field monodromy (b1).

## The stalks of `j_* F` over the places above `z`

For a maximal ideal `Q` of `B` let `B/Q` be its residue field (a field by Mathlib's
`Ideal.Quotient.field`, installed as a local instance) and `(B/Q)^alg` its algebraic closure.

- `placeGeometricPoint C W hW Q : Spec (B/Q)^alg → Spec Γ(C, W) → C` is weil-conjectures's
  `Scheme.FiniteEtale.pointOfAlgebra` over the affine chart `hW.fromSpec`: the geometric point
  over the place `Q`. For `Q` above `z` it lies over `z`.
- `placeDirectImageStalk C U ℓ W hW Q F` is the stalk at this geometric point of `j_* F`, for
  `j : U → C` the open immersion and weil-conjectures's direct image
  `AlgebraicGeometry.ProEtale.adicLowerStar`, as an `E`-vector space, `E = PadicAlgCl ℓ`.
- `placeGeometricPoint_transport` proves that for a `Γ(C, W)`-algebra isomorphism
  `τ' : (B/Q)^alg ≃ (B/Q')^alg`, the point over `Q'` precomposed with `Spec τ'⁻¹` is the point
  over `Q`.
- `placeStalkTransport C U ℓ W hW Q Q' F τ'` is the resulting linear map from the stalk over `Q`
  to the stalk over `Q'`: pullback of sections along `Spec τ'`, built from weil-conjectures's
  `ProEtale.upperStarComp` and `ProEtale.globalSectionsUpperStarIso` by the formula of
  `ProEtale.reparamStalkIso`. For `Q' = Q` it is the action of the automorphism `τ'` of
  `(B/Q)^alg` on the stalk by transport of structure, in the same convention as the monodromy
  of lisse sheaves: the action of `σ` on the generic stalk is pullback along `Spec σ`.

## `BoundaryStalkInertiaStatement`

Let `k` be a finite field, `ℓ` a prime invertible in `k`, `C` an integral scheme over `Spec k`,
smooth of relative dimension one (Mathlib's `SmoothOfRelativeDimension 1`), `U` a nonempty open,
`F` a lisse sheaf on `U`, `z` a closed point and `W` an affine open containing `z`. The places
above `z` are the maximal ideals `Q` of `B` whose preimage in `Γ(C, W)` is the prime of `z`
(Mathlib's `IsAffineOpen.primeIdealOf`). This is the setting of weil-conjectures's
boundary-stalk results (`WeilConjectures.WeilSheaf.BoundaryStrictHenselization`, where the
inertia group of `Q` is Mathlib's `Ideal.inertia` and `B_Q^{I_Q}` is the strict henselization
at `z`). The statement has two parts.

**At every place `Q` above `z`:**

1. **Restriction.** `boundaryMonodromy` is equivalent to the restriction of `genericMonodromy`
   along `Ω ≃ₐ[K_Q] Ω → Ω ≃ₐ[K] Ω`: the stalk representation at the punctured henselian
   neighbourhood is the restriction along `π₁(η_z^h) → π₁(U)`.
2. **Completion.** There are a finite field `κ`, a ring map `ι₀ : K_Q → LaurentSeries κ`, a
   ring map `ι : Ω → SeparableClosure (LaurentSeries κ)` and an isomorphism of topological
   groups `φ` from the Galois group of `LaurentSeries κ` onto `Ω ≃ₐ[K_Q] Ω` such that:
   - `ι₀` has dense image for the `t`-adic topology of `κ((t))` (Mathlib's uniform structure
     on `LaurentSeries`), and `ι` extends `ι₀`;
   - `ι (φ σ a) = σ (ι a)`: `φ` is restriction of automorphisms along `ι`;
   - `ι` maps `B` into the valuation ring of the Library's `closureValuation`, and `Q` is the
     preimage in `B` of its maximal ideal (the elements of valuation less than one);
   - `φ` carries the Library's `absoluteInertia` exactly onto the elements of `Ω ≃ₐ[K_Q] Ω`
     whose image in `Ω ≃ₐ[K] Ω` lies in the inertia group `Ideal.inertia` of `Q`;
   - there is a ring isomorphism `ψ : B/Q ≃ AlgebraicClosure 𝓀`, `𝓀` the residue field of
     `LaurentSeries κ`, which is the reduction induced by `ι`: `ψ (b mod Q)` is the Library's
     `residueClosureEquiv` of the residue class of `ι b` in the Library's `closureIntegers`.
     It transports the action of `φ σ` on `B/Q` to the Library's `absoluteResidueHom σ`.

   Such an `ι₀` is a completion of `K_Q` at `Q`. The completed local ring of `C` at `z` is a
   complete discrete valuation ring of equal characteristic with finite, hence perfect,
   residue field `κ = κ(z)`, so it is isomorphic to `κ[[t]]` (Serre, *Local Fields*, II §4,
   Theorem 2, p. 33), and `K_Q` has the same completion as `K` at `z`. At each finite Galois
   level, the Galois group of the completion is the decomposition group (Serre, II §3,
   Theorem 1 and Corollary 4, pp. 30–31), the valuation rings correspond (Proposition 4,
   p. 32), and the decomposition group acts on the residue field with kernel the inertia
   group (I §7, Proposition 20, p. 21). The completed local ring has a canonical coefficient
   field: as `κ(z)` is perfect, its multiplicative system of representatives is a field, and it
   is the only field of representatives (Serre, II §4, Proposition 8 (i), (iii), (iv) and its
   application to Theorem 2, pp. 35–36). For `q = |κ(z)|` it consists of the roots of
   `X^q − X`. The identification with `κ[[t]]` depends on the choice of a uniformizer, so the
   statement asserts that a completion embedding exists. The transported local
   monodromy is the restriction of `boundaryMonodromy` along `φ`: Laumon's local monodromy
   followed by (b2). For the rational ends of the Fourier lines
   `Langlands.Correspondence.Laumon.Completion` gives a canonical completion.

**For all places above `z` together:** there is a family `f_Q` of `E`-linear maps from the stalk
of `j_* F` over `Q` to the generic stalk, one for each place `Q` above `z`, such that

3. **Inertia invariants.** Each `f_Q` is injective with image the invariants of the inertia
   group of `Q` in the generic monodromy;
4. **Galois equivariance.** For places `Q`, `Q'` above `z`, `τ` in the Galois group with
   `Q' = τ • Q`, and a `Γ(C, W)`-isomorphism `τ' : (B/Q)^alg ≃ (B/Q')^alg` extending the
   isomorphism `B/Q → B/Q'`, `b mod Q ↦ τ b mod Q'` induced by `τ`,
   `f_Q' ∘ placeStalkTransport τ' = genericMonodromy(τ) ∘ f_Q`.

For `Q' = Q`, clause 4 says that `f_Q` intertwines the action of the decomposition group of
`Q` on the stalk, through its action on the residue field `B/Q`, with the generic monodromy.
In particular it intertwines the residual Frobenius: a lift `σ` to the decomposition group of
geometric Frobenius at `z` acts on the stalk through `Spec` of its residue automorphism. For
`Q' ≠ Q` it is the compatibility with the change of geometric point. The specialization maps
`(j_* F)_{x̄_Q} → F_η̄` through the strict henselizations `B_Q^{I_Q} ⊂ Ω` form such a family:
`τ` maps the strict henselization at `Q` onto the one at `τ • Q`, compatibly with the residue
map `τ'` and with `Spec τ` on the generic point, and all three actions are pullback along
`Spec`. Clauses 3 and 4 are the arithmetic analogue of weil-conjectures's
`AlgebraicGeometry.WeilSheaf.exists_injective_stalk_directImage_range_eq_invariants` and
`AlgebraicGeometry.WeilSheaf.exists_stalk_directImage_linearMap_invariants`, which give the
inertia-invariant description and the equivariance for the Frobenius of a lisse Weil sheaf.

The statement is true for every choice of the chart `W`. Clause 3 requires `ℓ` invertible in
`k`, the standing assumption of weil-conjectures's boundary-stalk results.

## Declarations used

The module imports `Langlands.Correspondence.Laumon.FieldMonodromy`,
`Langlands.Correspondence.Laumon.Completion`, `WeilConjectures.RingTheory.InertiaIndEtale` and
`WeilConjectures.WeilSheaf.BoundaryStrictHenselization`. Beyond the imported modules of this
program it uses weil-conjectures's `AlgebraicGeometry.ProEtale.LisseSheaf.upperStar` (the pullbacks
of `F` to `Spec K` and `Spec K_Q`), `AlgebraicGeometry.ProEtale.adicLowerStar`,
`AlgebraicGeometry.ProEtale.stalkFunctor`, `AlgebraicGeometry.ProEtale.AdicSheaf.forget`,
`AlgebraicGeometry.ProEtale.upperStarComp`, `AlgebraicGeometry.ProEtale.globalSectionsUpperStarIso`,
`AlgebraicGeometry.Scheme.FiniteEtale.pointOfAlgebra` and
`AlgebraicGeometry.WeilCoefficients.toModuleCat`; Mathlib's `Ideal.inertia`,
`Ideal.Quotient.field`, `IsAffineOpen.primeIdealOf`, `IsAffineOpen.fromSpec`,
`Scheme.Opens.fromSpecStalkOfMem` and `Scheme.Spec.mapIso`; and the Library's
`Langlands.LocalGalois.SepClosed.absoluteInertia`, `absoluteResidueHom`, `closureValuation`,
`closureIntegers` and `residueClosureEquiv`, `Langlands.LocalGalois.localNormedField` (with
`localNormedField_ultrametric` and `localNormedField_complete`) and
`Langlands.Weil.Local.SepClosed.localResidueField`, with
`Langlands.LocalField.Laurent.valuativeRel` as a local instance. The weil-conjectures
declarations depend only on `propext`, `Classical.choice` and `Quot.sound` under
`#print axioms`; so do `AlgebraicGeometry.ProEtale.upperStar`,
`AlgebraicGeometry.ProEtale.adicLisseSheaf`, `AlgebraicGeometry.ProEtale.adicConstantSheaf`,
`AlgebraicGeometry.ProEtale.adicConstantSheaf.monObj` and
`AlgebraicGeometry.ProEtale.sheafMonoidalCategory`, to which the elaborated terms also refer
(through `LisseSheaf.upperStar` and the definitions behind `LisseSheaf` and `AdicSheaf`).
Every declaration of this module depends only on these three axioms.
