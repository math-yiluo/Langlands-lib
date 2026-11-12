# Scaled transporters of CM levels and their maps of Harris lattices

## Purpose and provenance

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Section 3, printed pp. 306-307, fixes for the algebraic representation
`(ρ, W)` a `K_ℓ`-stable `𝒪`-lattice `ℒ_W`, where `𝒪` is the ring of integers of
`L_ℓ`. Section 4, printed
pp. 309-311, forms the `ℓ`-adic sheaf `W̃ = lim ℒ̃_m ⊗ L_ℓ` from the
reductions `ℒ_m = ℒ / ℓ^m`. The lattice is stable only under the compact
level. A translation by an element `g` of the finite-adelic group, as in a
transporter between two levels, maps it to `ρ(g) ℒ`. This is a different lattice,
which lies in `ℓ^{-e} ℒ'` for some `e`. Therefore the maps of coefficient
systems induced by transporters need `ℓ` inverted, as the task statement
records. This file supplies the integral bookkeeping for this. It is a derived
construction: each transporter receives a power of `ℓ` that clears the
denominators. The resulting maps of lattices and of their torsion quotients are
strictly functorial. Later modules divide by the power of `ℓ` after inverting `ℓ`.

The Library's lattices are `harrisLattice ρ p U` (in
[HarrisLattice](../Coefficients/HarrisLattice.md)), for a compact open level `U` of
the finite-adelic group. Small CM levels (`SmallCMLevel D`) are compact open levels
of the opposite group `D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ`. The
coefficient system of a small CM level `U` uses the lattice of the ordinary level
`CompactOpenLevel.inverseOpposite U.obj`, on which `u ∈ U` acts by
`ι u = (unop u)⁻¹`, through `CompactOpenLevel.inverseOppositeEquiv` (see
[HarrisTaylorCMCoefficientReduction](HarrisTaylorCMCoefficientReduction.md)
and `cmHarrisTorsionSystem` in
[HarrisTaylorCMCoefficientDiagram](HarrisTaylorCMCoefficientDiagram.md)).
Throughout, `ℓ = harrisCoefficientPrime p` is the coefficient prime of the
rational place `p`, and `R = HarrisCoefficientIntegers K p = ∏_{λ | p} O_λ`.

## Existence of the scaling exponent

In namespace `Langlands.Shimura.Coefficients`:

* `exists_pow_smul_placeAction_mem`: at a place `l` above `p`, let `m` be a
  natural number of valuation `< 1` in `K_l`. For every finite-adelic element
  `g` and compact open levels `U` and `V`, there is `e` such that
  `m^e • ρ_l(g) x` lies in the compact-level lattice of `V` for every `x` in that
  of `U`. Proof: the lattice of `V` is open for the module topology of
  `K_l ⊗ W` (`algebraicCompactCoefficientLattice_isOpen`), and `m^e → 0` in
  `K_l` (`Valued.tendsto_zero_pow_of_v_lt_one`). Hence, for each of finitely
  many generators `s` of the lattice of `U`, eventually `m^e • ρ_l(g) s` lies in
  the lattice of `V`. The statement for all elements follows by induction over
  the span, using `O_l`-linearity of `ρ_l(g)`.
* `exists_pow_smul_harrisAdelic_mem`: if `m` has valuation `< 1` at every place
  above `p`, then for all `g`, `U` and `V` there is `e` with
  `m^e • ρ(g) x ∈ harrisLattice ρ p V` for all `x ∈ harrisLattice ρ p U`. Here
  `ρ(g) = ρ.harrisAdelic p g`. The proof takes the maximum of the place-wise
  exponents over the finitely many places above `p`. It uses the place-wise
  description of `harrisLattice` (`mem_harrisLattice`) and of the action
  (`harrisCoefficientEquiv_adelic`, `harrisProductAdelic_apply`).

## Transporters and admissible exponents

In namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`:

* `smallCMArrowElement D b` is `ι a = (unop a)⁻¹` for a transporter
  `b : V ⟶ U` of small CM levels with translating element `a = b.hom.element`.
  It is `1` for identities (`smallCMArrowElement_id`). For a composite,
  `ι(b' ≫ b) = ι(b') ι(b)` (`smallCMArrowElement_comp`): the element of
  `b' ≫ b` is the product `a' a` in the opposite group, and `ι` is a group
  homomorphism.
* `CMHarrisLatticeScaled D ρ p b e` is the proposition
  `∀ x ∈ ℒ_U, ℓ^e • ρ(ι b) x ∈ ℒ_V`, where `ℒ_U` is the lattice of
  `inverseOpposite U.obj`.
* `exists_cmHarrisLatticeScaled`: every transporter has an admissible exponent.
  This is `exists_pow_smul_harrisAdelic_mem` with
  `harrisCoefficientPrime_valued_lt_one`.
* `CMHarrisLatticeScaled.mono`: larger exponents stay admissible.
  `cmHarrisLatticeScaled_id`: `0` is admissible for identities.
  `CMHarrisLatticeScaled.comp`: if `e'` is admissible for `b' : W ⟶ V` and `e`
  for `b : V ⟶ U`, then `e + e'` is admissible for `b' ≫ b`.

## The category of scaled levels

`CMScaledLevel D ρ p` has objects pairs of a small CM level `level` and a natural
number `scale`. A morphism `X ⟶ Y` (`CMScaledLevel.Hom`) is a transporter
`hom : X.level ⟶ Y.level` with `X.scale ≤ Y.scale` (`le`), such that the
difference `Y.scale - X.scale` is admissible for it (`scaled`). Identities and
composites are those of transporters. The exponent condition of a composite is
`CMHarrisLatticeScaled.comp`, since the differences add. `CMScaledLevel.id_hom`
and `CMScaledLevel.comp_hom` state that the underlying transporters are the
identity and the composite.

Two kinds of morphisms are singled out:

* `CMScaledLevel.raise D ρ p U h : ⟨U, n⟩ ⟶ ⟨U, n'⟩`, for `h : n ≤ n'`, is the
  identity transporter, with exponent difference `n' - n`.
* `CMScaledLevel.Hom.shift f k : ⟨X.level, k + X.scale⟩ ⟶ ⟨Y.level, k + Y.scale⟩`
  is the transporter of `f` with both exponents raised by `k`.

## Maps of lattices

For `f : X ⟶ Y` with transporter `b`, `cmHarrisLatticeTransport D ρ p f` is the
`R`-linear map from the lattice of `Y.level` to the lattice of `X.level` given by
`x ↦ ℓ^(Y.scale - X.scale) • ρ(ι b) x` (`cmHarrisLatticeTransport_coe`). It is
the restriction of a map of the ambient coefficient module, so it is well defined
by `f.scaled`. Its properties:

* `cmHarrisLatticeTransport_id`: identities give the identity.
* `cmHarrisLatticeTransport_comp`: `transport (f ≫ g) = transport f ∘ transport g`,
  so the construction is a contravariant functor.
* `cmHarrisLatticeTransport_raise`: a raise acts as multiplication by
  `ℓ^(n' - n)`.
* `cmHarrisLatticeTransport_shift`: shifting both exponents does not change the
  map.
* `cmHarrisLatticeTransport_harrisAdelic`: if `y = ρ((ι b)⁻¹ g (ι b)) x`, then
  `transport f y = ρ(g) (transport f x)`. This is the equivariance of the map.

## Maps of torsion coefficient modules

The coefficient modules of the Library's CM coefficient systems at stage `k` are
the carriers of `(cmHarrisTorsionSystem D ρ p U ℓ).obj (op k)`, namely the
quotients `ℒ_U / I^k ℒ_U` for `I = harrisCoefficientScalarIdeal K p ℓ = (ℓ)`.
For `f : X ⟶ Y` and `k' ≤ k`, `cmHarrisTorsionTransport D ρ p f h` is the map of
`R`-modules from stage `k` of `Y.level` to stage `k'` of `X.level`. It reduces the
lattice map modulo `ℓ^k` (`AdicSystem.powerReduction`) and then reduces from
`ℓ^k` to `ℓ^{k'}` (`AdicSystem.transition`). On residues it is the residue of
the lattice map (`cmHarrisTorsionTransport_mk`). Its properties:

* `cmHarrisTorsionTransport_comp`: for `k'' ≤ k' ≤ k`, the map of `f ≫ g` from
  stage `k` to stage `k''` is the map of `g` from `k` to `k'` followed by the map
  of `f` from `k'` to `k''`.
* `cmHarrisTorsionTransport_id`: for an identity it is the transition map of the
  torsion system from `k` to `k'`.
* `cmHarrisTorsionTransport_raise`: for a raise it is `ℓ^(n' - n)` times that
  transition map.
* `cmHarrisTorsionTransport_comm`: if `u = a⁻¹ v a` in the opposite group, with
  `a` the translating element of the transporter, `u` in the level of `Y` and `v`
  in the level of `X`, then the map intertwines the action of `u` at stage `k`
  with the action of `v` at stage `k'`. The proof reduces to
  `cmHarrisLatticeTransport_harrisAdelic`, using
  `ι(a⁻¹ v a) = (ι a)⁻¹ ι(v) ι(a)`.

## Scope

The file constructs no sheaves and no cohomology. The transport maps of
coefficient sheaves over the CM tower, built from these torsion maps, and the
normalization by powers of `ℓ` after inverting `ℓ`, are separate constructions.
