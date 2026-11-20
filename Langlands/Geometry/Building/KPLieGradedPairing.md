# The residue pairing between `𝔤*_{x,r}` and `𝔤_{x,-r}`

This module records the pairing convention between the dual Moy–Prasad lattices
`𝔤*_{x,r}` of KP 13.3.1 and the lattices `𝔤_{x,-r}`. The pairing takes values
in the residue field. It is built for supplied data that satisfy the
periodicity hypothesis `IsPeriodic`. The module also proves that the pairing
is nondegenerate on both sides, under two further hypotheses: `𝔤_{x,-r}` is a
lattice (right side), and the filtration is left-continuous at `-r` (left side).

## Setting

`F` is a nonarchimedean local field with ring of integers `𝒪 = 𝒪[F]`, maximal
ideal `𝔪 = 𝓂[F]` and residue field `𝔣 = 𝓀[F]` (Mathlib's `ValuativeRel`
notations). `G` is a group scheme over `Spec F` with `[IsAffineHom G.X.hom]`,
and `𝔤 = GenericLie 𝒪[F] G` is its Lie algebra, viewed as an `𝒪`-module.
`𝔤* = Module.Dual F 𝔤` is the `F`-linear dual. `P : ParahoricBuildingData G`
and `L : P.LieFiltrationData` are supplied data. For `x : P.Apartment` and a
real `r`, the module uses the following Library declarations from
`Geometry.Building.KPLieFiltrationDual`:

- `𝔤_{x,r} = L.lieFiltrationReal x r`;
- `𝔤_{x,r+} = L.lieFiltrationPlusReal x r`, the supremum of the `𝔤_{x,s}` for
  `s > r`;
- `𝔤*_{x,r} = L.dualLieFiltration x r`, the `X ∈ 𝔤*` with `X(Y) ∈ 𝔪` for all
  `Y ∈ 𝔤_{x,(-r)+}`;
- `𝔤*_{x,r+} = L.dualLieFiltrationPlus x r`;
- the periodicity predicate `L.IsPeriodic`, which says
  `𝔤_{x,t+1} = 𝔪 • 𝔤_{x,t}` for `t ≥ 0`.

From `Geometry.Building.KPLieGradedAction` it uses the graded piece
`L.gradedLie x r` (`𝔤_{x,r}` modulo the inverse image of `𝔤_{x,r+}`), the
stabilizer `L.filtrationStabilizer x`, the coadjoint action `coadjoint`, the
representation `L.gradedAdjoint x r`, the left-continuity predicate
`L.IsLeftContinuousAt x t` (there is `s < t` with `𝔤_{x,u} ⊆ 𝔤_{x,t}` for every
`u` with `s < u ≤ t`) and its consequence `exists_lieFiltrationPlusReal_le`
(under periodicity, `𝔤_{x,s+} ⊆ 𝔤_{x,t}` for some `s < t`).

All declarations are in the namespace
`Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData`.

## Shifting by the maximal ideal

- `smul_mem_lieFiltrationReal_add_one hL ha hX`: under periodicity, if
  `a ∈ 𝔪` and `X ∈ 𝔤_{x,t}` for a real `t`, then `a • X ∈ 𝔤_{x,t+1}`. Write
  `n = ⌈-t⌉₊` for the shift used in `lieFiltrationReal`. The shift for `t + 1`
  is `n - 1` (`Nat.ceil_sub_one`). If `n = 0`, then `t ≥ 0`, the lattice at
  `t + 1` is `𝔤_{x,t+1} = 𝔪 • 𝔤_{x,t}` by periodicity, and `a • X` lies in it.
  If `n = k + 1`, both depths have the same shifted index `t + n`, and the
  condition for `a • X` at `t + 1` (`b • a • X ∈ 𝔤_{x,t+n}` for `b ∈ 𝔪^k`)
  follows from the condition for `X` at `t`, because `b a ∈ 𝔪^{k+1}`.

## Integrality

- `exists_integer_eq_apply hL hX hY`: under periodicity, for `X ∈ 𝔤*_{x,r}`
  and `Y ∈ 𝔤_{x,-r}`, there is `c ∈ 𝒪` with `c = X(Y)` in `F`. Proof: `𝒪` is
  a discrete valuation ring (Mathlib instance for nonarchimedean local fields),
  so it has a uniformizer `ϖ` with `𝔪 = ϖ𝒪`
  (`IsDiscreteValuationRing.exists_irreducible`, `irreducible_iff_uniformizer`).
  By the previous lemma `ϖ • Y ∈ 𝔤_{x,-r+1}`, and `-r + 1 > -r`, so the
  membership criterion `mem_dualLieFiltration` gives `ϖ X(Y) = X(ϖ • Y) ∈ 𝔪`.
  Writing `ϖ X(Y) = c ϖ` with `c ∈ 𝒪` and cancelling `ϖ ≠ 0` gives `X(Y) = c`.
- `exists_mem_maximalIdeal_eq_apply hX hY`: for `X ∈ 𝔤*_{x,r}` and
  `Y ∈ 𝔤_{x,(-r)+}`, `X(Y) ∈ 𝔪`. This is the definition of `𝔤*_{x,r}` and needs
  no hypothesis.
- `exists_mem_maximalIdeal_eq_apply_of_mem_dualLieFiltrationPlus hX hY`: for
  `X ∈ 𝔤*_{x,r+}` and `Y ∈ 𝔤_{x,-r}`, `X(Y) ∈ 𝔪`. By
  `mem_dualLieFiltrationPlus`, `X ∈ 𝔤*_{x,s}` for some `s > r`; then `-r > -s`
  and the criterion `mem_dualLieFiltration` applies to `Y`. No hypothesis is
  needed.
- `apply_smul_eq` and `smul_apply_eq`: `X(c • Y) = c X(Y)` and
  `(c • X)(Y) = c X(Y)` for `c ∈ 𝒪`.

## The pairing

- `pairingInteger hL x r X Y : 𝒪` is the element `c` above, chosen with
  `Classical.choose`. `coe_pairingInteger` says that its image in `F` is
  `X(Y)`. `pairingInteger_eq_iff` characterizes it: it equals `c` if and only
  if `c = X(Y)` in `F`. So the choice does not matter, since `𝒪 → F` is
  injective.
- **`lieDualPairing hL x r : 𝔤*_{x,r} →ₗ[𝒪] 𝔤_{x,-r} →ₗ[𝒪] 𝔣`** is the
  pairing `(X, Y) ↦ X(Y) mod 𝔪` (`LinearMap.mk₂`). Each of the four linearity
  conditions is proved with `pairingInteger_eq_iff`, after moving the scalar
  through the residue map (`IsLocalRing.ResidueField.algebraMap_eq`).
  `lieDualPairing_apply` gives its value as `residue c` for any `c ∈ 𝒪` with
  `c = X(Y)`.
- `lieDualPairing_eq_zero_of_mem_lieFiltrationPlusReal`: the pairing vanishes
  when `Y ∈ 𝔤_{x,(-r)+}`.
- `lieDualPairing_eq_zero_of_mem_dualLieFiltrationPlus`: the pairing vanishes
  when `X ∈ 𝔤*_{x,r+}`.
- `lieDualPairing_coadjoint`: for `g` in the stabilizer of the filtration,
  `⟨Ad*(g) X, Ad(g) Y⟩ = ⟨X, Y⟩`. Indeed
  `(Ad*(g) X)(Ad(g) Y) = X(Ad(g⁻¹) Ad(g) Y) = X(Y)` (`adjointF_inv_apply`).

## Descent to the graded piece

- **`gradedLieDualPairing hL x r : 𝔤*_{x,r} →ₗ[𝒪] gradedLie x (-r) →ₗ[𝒪] 𝔣`**
  is the pairing on `𝔤_{x,-r}/𝔤_{x,(-r)+}`, obtained with `Submodule.liftQ`
  from the first vanishing lemma. Its additivity and `𝒪`-linearity in `X`
  are checked on representatives (`Submodule.linearMap_qext`).
  `gradedLieDualPairing_mk` gives its value on a class, by `rfl`.
- `gradedLieDualPairing_eq_zero_of_mem_dualLieFiltrationPlus`: it vanishes for
  `X ∈ 𝔤*_{x,r+}`. So it depends on `X` only modulo `𝔤*_{x,r+}`.
- `gradedLieDualPairing_gradedAdjoint`: it is invariant under the stabilizer,
  with the coadjoint action on `𝔤*_{x,r}` and the representation
  `gradedAdjoint x (-r)` on the graded piece.

Under periodicity, `gradedLie x (-r)` is `𝔤_{x,-r}/𝔤_{x,(-r)+}` in KP's sense
(see `KPLieGradedAction`). The pairing therefore induces a pairing
`𝔤*_{x,r}/𝔤*_{x,r+} × 𝔤_{x,-r}/𝔤_{x,(-r)+} → 𝔣`. The module does not state
this as a map out of the quotient of `𝔤*_{x,r}`. It records instead the
vanishing lemma that makes it well defined.

## Nondegeneracy

The graded piece is killed by `𝔪`:

- `smul_mem_lieFiltrationPlusReal hL ha hY`: under periodicity, `a ∈ 𝔪` and
  `Y ∈ 𝔤_{x,t}` give `a • Y ∈ 𝔤_{x,t+}`, because `a • Y ∈ 𝔤_{x,t+1}` and
  `t + 1 > t` (`lieFiltrationReal_le_lieFiltrationPlusReal`).
- `isTorsionBySet_gradedLie hL x t`: under periodicity,
  `Module.IsTorsionBySet 𝒪 (gradedLie x t) 𝔪`.
- `exists_linearMap_residueField_ne_zero hL hY`: under periodicity, for a
  nonzero `Y` in `gradedLie x t` there is an `𝒪`-linear map
  `φ : gradedLie x t → 𝔣` with `φ Y ≠ 0`. Inside the proof the graded piece is
  made a vector space over the field `𝒪/𝔪` (`Module.IsTorsionBySet.module`,
  `Ideal.Quotient.field`), and `Module.forall_dual_apply_eq_zero_iff`
  produces the linear form.

Right side. The hypothesis is the instance argument
`[Submodule.IsLattice F (L.lieFiltrationReal x (-r))]` (Mathlib's
`Submodule.IsLattice`): `𝔤_{x,-r}` is a finitely generated `𝒪`-submodule
whose `F`-span is `𝔤`.

- **`gradedLieDualPairing_surjective hL`**: under periodicity and the lattice
  hypothesis, every `𝒪`-linear map `φ : gradedLie x (-r) → 𝔣` equals
  `gradedLieDualPairing hL x r X` for some `X ∈ 𝔤*_{x,r}`. Proof: the lattice
  `𝔤_{x,-r}` is a free `𝒪`-module (`Submodule.IsLattice.free`, `𝒪` being a
  principal ideal domain), hence projective, so `φ ∘ mkQ : 𝔤_{x,-r} → 𝔣`
  lifts through the residue map to an `𝒪`-linear `l : 𝔤_{x,-r} → 𝒪`
  (`Module.projective_lifting_property`). An `𝒪`-basis `b` of `𝔤_{x,-r}`
  (`Module.Free.chooseBasis`) is an `F`-basis of `𝔤`
  (`Module.Basis.extendOfIsLattice`). Let `X` be the `F`-linear form with
  `X(b_i) = l(b_i)` (`Module.Basis.constr`). Then `X = l` on `𝔤_{x,-r}`
  (`Module.Basis.ext`). Under periodicity `𝔤_{x,(-r)+} ⊆ 𝔤_{x,-r}`
  (`lieFiltrationPlusReal_le`), and on `𝔤_{x,(-r)+}` the residue of `l` is
  `φ` of the zero class, so `X(𝔤_{x,(-r)+}) ⊆ 𝔪` and `X ∈ 𝔤*_{x,r}`. The
  pairing of `X` with the class of `Y ∈ 𝔤_{x,-r}` is `residue (l Y)`, which is
  `φ` of that class.
- `exists_mem_dualLieFiltration_residue_ne_zero hL Y hY`: under periodicity
  and the lattice hypothesis, if `Y ∈ 𝔤_{x,-r}` is not in `𝔤_{x,(-r)+}`, there
  are `X ∈ 𝔤*_{x,r}` and `c ∈ 𝒪` with `c = X(Y)` and `residue c ≠ 0`: apply
  surjectivity to a map `φ` with `φ(class of Y) ≠ 0`.
- **`eq_zero_of_forall_gradedLieDualPairing_eq_zero hL h`**: under
  periodicity and the lattice hypothesis, if
  `gradedLieDualPairing hL x r X Y = 0` for every `X ∈ 𝔤*_{x,r}`, then `Y = 0`
  in `gradedLie x (-r)`.
- `ker_gradedLieDualPairing_flip hL`: the same statement as
  `LinearMap.ker (gradedLieDualPairing hL x r).flip = ⊥`.
- `mem_lieFiltrationPlusReal_iff_forall_dual hL hY`: under periodicity and the
  lattice hypothesis, for `Y ∈ 𝔤_{x,-r}`: `Y ∈ 𝔤_{x,(-r)+}` if and only if
  `X(Y) ∈ 𝔪` for every `X ∈ 𝔤*_{x,r}`. So `𝔤_{x,(-r)+}` is recovered from
  `𝔤*_{x,r}` as an annihilator inside `𝔤_{x,-r}`.

Left side.

- `gradedLieDualPairing_eq_zero_iff_forall hL X`: under periodicity,
  `gradedLieDualPairing hL x r X = 0` if and only if `X(Y) ∈ 𝔪` for every
  `Y ∈ 𝔤_{x,-r}`. No further hypothesis is needed.
- `mem_dualLieFiltrationPlus_of_forall hL hc hX`: under periodicity and left
  continuity at `-r` (`IsLeftContinuousAt`, defined in `KPLieGradedAction`), a
  linear form `X` with `X(𝔤_{x,-r}) ⊆ 𝔪` lies in `𝔤*_{x,r+}`. With `s < -r`
  from `exists_lieFiltrationPlusReal_le`, `X(𝔤_{x,s+}) ⊆ 𝔪`, so `X ∈ 𝔤*_{x,-s}`
  and `-s > r`.
- **`gradedLieDualPairing_eq_zero_iff hL hc X`**: under periodicity and left
  continuity at `-r`, `gradedLieDualPairing hL x r X = 0` if and only if
  `X ∈ 𝔤*_{x,r+}`.
- `ker_gradedLieDualPairing hL hc`: the same statement as
  `LinearMap.ker (gradedLieDualPairing hL x r) = 𝔤*_{x,r+} ∩ 𝔤*_{x,r}`
  (as `comap` along the inclusion of `𝔤*_{x,r}`).

Together, under the three hypotheses, the induced pairing
`𝔤*_{x,r}/𝔤*_{x,r+} × 𝔤_{x,-r}/𝔤_{x,(-r)+} → 𝔣` has zero kernel on both sides,
and `X ↦ gradedLieDualPairing hL x r X` is a surjective `𝒪`-linear map from
`𝔤*_{x,r}` onto the `𝒪`-linear maps `𝔤_{x,-r}/𝔤_{x,(-r)+} → 𝔣` with kernel
`𝔤*_{x,r+}`. By the first isomorphism theorem `𝔤*_{x,r}/𝔤*_{x,r+}` is
therefore isomorphic to that space of maps. The module states the
surjectivity and the kernel; it does not construct the isomorphism as a
declaration, because quotients of the subtype `𝔤*_{x,r}` meet an instance
mismatch (see `KPLieGradedAction`, where `dualGradedLie` is an image for the
same reason).

## Comparison with Kaletha–Prasad

KP 13.3.1 (printed p. 470; PDF p. 501) defines, for any real `r`,
"`𝔤*_{x,r} = {X ∈ 𝔤* | X(Y) ∈ 𝔪 for all Y ∈ 𝔤_{x,(-r)+}}`". KP do not state a
pairing between graded pieces in §13.3. The module derives it from this
definition. The definition gives the vanishing on `𝔤*_{x,r} × 𝔤_{x,(-r)+}`
directly. Integrality on `𝔤*_{x,r} × 𝔤_{x,-r}` uses the identity
`𝔤_{x,r+n} = 𝔪^n 𝔤_{x,r}` of KP 13.3.1 (Proposition 8.5.16 for the models
`𝒢_{x,r}`; printed p. 319, PDF p. 350), here the hypothesis `IsPeriodic`.
The valuation normalization is the Library's `localFieldOrder` with
`ord(Fˣ) = ℤ`, so the depth shift by `1` corresponds to multiplication by a
uniformizer. KP 13.3.4 (printed p. 471; PDF p. 502) gives the action of the
reductive quotient on `𝔤_{x,r}/𝔤_{x,r+}` and on `𝔤*_{x,r}/𝔤*_{x,r+}`. The
invariance lemmas express that the pairing is compatible with these actions,
at the level of the rational points that stabilize the supplied filtration.

Both nondegeneracy hypotheses are hypotheses on the supplied data. KP 13.3.1
says that `𝔤_{x,r}` "is an 𝔬-lattice in the k-vector space 𝔤(k)". For a
smooth supplied integral model, the Library proves that its Lie algebra is a
lattice (`Langlands.GroupScheme.IntegralModel.lieLattice_isLattice`); it does
not identify the supplied `𝔤_{x,r}` with such a Lie algebra. Left continuity
matches the convention that `𝔤_{x,r}` collects the root lattices `u_ψ` with
`ψ(x) ≥ r` (KP 13.3.3, a non-strict inequality), together with KP's statement,
for the groups `G(k)_{x,r}`, that the jumps of the filtration form a discrete
subset of ℝ (Introduction, printed p. xviii). Neither property is proved here
for KP's lattices.

The corrections of 1 November 2024 have no entry for §13.3 or §8.5.

## Provenance

Derived. The pairing, its integrality and its vanishing and invariance
properties are internal consequences of KP's definition of `𝔤*_{x,r}` and of
the periodicity hypothesis; no published statement is transcribed. The Lean
code uses the Library declarations listed in the Setting section and
`mem_lieFiltrationReal`, `mem_dualLieFiltration`, `mem_dualPairingSubmodule`,
`mem_dualLieFiltrationPlus`, `adjointF_apply` and `adjointF_inv_apply`. From
Mathlib it uses `IsDiscreteValuationRing.exists_irreducible`,
`IsDiscreteValuationRing.irreducible_iff_uniformizer`,
`Ideal.mem_span_singleton'`, `Nat.ceil_sub_one`, `IsLocalRing.residue`,
`IsLocalRing.residue_eq_zero_iff`, `LinearMap.mk₂`, `Submodule.liftQ` and
`Submodule.linearMap_qext`. For nondegeneracy it also uses
`lieFiltrationReal_le_lieFiltrationPlusReal`, `lieFiltrationPlusReal_le`,
`IsLeftContinuousAt`, `exists_lieFiltrationPlusReal_le`, and from Mathlib `Module.IsTorsionBySet.module`,
`Ideal.Quotient.field`, `Module.Free.of_divisionRing`,
`Module.forall_dual_apply_eq_zero_iff`, `Module.projective_lifting_property`,
`Submodule.IsLattice` with `Submodule.IsLattice.free`,
`Module.Free.chooseBasis`, `Module.Basis.extendOfIsLattice`,
`Module.Basis.constr` and `Module.Basis.ext`. No external code is adapted.

## Not claimed

- Periodicity is a hypothesis; Proposition 8.5.16 is not formalized.
- Nondegeneracy is proved only under the lattice and left-continuity
  hypotheses. Neither is derived from the supplied data.
- The isomorphism `𝔤*_{x,r}/𝔤*_{x,r+} ≅ Hom_𝒪(𝔤_{x,-r}/𝔤_{x,(-r)+}, 𝔣)` is
  not a declaration; only surjectivity and the kernel are stated. Nor is
  `𝔤*_{x,r} = {X | X(𝔤_{x,-r}) ⊆ 𝒪}` or any other duality between `𝔤_{x,r}`
  and `𝔤*_{x,-r}` beyond the annihilator statement above.
- The `𝔣`-vector-space structure of the graded pieces is not constructed as a
  declaration (it appears only inside a proof); the pairing is `𝒪`-bilinear
  with values in `𝔣`.
- Invariance is proved for the rational points that stabilize the supplied
  filtration, not for an algebraic action of the reductive quotient.
