# Uniqueness of Whittaker functionals on the actual compact mirabolic model

Author: Worker 805.

This module proves that the space of Whittaker functionals on the actual
compact mirabolic model `Whittaker.mirabolicCompactInduced ψ n` (BZ76's
`τ_P⁰ = ind(P, U, Θ)`, §5.7, p.45) has dimension at most one, for every rank,
in the form of a *test vector*:

```lean
theorem Langlands.Whittaker.MirabolicWhittaker.exists_testVector
    {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [∀ m, NonarchimedeanGroup (Langlands.GeneralLinear m F)]
    [∀ m, LocallyCompactSpace (Langlands.GeneralLinear m F)]
    (ψ : UnitaryAdditiveCharacter F) (hψ : IsOpen {t : F | ψ.complex t = 1}) :
    ∀ n : ℕ, ∃ f₀ : MirabolicCompactFunctions ψ n,
      ∀ ℓ ∈ compactFunctionals ψ n, ℓ f₀ = 0 → ℓ = 0
```

Here `compactFunctionals ψ n` abbreviates the published
`Whittaker.functionals (Mirabolic.upperUnipotent n F) (mirabolicCharacter ψ n)
(mirabolicCompactInduced ψ n)`: linear functionals `ℓ` on the compact model with
`ℓ (ρ u f) = Θ(u) ℓ f` for every upper unipotent `u`, where `ρ` is right
translation and `Θ = mirabolicCharacter ψ n` is the standard character (the
product of `ψ` of the adjacent superdiagonal entries). Consequently
`ℓ ↦ ℓ f₀` is an injective linear map `compactFunctionals ψ n → ℂ`.
The rank index is the published one: `mirabolic n F` sits in
`GeneralLinear (n + 1) F`.

`isOpen_complex_eq_one` shows that the hypothesis `hψ` holds whenever `F` is a
nonarchimedean additive group (in particular for a p-adic field with its
canonical topology): `ψ` is continuous and unitary, and a subgroup on which
`‖ψ - 1‖ < 1/2` lies in the kernel because all powers of the value stay in that
ball (`complex_eq_one_of_forall_norm_pow_sub_one_lt`). The GL instances are
supplied for a p-adic field by `T.generalLinearNonarchimedean` and
`T.generalLinearLocallyCompactSpace`. Nontriviality of `ψ` is part of the
published structure `UnitaryAdditiveCharacter` and is used through
`exists_complex_ne_one`.

## Relation to the literature

BZ76, Proposition 5.15(b) (p.49), states that every P-homomorphism
`τ_P⁰ → τ_P` is proportional to the standard embedding; its proof (p.50) uses
Frobenius duality and `dim E_{U,Θ} = 1` for the space `E` of `τ_P⁰`, obtained
from the derivative calculus of 5.12(g). The present module proves the
"at most one" half of this dimension statement in dual form: the dual of
`E_{U,Θ}` is the space of Whittaker functionals. The proof is internal and does
not follow the derivative calculus; it is a direct induction on the rank over
the actual unnormalized models. It uses no minimality, scalar-Hom uniqueness,
or functional-multiplicity result, so it can feed those statements.

## Proof

Write `P_n = mirabolic n F`, `U_n = Mirabolic.upperUnipotent n F`, and
`CF_n` for `MirabolicCompactFunctions ψ n`, with evaluation
`mirabolicCompactEval ψ n`.

### Algebra (section `Algebra`)

The published successor embedding `successor : P_n → P_(n+1)` (`levi` of a
mirabolic matrix) maps `U_n` into `U_(n+1)` (`successor_mem_upperUnipotent`)
and preserves the standard character (`mirabolicCharacter_successor`). Upper
unipotent matrices of rank `n + 2` lie in the published plus subgroup
`plusSubgroup n F` (`upperUnipotent_le_plusSubgroup`), and the rank-`n + 2`
character factors as `ψ` of the final column entry times the rank-`n + 1`
character of the plus projection (`mirabolicCharacter_succ`). On radical
matrices `radicalElement x` the character is `ψ (x last)`
(`mirabolicCharacter_radicalElement`), and
`g * radicalElement x = radicalElement ((projection g) · x) * g`
(`mul_radicalElement`).

### Restriction (section `Restriction`)

`restriction ψ : CF_(n+1) →ₗ[ℂ] CF_n` sends `f` to `p ↦ f (successor p)`.
Covariance comes from `mirabolicCharacter_successor`; the open subgroup fixing
`f` is pulled back along the continuous successor map. For compact support,
cover the projected support of `f` by the image of a compact set `C`
(`leftQuotient_exists_isCompact_image`); any `successor p` in the support is
`u * c` with `u ∈ U_(n+1)` and `c ∈ C`, so `c` lies in the closed plus subgroup
and `[p] = [plusProjection c]`. The projected support of the restriction is
therefore inside the compact image of `C ∩ plusSubgroup` under the continuous
plus projection (`quotientSupport_restrictFun_subset`,
`isCompact_quotientSupport_restrictFun`). Restriction intertwines right
translation by `successor p` with right translation by `p`
(`restriction_translate`).

### Surjectivity of restriction (section `Extension`)

Given `f ∈ CF_n`, define on the plus subgroup
`plusValue f q = ψ (lastColumn q last) · f (plusProjection q)`; it is left
`U_(n+1)`-covariant (`plusValue_left`) and equals `f` on successor matrices
(`plusValue_successor`). For a subgroup `H` of `P_(n+1)`, `extendFun H f g` is
`plusValue f (g k⁻¹)` if some `k ∈ H` has `g k⁻¹ ∈ plusSubgroup`, and `0`
otherwise. Under the compatibility `IsExtensionGroup H f` (every `k ∈ H` in
the plus subgroup has `ψ (lastColumn k last) = 1` and its plus projection fixes
`f`), the value does not depend on the choice of `k` (`extendFun_eq`), the
function is left covariant (`extendFun_left`), right `H`-invariant
(`extendFun_right`), and restricts to `f` (`extendFun_successor`). If `H` is a
compact open subgroup, the projected support lies in the compact image of
`C × H` under `(c, k) ↦ [successor c · k]`, where `C` covers the support of `f`
(`isCompact_quotientSupport_extendFun`), using
`plus_eq_radicalElement_mul_successor`. So `extendCompact` lies in `CF_(n+1)`
and restricts to `f` (`restriction_extendCompact`).

A compatible compact open subgroup exists (`exists_extensionGroup`): with `K`
an open subgroup fixing `f`, the set of `g` with `projection g` in (an open set
inducing) `K` and `ψ (lastColumn g last) = 1` is an open neighbourhood of `1`
(here `hψ` is used), and `P_(n+1)` is nonarchimedean (`mirabolic_nonarchimedean`)
and locally compact, so it contains a compact open subgroup
(`compactOpenSubgroupBasis`). Hence restriction is surjective
(`restriction_surjective`).

### Whittaker functionals kill the restriction kernel (sections `Kernel`, `KernelVanishing`)

Let `rowOf g = lastRow (projection g)`; it is invariant under left
multiplication by `U_(n+1)` (`rowOf_upperUnipotent_mul`). Right translation by a
radical matrix multiplies values by a character of the row,
`f (g · radicalElement x) = ψ (rowOf g ⬝ᵥ x) · f g`
(`eval_mul_radicalElement`), while a Whittaker functional satisfies
`ℓ (ρ (radicalElement x) f) = ψ (x last) · ℓ f` (`functional_radicalElement`);
note `ψ (x last) = ψ (e_n ⬝ᵥ x)` with `e_n = lastRow 1`.

Suppose `restriction f = 0` and `K` is an open subgroup fixing `f`. If
`rowOf g` lies in `lastRow '' J` with `J = K.comap levi`, then by the published
`lastRow_mem_image_iff` (`LastRowCompactOrbit`) one can write
`g = radicalElement v · successor a · levi j` with `levi j ∈ K`, so `f g`
is a character value times `f (successor a) = 0`
(`eval_eq_zero_of_rowOf_mem`). The set `O = lastRow '' J` is open
(`isOpen_lastRow_image`) and contains `e_n`.

`functional_eq_zero_of_finset` is the symbol argument: given finitely many
pairs `(x_i, c_i)` with `c_i ≠ ψ (x_i last)`, every `h` whose nonzero values sit
at points `g` with `ψ (rowOf g ⬝ᵥ x_i) = c_i` for some `i` satisfies `ℓ h = 0`.
By induction on the finite set, `h' = ρ (radicalElement x) h - c · h` has values
`(ψ (rowOf g ⬝ᵥ x) - c) · h g`, so it satisfies the hypothesis for the smaller
set, while `ℓ h' = (ψ (x last) - c) · ℓ h` with a nonzero factor.

In `functional_eq_zero_of_restriction_eq_zero` the rows of points where `f`
is nonzero lie in the compact set `S = rowOf '' C \ O`. For `y ∈ S`, `y ≠ e_n`,
so choosing a coordinate where they differ and `t` with `ψ t ≠ 1` gives `x_y`
with `ψ (y ⬝ᵥ x_y) ≠ ψ (x_y last)`. The sets
`{z | ψ (z ⬝ᵥ x_y) = ψ (y ⬝ᵥ x_y)}` are open neighbourhoods of `y` (again by
`hψ`); a finite subcover of `S` gives the finite set for the symbol argument,
so `ℓ f = 0`.

### Induction (sections `Induction`, `TestVector`)

For rank zero (`P_0` trivial) a function nonzero at `1` spans the model, or
the model is zero (`exists_testVector_zero`). For the inductive step,
restriction is surjective and every rank-`n + 2` Whittaker functional `ℓ`
vanishes on its kernel, so `ℓ = ℓ' ∘ restriction` for a functional `ℓ'`
(`range_dualMap_eq_dualAnnihilator_ker_of_surjective`); `ℓ'` is again a
Whittaker functional because restriction intertwines `successor u` with `u`
and the characters agree (`exists_functional_comp_restriction`). If `f₀` is a
test vector of rank `n + 1`, any preimage `f₁` of `f₀` under restriction is a
test vector of rank `n + 2`: `ℓ f₁ = ℓ' f₀ = 0` forces `ℓ' = 0`, hence `ℓ = 0`
(`exists_testVector`).
