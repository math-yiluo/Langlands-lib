# Inner forms of the special linear group are reduced-norm-one groups: proof

This module proves the published proposition
`Langlands.GroupScheme.SpecialLinearInnerFormNormOneStatement`:

> `theorem Langlands.GroupScheme.specialLinearInnerFormNormOne :
>   SpecialLinearInnerFormNormOneStatement.{u}`

Let `K` be a field, `G` a group scheme over `Spec K`, and
`d : QuasiSplitInnerForm G` a quasi-split inner-form presentation with an
isomorphism `i : d.model ≅ SL_{n+1}` over `K`. Write `L = d.carrier` for the
finite Galois splitting field, `q : d.model ⟶ d.adjoint` for the adjoint
quotient, `ξ = d.cocycle` for the adjoint discrepancy cocycle on `Spec L`, and
`ℓ = d.localIso` for the given local isomorphisms `d.model ≅ G` over points of
`Spec L`. The proof builds a central simple `K`-algebra `A` of reduced degree
`n + 1` by Galois descent of `M_{n+1}(L)`, and then shows `G ≅ normOne K A`
by descending local isomorphisms with the same discrepancy.

The proof uses the Library's matrix action of adjoint points from
`Langlands.GroupScheme.SpecialLinearInnerForm.AdjointMatrix` (Worker 227) and two
helper modules submitted with this proof:
`Langlands.GroupScheme.SpecialLinearInnerForm.GaloisDescent` (Galois descent of
algebras) and `Langlands.GroupScheme.SpecialLinearInnerForm.NormOneChart`
(reduced-norm-one points as determinant-one matrices through a chart). It does
not use any type-A or local Kneser–Tits input.

## Step 1: Galois values of the cocycle

`galoisValue d σ := ξ(𝟙, Spec σ) : Spec L ⟶ d.adjoint` for `σ ∈ Gal(L/K)`.
`galoisValue_one` gives `galoisValue d 1 = 1` (`Cocycle.toFun_self`), and
`galoisValue_mul` gives the crossed-homomorphism rule
`c_{στ} = c_σ · (Spec σ ≫ c_τ)`. This follows from the cocycle identity
`ξ(𝟙, Spec σ ≫ Spec τ) = ξ(𝟙, Spec σ) · ξ(Spec σ, Spec σ ≫ Spec τ)` together with
naturality of `ξ` along `Spec σ`.

## Step 2: the twisted Galois action and the algebra `A`

`galoisMatrixHom d i σ := adjointMatrixHom d.isAdjointQuotient i (galoisValue d σ)`
is the `L`-algebra endomorphism of `M_m(L)` by which the adjoint point `c_σ`
acts. On determinant-one matrices it is the given inner action, and after a
local lift it is conjugation by a lift of `c_σ`. `twistedAction d i` is the
`SemilinearGaloisAction K L (Matrix m m L)` with

`act σ x = galoisMatrixHom d i σ (x.map σ)`.

* Semilinearity: `x.map σ` sends the scalar matrix of `l` to that of `σ l`, and
  `galoisMatrixHom` is `L`-linear.
* `act 1 = id`: by `galoisValue_one` and `adjointMatrixHom_one`.
* `act (σ τ) = act σ ∘ act τ`: by `galoisValue_mul` and `adjointMatrixHom_mul`,
  we have `act (στ) x = α_{c_σ}(α_{Spec σ ≫ c_τ}(x.map (στ)))`. By
  `adjointMatrixHom_naturality` along `σ`,
  `(α_{c_τ}(x.map τ)).map σ = α_{Spec σ ≫ c_τ}((x.map τ).map σ)`.

`A := (twistedAction d i).fixed` is the fixed `K`-subalgebra. By the
GaloisDescent module it is finite-dimensional, central (`M_m(L)` is central over
`L` and nontrivial for nonempty `m`) and simple. With the identity chart,
`reducedDegree_fixed` gives `reducedDegree K A = n + 1`. The descent chart is
`ε := descentEquiv : L ⊗[K] A ≃ₐ[L] M_m(L)`, with `ε(1 ⊗ a) = a`.

## Step 3: the key chart identity

`extendMatrix_chartAlong_galois`: for any ring map `f : L → R` over `K`, all
`σ` and all `x ∈ R ⊗[K] A`,

`extendMatrix f α_{c_σ} (chartAlong ε (f ∘ σ) x) = chartAlong ε f x`.

Both sides are additive in `x`. On `r ⊗ a` the left side is
`r • (α_{c_σ}(a.map σ)).map f` (by `extendMatrix_map`), and
`α_{c_σ}(a.map σ) = act σ a = a` because `a` is fixed.

## Step 4: chart local isomorphisms with the same discrepancy

`chartLocalIso d i : LocalGroupIso d.model (normOne K A) (Spec L)` sends a point
`g` over `s : V ⟶ Spec L` to the norm-one point whose chart matrix along
`pointScalars s` is the SL-matrix `pointMatrix i V g`:
`(normOneChartPoints ε s).symm (pointMatrix i V g)`. Naturality follows from
`pointMatrix_naturality` and `normOneChartPoints_naturality`.

`chartLocalIso_galois`: for every `σ`, `s` and `g`,
`chartLocalIso_s(act(s ≫ c_σ) g) = chartLocalIso_{s ≫ Spec σ}(g)`. By Worker
227's `pointMatrix_innerAction`, the matrix of `act(s ≫ c_σ) g` is
`extendMatrix (sectionMap s) α_{c_σ}` applied to the matrix of `g`. By
`pointScalars_comp_ringTestMap`, the chart along `s ≫ Spec σ` is the chart along
`pointScalars s ∘ σ`. The identity then reduces to Step 3.

`chartLocalIso_hasDiscrepancy`: `chartLocalIso d i` has discrepancy `ξ` for the
inner action of the adjoint quotient. By `hasDiscrepancy_iff_overlap` it
suffices to check the universal overlap equation for `ξ.overlap`. By
`hasOverlapDiscrepancy_of_galois` it suffices to check that equation on the
Galois pairs `(𝟙, Spec σ)`, where `galoisPair σ ≫ ξ.overlap = galoisValue d σ`
(`toFun_eq_lift_overlap`). This is exactly `chartLocalIso_galois`.

## Step 5: descent

`compareLocalIso d i : LocalGroupIso G (normOne K A) (Spec L)` is
`b ↦ (ℓ_b)⁻¹ ≫ chartLocalIso_b`, which is natural because both factors are.
`compareLocalIso_isIndependent` holds because both local isomorphisms have
discrepancy `ξ`. Write `h = ℓ_c g`. Then `ℓ_b⁻¹ h = act(ξ(b,c)) g` by
`d.hasDiscrepancy`, and `chartLocalIso_b(act(ξ(b,c)) g) = chartLocalIso_c g` by
Step 4. Since `Spec L → Spec K` is surjective, flat and quasi-compact
(`fieldExtension_fpqc`), `LocalGroupIso.descend` gives
`normOneIso d i : G ≅ normOne K A`.

The main theorem supplies `A` with its canonical subalgebra instances, the
reduced degree from Step 2, and `normOneIso d i`. The only axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

This is the classical fact that inner forms of `SL_{n+1}` are the groups
`SL_1(A)` for central simple algebras `A` of degree `n + 1`. The argument is
twisted Galois descent of the matrix algebra (as in Serre, *Galois Cohomology*
III.1 and Knus–Merkurjev–Rost–Tignol, *The Book of Involutions* §26). The Lean
route here is self-contained: it uses Galois descent of algebras and the
local-isomorphism descent machinery of the Library, and uses no Skolem–Noether
theorem, because the adjoint action on matrices comes from the published
`adjointMatrixHom`.
