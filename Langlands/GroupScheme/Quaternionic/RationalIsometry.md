# Rational isometries of a quadratic form over an algebra with involution

Module `Langlands.GroupScheme.Quaternionic.RationalIsometry`.

## Setting

`K` is a field, `D` a division ring that is a `K`-algebra, and `σ` an involution of the
first kind of `D` (`FirstKindInvolution K D`). A `σ`-quadratic form on row vectors `D^n`
in the sense of Tits is an element `q = [Q]` of `σ.QuadraticForms n`, the quotient of
`M_n(D)` by Tits's subspace `{X - ᵗX^σ}` (`σ.quadraticKernel n`). Its polar form is
`h = σ.polar q = Q + ᵗQ^σ` and its values are `q(x) = [Q(x, x)]` in `D` modulo the
alternating subspace `{a - σ(a)}` (`σ.quadraticValue x q`). A matrix acts on row vectors on
the right, `x ↦ x u` (`x ᵥ* u`).

## Main definition

`rationalIsometryGroup σ q : Subgroup (Matrix n n D)ˣ` is the subgroup of units `u` with

  `u Q ᵗu^σ - Q ∈ {X - ᵗX^σ}`

for the chosen representative `Q = Quotient.out q`. This is exactly the condition that `u`
preserves the class of `Q` under the action `Q ↦ u Q ᵗu^σ`, i.e. the rational points of the
isometry group `O(q)` of Tits's σ-quadratic form (Tits, *Formes quadratiques, groupes
orthogonaux et algèbres de Clifford*, Invent. Math. 5 (1968), §1–2; the Library group
scheme `FirstKindInvolution.isometryGroup` uses the same condition on points).

## Results

* Alternating subspace: `τ a - a` is alternating; `d z τ(d)` is alternating when `z` is;
  alternating elements satisfy `τ z = -z`.
* Sesquilinear forms: negation/subtraction lemmas, `σ.sesqForm H eᵢ eⱼ = H i j`
  (`sesqForm_single_single`), and a Gram matrix is determined by its form
  (`matrix_eq_of_sesqForm_eq`).
* Tits's subspace: its elements have alternating diagonal values and are antihermitian;
  conversely, over a linearly ordered index type an antihermitian matrix with alternating
  diagonal lies in it (`mem_quadraticKernel_of_antihermitian`).
* `mem_rationalIsometryGroup_iff`: membership can be tested on any representative `Q`.
* `sesqForm_polar_vecMul_of_mem`, `quadraticValue_vecMul_of_mem`: rational isometries
  preserve `h` and the values of `q`.
* **Isometry criterion** `mem_rationalIsometryGroup_iff_forall` (with
  `mem_rationalIsometryGroup_of_forall`): for linearly ordered `n` (e.g. `Fin m`), a unit is
  a rational isometry of `q` iff it preserves `h(x, y)` for all `x, y` and `q(x)` for all `x`.

## Provenance

Internal. The subgroup is the set of rational points of Tits's isometry group written out
directly in matrix terms; the lemmas are elementary linear algebra used to verify that
explicit matrices (Eichler transformations, reflections, hyperbolic scalings in
`EichlerTransformations`) are isometries. They serve the proof of the Kneser–Tits property
for quaternionic spin groups (Task 5398).
