# The existence theorem for norm groups containing n-th powers

`Langlands/GaloisCohomology/Local/Duality/Existence.lean`, namespaces `Langlands.ProfiniteCohomology` (characters of degree one) and `Langlands.GaloisCohomology.Local`.

**Theorem.** Let `K` be a nonarchimedean local field, `Ksep` a separable closure (`K Ksep : Type u`, any universe `u`), `n`
an integer invertible in `K` and `H ⊆ Kˣ` a subgroup containing `Kˣⁿ`. Then there is a finite abelian
extension `E` of `K` inside `Ksep` with norm group `N(Eˣ) = H`
(`exists_isAbelianGalois_fieldNormSubgroup_eq`; the norm group is the NYLL copy's
`LocalFieldTheory.DiscreteValuationField.fieldNormSubgroup`).

The proof is the Kummer argument through local duality in degree one (`Duality/Main.lean`). Over the
fixed field `E₀` of an open subgroup `U`, let `X = H¹(U, ℤ/n)`, `Y = H¹(U, μ_n)`; the Kummer map
`E₀ˣ → Y` is onto with kernel `E₀ˣⁿ`, and the cup product `X × Y → H²(U, μ_n) ≅ ℤ/n` is perfect. For
`A ⊆ X` the annihilator of the image `S` of `H`, let `N` be the common kernel of the characters of
`A` and `F` its fixed field. A norm from `F` is a norm from the field of each character of `A`, so
(cup product criterion of `KummerCup.lean`) its Kummer class is orthogonal to `A`, hence lies in `S`
(double annihilator), and the unit lies in `H`. On the other side `[E₀ˣ : N(Fˣ)] = [F : E₀]` (norm
index) `= |Gal/N| ≤ |Hom(A, ℤ/n)| ≤ |A| = |Y/S| = [E₀ˣ : H]`. Hence `N(Fˣ) = H`. The statement over
`K` follows from `U = ⊤`, whose fixed field is `K`.

## Declarations

The counting lemmas on perfect pairings of finite groups used here (`card_annihilator_left`,
`leftAnnihilator`, `mem_of_forall_leftAnnihilator`, `card_quotient_le_of_pairing`) are in the
module `Langlands.Cohomology.Profinite.Duality.DualModule`.

Characters of degree one (namespace `Langlands.ProfiniteCohomology`):

- `zmodCocycleHom_sub`, `zmodCocycleHom_add`, `zmodCocycleHom_eq_of_cohomologyπ_eq` (for trivial
  coefficients a class of degree one determines its cocycle).

Local fields (namespace `Langlands.GaloisCohomology.Local`):

- `unitsInvariantOpen_mul`, `unitsInvariantOpen_injective`; `kummerHom hn U : E₀ˣ →+ H¹(U, μ_n)`,
  `kummerHom_apply`, `kummerHom_surjective`, `exists_pow_eq_of_kummerHom_eq_zero`.
- `classChar U x : Gal(Ksep/E₀) → ℤ/n` (the character of a class of `H¹(U, ℤ/n)`), with
  `classChar_cohomologyπ`, `classChar_add`, `classChar_mul`, `classChar_one`, `classChar_inv`,
  `mem_charKer_openChar_iff`, `isOpen_charKer_openChar`.
- `mem_of_kummerHom_mem_map hn U hH b hb`: for `H ⊇ E₀ˣⁿ`, a unit whose Kummer class lies in the
  image of `H` lies in `H`; `card_quotient_map_kummerHom hn U hH`: `Y` modulo the Kummer image of `H`
  has `[E₀ˣ : H]` elements.
- `finiteDimensional_isAbelianGalois_fixedField_of_commutator_mem N hNnormal hNopen hcomm`: the fixed
  field of an open normal subgroup of `Gal(Ksep/E)` containing all commutators is a finite abelian
  extension of `E`.
- `fieldNormSubgroup_eq_of_le_of_finrank_le U F H hle hHpos hfinrank`: a subgroup `H` of finite index
  of `E₀ˣ` containing the norm group of a finite abelian extension `F` with `[F : E₀] ≤ [E₀ˣ : H]` is
  that norm group (norm index, `index_fieldNormSubgroup_of_isAbelianGalois`).
- `exists_fieldNormSubgroup_eq_of_range_pow_le hn U H hH`: the existence theorem over the fixed field
  of an open subgroup, from the four lemmas above.
- `exists_isAbelianGalois_fieldNormSubgroup_eq K Ksep hn H hH`: the existence theorem over `K`.

## Source and licence

New file, no text of the repository `leanprover-community/riemann-hypothesis`. The source proves
the existence theorem for all open subgroups of finite index with its own Lubin–Tate theory
(`src/GroundTheory/LocalFields/Existence.lean`), and uses it for the right kernel of local duality;
here it is proved only for subgroups containing `Kˣⁿ`, after local
duality (whose right kernel is controlled by counting, `Duality/Main.lean`).

## References

- J.-P. Serre, *Local Fields*, chapter XIV, §6 (the existence theorem), pp. 218–219.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §2, Theorem
  (7.2.6) (Tate duality, stated for `p`-adic fields), p. 380.
