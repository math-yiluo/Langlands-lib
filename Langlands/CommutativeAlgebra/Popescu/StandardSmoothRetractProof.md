# Proof: smooth algebras are retracts of standard smooth algebras

`Langlands.CommutativeAlgebra.Popescu.StandardSmoothRetract.standardSmoothRetract :
StandardSmoothRetractStatement.{u}` proves the statement
`Langlands.CommutativeAlgebra.Popescu.StandardSmoothRetractStatement` (Stacks Project,
*Smoothing Ring Maps*, Lemma 3.4, Tag 07CH) for every universe `u`. The proof uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Route

Stacks (*Smoothing Ring Maps*, Lemma 3.4, printed pp. 7–8) first replaces `A` by a
vector bundle `C` over `A` that is a relative global complete intersection (Lemma 3.3),
then takes the polynomial ring `B' = C[y_1, …, y_c]` with coordinates
`z_i = x_i − Σ_j c_ij y_j` built from a splitting `t` of the conormal sequence of `C`,
finds by Nakayama a `g ∈ 1 + (y_1, …, y_c)` with `R[z_1, …, z_n] → B'_g` unramified,
proves it étale with the fibrewise flatness criterion, and concludes with Algebra,
Lemma 143.2.

The Lean proof keeps the shape of this argument (a vector bundle with its zero-section
retraction, explicit coordinates `z_i`, and a Nakayama element `g` congruent to `1`
modulo the ideal of the zero section) but differs in three ways: it uses a single vector
bundle over `A` itself, cut out by an idempotent splitting `A^n → Ω[A⁄R]`; it proves that
`Ω[B⁄R]` is free on the `d z_i` instead of proving étaleness; and it obtains standard
smoothness from Mathlib's `Algebra.IsStandardSmooth.of_basis_kaehlerDifferential`, which
needs only finite presentation, a trivial `H1Cotangent R B` and a basis of `Ω[B⁄R]`
consisting of differentials of elements.

Let `A` be smooth over `R`.

1. **Generators and an idempotent.** `Algebra.FiniteType.iff_quotient_mvPolynomial''`
   gives a surjection `f : R[X_1..X_n] → A`; put `a_k = f(X_k)`. The map
   `rho : A^n → Ω[A⁄R]`, `e_k ↦ d a_k`, is surjective (`rho_surjective`). Since
   `Ω[A⁄R]` is projective (smoothness), `Module.projective_lifting_property` gives a
   section `s` of `rho`. Then `p = id − s ∘ rho` is an idempotent endomorphism of `A^n`
   with `rho ∘ p = 0`, every `ω` has a preimage `b` with `p b = 0`, and `rho w = 0`,
   `p w = 0` imply `w = 0`.

2. **The vector bundle `C`.** `Cr p = A[X_1..X_n] ⧸ (X_i − Σ_j (p e_i)_j X_j)` (`relIdeal`,
   `Cr`). It is finitely presented over `A` (`Algebra.FinitePresentation.quotient`), and
   formally smooth because the quotient map splits: `sec : C → A[X]`, `X_i ↦ L(p e_i)`
   where `L v = Σ_j v_j X_j`, is a section (`mk_sec`), so
   `Algebra.FormallySmooth.of_split` applies (`smooth_Cr`). Hence `C` is smooth over `A`
   and, by composition, over `R`. The augmentation `eps : C → A`, `X_i ↦ 0`, is an
   `A`-algebra map; `J` denotes its kernel.

3. **The differentials of `C`.** Let `x_i` be the image of `X_i` in `C`,
   `z_i = a_i − x_i`, and `psi : C^n → Ω[C⁄R]`, `e_i ↦ d z_i`.
   - `top_le_range_psi_sup`: `psi` is surjective modulo `J • Ω[C⁄R]`. For `y ∈ A` choose
     `b` with `rho b = d y` and `p b = 0`. Then `d y = Σ b_k d a_k` in `Ω[C⁄R]`
     (via `KaehlerDifferential.map`), and `Σ b_k x_k = 0` in `C` (from
     `linForm_sub_mem`), so `Σ b_k d x_k = −Σ x_k d b_k ∈ J • Ω`. With
     `d a_k = d z_k + d x_k` this puts `d y` in `range psi + J • Ω`; then `d x_i` and, by
     induction over polynomials, every `d c` lies there.
   - `mem_smul_top_of_psi_eq_zero`: the kernel of `psi` lies in `J • C^n`. If
     `psi v = 0`, set `w = eps ∘ v ∈ A^n`. Pushing along `eps` (with
     `KaehlerDifferential.map`) gives `rho w = 0`. The `A`-algebra map
     `sig : C → A ⊕ ε A^n` (trivial square-zero extension, `X_i ↦ ε p e_i`) has first
     component `eps` (`sig_fst`), so its second component is an `R`-derivation
     `δ : C → A^n` with `δ z_i = −p e_i`; applying `δ.liftKaehlerDifferential` gives
     `p w = 0`. Hence `w = 0`, i.e. every `v_i ∈ J`.

4. **Nakayama.** `exists_smul_range_and_smul_ker` (for `φ : M → N`, `M` finite, `N`
   finite projective, surjective modulo `J` with kernel in `J • M`) produces `g` with
   `g − 1 ∈ J`, `g • N ⊆ range φ` and `g • ker φ = 0`. It uses
   `Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup` for the cokernel, a
   projective lifting `t` with `φ ∘ t = r •`, and
   `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` on the finitely
   generated submodule `range(r • id − t ∘ φ)`, which contains `r • ker φ`. Here it is
   applied to `psi`; `Ω[C⁄R]` is finite projective since `C` is smooth over `R`.

5. **Localization.** `B = Localization.Away g`. It is smooth over `C`
   (`Algebra.Smooth.of_isLocalization_Away`), hence over `A` and `R`. Since
   `Ω[B⁄R]` is the localization of `Ω[C⁄R]` at `g` (`KaehlerDifferential.map` is an
   `IsLocalizedModule` instance), `bijective_of_isLocalizedModule` shows that
   `B^n → Ω[B⁄R]`, `e_i ↦ d z_i`, is bijective. So `Ω[B⁄R]` has the basis `d z_i`, and
   `Algebra.IsStandardSmooth.of_basis_kaehlerDifferential` gives that `B` is standard
   smooth over `R`; its other hypotheses (`B` finitely presented over `R` and
   `H1Cotangent R B` trivial) are instances supplied by `Algebra.Smooth R B`.

6. **Retraction.** `eps g = 1` because `g − 1 ∈ J`, so `eps` extends to the `A`-algebra
   map `IsLocalization.liftAlgHom : B →ₐ[A] A`.

## Auxiliary declarations

All are in namespace `Langlands.CommutativeAlgebra.Popescu.StandardSmoothRetract`:
`exists_smul_range_and_smul_ker`, `linForm`, `relIdeal`, `Cr`, `eps`, `sig`, `sec`,
`smooth_Cr`, `rho`, `rho_surjective`, `xx`, `zz`, `psi`, `top_le_range_psi_sup`,
`mem_smul_top_of_psi_eq_zero`, `bijective_of_isLocalizedModule`, and small helper lemmas
(`linForm_single`, `aeval_linForm`, `relIdeal_fg`, `linForm_sub_mem`, `relIdeal_le_ker`,
`eq_sum_single`, `sum_smul_map_single`, `eps_mk_X`, `sig_mk_X`, `sig_fst`, `mk_sec`,
`mk_linForm`). These are internal to this proof and not claimed as Library results.
