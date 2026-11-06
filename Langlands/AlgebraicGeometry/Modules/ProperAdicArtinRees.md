# A uniform Artin–Rees bound for Čech boundaries on proper schemes

This module proves the geometric input for Stacks Project Lemma 30.20.4(3)
(tag [02OB](https://stacks.math.columbia.edu/tag/02OB)). It is used in the
form that comment 11745 on that lemma gives, through Lemma 30.20.3 (tag
[02O7](https://stacks.math.columbia.edu/tag/02O7)). The final result is

`exists_uniform_cechBoundaryLift f M 𝒰 I p : ∃ c, ∀ n k, n + c ≤ k →
IdealAdic.CechBoundaryLift f M 𝒰 (I ^ k) (I ^ n) p`.

Its hypotheses are: `R : CommRingCat` noetherian; `f : X ⟶ Spec R` proper;
`M : X.Modules` quasi-coherent with finite sections over every affine open;
`𝒰` an arbitrary finite ordered affine cover of `X`; `I : Ideal R`; and
`p : ℕ`. The proposition `CechBoundaryLift` is the published one from
`ProperAdicCechKernelReduction`. Every alternating degree-`p` Čech cochain
`y` of `OModulePresheaf.ofModules f M` with `d y ∈ I^k • ⊤` has a cochain
`y' ∈ I^n • ⊤` with `d y' = d y`. Here `• ⊤` is taken in the `R`-module of
Čech cochains. The single bound `c` works for all `n` and `k`.

## Route

The Stacks argument uses the finite graded module `⊕ₙ H^p(X, Iⁿ F)` over
the Rees algebra `B = ⊕ₙ Iⁿ` (Lemma 30.20.1). The implemented proof uses the
same finiteness, but at the level of Čech cochains, which keeps one `c` for
all indices. It generalizes the ported FLT solution
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper`.
That solution treats only the structure sheaf in Čech degree `0`. This module
treats an arbitrary quasi-coherent module with finite affine sections in every
degree. Its scheme `P' = P ×_A Spec(B)` and pullback `P₁ = P' ×_B Spec(A[X])`,
the maps `fst'`, `π'`, `g`, the covers `K'` and the ring isomorphisms `ΦC` are
reused from that file's `SolKS` namespace.

## The base-change presheaf (section `BaseChange`)

For an FLT presheaf `F : OModulePresheaf π` over `Spec R` and an `R`-module
`S`, `baseChange F S` is the presheaf `U ↦ F(U) ⊗[R] S`. Sections act through
the first factor, and restriction is `res ⊗ id`. `toBaseChange F S s₀` is the
morphism `x ↦ x ⊗ s₀`. Two lemmas cover the FLT image presheaf
`OModulePresheaf.im (toBaseChange F S s₀)`:

- `isCoherent_im_toBaseChange`: the image has finite sections on affine opens
  if `F` does.
- `isQuasicoherent_im_toBaseChange`: the image satisfies the FLT
  localization conditions on basic opens of affine opens if `F` does.

The kernel half of the second lemma is `exists_pow_smul_eq_zero_baseChange`.
It uses that restriction to a basic open is a localization of modules, and
Mathlib's `IsLocalizedModule.rTensor`.

## The Rees presheaf (section `Rees`)

Let `A` be a commutative ring, `I` an ideal, `q : P ⟶ Spec A` and
`M : P.Modules`. Polynomials `A[X]` are an algebra over `B` through the
inclusion `B ⊆ A[X]` (`reesPolynomialAlgebra`). Then:

- `reesPullback I q M` is the actual module pullback `fst'^* M` on `P'`.
- `reesPullbackPresheaf` is its FLT presheaf of sections over `Spec B`.
- `reesTensor` is `baseChange (reesPullbackPresheaf I q M) A[X]`.
- `reesPresheaf I q M` is the image of `x ↦ x ⊗ 1`.

Over a Čech intersection `U = K.inter s` with preimage `W = (K' I q K).inter s`,
the construction compares these sections with polynomials whose coefficients
are sections of `M`. The comparison maps are additive maps into
`PolynomialModule Γ(P, U) Γ(M, U)`:

- `reesRho I q K s : Γ(P', W) →+* Γ(P, U)[X]` is `ΦC` composed with the
  pullback along `g`. It sends `fst'`-pullbacks of `c` to `C c`
  (`reesRho_fst`). It sends the image of `r ∈ B` to its polynomial with
  coefficients mapped into `Γ(P, U)` (`reesRho_algR`). It commutes with
  restriction to faces (`reesRho_res`). Its values lie in the Rees algebra of
  `I Γ(P, U)` (`reesRho_mem`).
- `reesTensorEquiv` is the published bijection
  `Γ(P', W) ⊗_{Γ(P,U)} Γ(M, U) ≃ Γ(W, fst'^* M)` (`pullbackTensorMap`).
  Through it, `reesPsi` sends `y ⊗ m` to `reesRho y • m X⁰`.
- `reesPsiT` sends `g ⊗ a` in `reesTensor` to `a • reesPsi g`, where `a` is
  mapped into `Γ(P, U)[X]`.
- `reesInv` sends `m Xʲ` to `fst'^* m ⊗ Xʲ`. Then `reesInv_psiT` proves
  `reesInv ∘ reesPsiT = id`, so `reesPsiT_injective`. The proof uses that
  `Γ(P', W)` is generated as a ring by the images of `Γ(P, U)` and `B`
  (`closure_eq_top` from the FLT file).

These maps satisfy the following:

- `reesPsiT_res`: coefficients commute with restriction to faces.
- `reesPsiT_rsmul`: the `B`-action multiplies by the polynomial of `r`.
- `reesPsi_coeff_mem`: the `j`-th coefficient of a pulled-back section lies
  in `Iʲ • ⊤`, as an `A`-submodule of `Γ(M, U)`.
- `exists_reesPsi_eq_single`: every `b ∈ Iᵏ • ⊤` is the `k`-th and only
  coefficient of some pulled-back section.

## Coefficient cochains

`reesCoeff i j z` is the Čech cochain of `M` formed by the `j`-th coefficients
of a Rees cochain `z`. It is additive. It commutes with the differentials
(`reesCoeff_d`) and satisfies the convolution formula for the `B`-action
(`reesCoeff_smul`). Its values lie in `Iʲ • ⊤` (`reesCoeff_mem`). For a cochain
`b` with components in `Iᵏ • ⊤`, `reesZ i k b hb` is a Rees cochain whose
coefficients are `b` in degree `k` and `0` elsewhere (`reesCoeff_reesZ`). If
`d b = 0` then `d (reesZ …) = 0` (`d_reesZ_eq_zero`), by injectivity of
`reesPsiT`.

## Uniform stabilization (sections `Rees` and `Main`)

The FLT argument is transcribed to Čech degree `i`. It uses the following
objects:

- `reesH` is the degree-`i+1` Čech cohomology of the Rees presheaf for the
  cover `K'`.
- `reesCls k b` is the class of `reesZ (i+1) k b` for a coboundary `b` with
  components in `Iᵏ • ⊤`.
- `reesN m` is the `B`-span of these classes with `k ≤ m`.

`reesGood_of_mem` shows that every class in `reesN c₀` has a representative
whose `j`-th coefficient is the coboundary of a cochain in `I^(j-c₀) • ⊤`.

The main estimate is `exists_uniform_d_eq_d I q M K i hFc hFq`. It assumes
`A` noetherian, `q` proper, `M` quasi-coherent, and the Rees presheaf
coherent and quasi-coherent. It gives one `c` such that, for every `n`, every
Čech coboundary `d w` with components in `I^(n+c) • ⊤` equals `d w'` for some
`w'` with components in `Iⁿ • ⊤`. The published
`OModulePresheaf.cechFinite_of_isProper` makes `reesH` a finite module over
the noetherian ring `B`, because `π' : P' ⟶ Spec B` is proper. The increasing
chain `reesN` stabilizes at some `c₀`, and `c = c₀` works.

The hypotheses on the Rees presheaf are discharged by
`isQuasicoherent_reesPresheaf`, using `isQuasicoherent_reesPullbackPresheaf`.
They are also discharged by `isCoherent_reesPresheaf`, using
`HasFiniteAffineSections.pullbackObj` from `PullbackFiniteAffineSections`.

## Boundary lifts

`mem_ideal_smul_top_pi_iff` states that, for a finite product of modules,
`x ∈ J • ⊤` holds exactly when every component is in `J • ⊤`.
`exists_uniform_cechBoundaryLift` specializes `exists_uniform_d_eq_d` to
`A = R` and `q = f`. It converts componentwise membership to membership in
the cochain module, and uses `I^k ≤ I^(n+c)` for `n + c ≤ k`.

## Provenance

This module is derived content. The proof is a Čech-level form of Stacks
Lemmas 30.20.1 and 30.20.3, generalizing the cited FLT port. No local-ring,
completeness, flatness or projectivity hypothesis is used. The cover `𝒰` in
the final theorem is arbitrary. Separatedness of `f` is used only through
properness.
