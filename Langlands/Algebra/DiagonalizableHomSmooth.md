# Smoothness of homomorphisms out of a finite diagonalizable group

Module `Langlands.Algebra.DiagonalizableHomSmooth`, namespace `Langlands.FiniteBialgebraHom`.

## Statement and provenance

Let `R` be a commutative ring and `A` a commutative Hopf algebra over `R`. Assume `A` is finitely
presented and formally smooth over `R`. Let `M` be a finite abelian group, all in the same
universe as `R`, and write `R[M]` for `AddMonoidAlgebra R M`. The main results are the instances

- `formallySmooth_homAlgebra : Algebra.FormallySmooth R (HomAlgebra R A R[M])` and
- `smooth_homAlgebra : Algebra.Smooth R (HomAlgebra R A R[M])`.

`HomAlgebra R A P` is from `Langlands.Algebra.FiniteBialgebraHom`. Its `R`-algebra maps to `C`
are the Hopf points `A → C ⊗[R] P` (`homEquiv`). Geometrically, `Spec A` is a smooth affine group
`G` over `R`, `Spec R[M]` is the diagonalizable group `D(M)`, and `Spec (HomAlgebra R A R[M])`
represents the functor `Hom_gr(D(M), G)`. The result is therefore the case of SGA 3, Exp. XI,
Prop. 2.1 / Cor. 4.2 in which `H = D(M)` is finite diagonalizable and `G` is smooth and affine.
SGA 3 states that `Hom_{S-gr}(H, G)` is formally smooth for `H` of multiplicative type and `G`
smooth, and refers to Exp. IX 3.6, where it is deduced from the vanishing of Hochschild cohomology.

The proof here is internal to the project and takes a different route. `M`-characters act on the
Weil restriction that parametrizes all algebra maps `A → C ⊗[R] R[M]`. Hopf points are exactly
the normalised fixed points. The Library's fixed-point lifting for diagonalizable actions on
formally smooth algebras (`CharacterAction.exists_fixed_lift`) then lifts Hopf points through
square-zero thickenings.

The file is infrastructure for the torus case of SGA 3, Exp. XI, 4.1, which is the task "Prove
smooth moduli of actual closed torus subgroups".

## Convolution group (`section ConvGroup`)

- `convGroup` puts a group structure on `WithConv (A →ₐ[R] D)` for a commutative Hopf algebra `A`
  and a commutative `R`-algebra `D`. The monoid structure is Mathlib's convolution monoid, and the
  inverse of `f` is `f ∘ S`, with `S` the antipode. Mathlib's `AlgHom.convGroup` would require a
  bialgebra structure on the target, which `C ⊗[R] R[M]` lacks here. The proof of
  `inv_mul_cancel` uses `LinearMap.antipode_mul_id`. `convGroup` is a local instance, not a global
  one.
- `postComp h` is postcomposition with an algebra map `h : D →ₐ[R] E`, as a monoid hom
  `WithConv (A →ₐ[R] D) →* WithConv (A →ₐ[R] E)`. It preserves products by Mathlib's
  `AlgHom.comp_convMul_distrib`. The lemmas `postComp_apply`, `postComp_postComp` and `postComp_id`
  are all `rfl`.

## Characters (`section Characters`)

Here `C` is a commutative `R`-algebra and `t : Multiplicative M →* Cˣ` is a character.

- `charEval R t : R[M] →ₐ[R] C` evaluates at `t`: it sends `Xᵐ` to `t m` (`charEval_single`).
- `incl R : C →ₐ[R] C ⊗[R] R[M]` is `Algebra.TensorProduct.includeLeft`.
- `evalAt R t : C ⊗[R] R[M] →ₐ[R] C` sends `c ⊗ q` to `c · charEval t q` (`evalAt_tmul`).
- `translateChar R t` is the character `m ↦ t(m) ⊗ Xᵐ` with values in `C ⊗[R] R[M]`.
  `translate R t` is the `C`-linear translation `c ⊗ Xᵐ ↦ c t(m) ⊗ Xᵐ`
  (`translate_tmul_one`, `translate_tmul_single`).
- `tensor_algHom_ext`: algebra maps out of `C ⊗[R] R[M]` that agree on `c ⊗ 1` and on
  `1 ⊗ Xᵐ` are equal.
- Laws, each proved with `tensor_algHom_ext`: `translate_one`,
  `translate_comp_translate` (`τ_t ∘ τ_s = τ_{ts}`), `translate_comp_incl`,
  `evalAt_comp_translate` (`ev_t ∘ τ_s = ev_{ts}`) and `evalAt_comp_incl`.
- `mapChar R g t` changes the coefficients of a character along `g : C →ₐ[R] D`. The lemmas
  `map_comp_translate`, `comp_evalAt`, `map_comp_incl` and `mapChar_one` give naturality.
  `char_one_mul` is `one_mul` for characters, stated separately for use in `simp` sets.
- `evalAt_one_eq_counit`: `ev_1` is `id_C ⊗ ε` followed by `C ⊗[R] R ≅ C`.
  `comulAlgHom_single_one`: `Δ Xᵐ = Xᵐ ⊗ Xᵐ`.
- `splitEval R t : C ⊗ (R[M] ⊗ R[M]) → C ⊗ R[M]` sends `c ⊗ p ⊗ q` to `c · t(q) ⊗ p`. The
  lemmas say that it composes to `translate R t` with `id ⊗ Δ` (`splitEval_comp_comul`), to the
  identity with `inclFirst` (`splitEval_comp_inclFirst`), and to `incl ∘ evalAt R t` with
  `inclSecond` (`splitEval_comp_inclSecond`).
- `universalChar R : Multiplicative M →* (C ⊗[R] R[M])ˣ` is `m ↦ 1 ⊗ Xᵐ`
  (`universalChar_apply`).
- `swapAssoc R : (C ⊗ P) ⊗ P →ₐ[R] C ⊗ (P ⊗ P)` sends `(c ⊗ q) ⊗ p` to `c ⊗ (p ⊗ q)`
  (`swapAssoc_tmul`), for any commutative `R`-algebra `P`. With `P = R[M]` it carries the
  universal translation to `id ⊗ Δ` (`swapAssoc_comp_translate`), coefficient extension along
  `incl` to `inclFirst` (`swapAssoc_comp_map`), and universal evaluation to `inclSecond`
  (`swapAssoc_comp_evalAt`).

## The normalised translation action (`section Action`)

`Pt R A M C` is `WithConv (A →ₐ[R] C ⊗[R] R[M])`, the points of the Weil restriction with values
in `C`, with the convolution group structure. The following are monoid homs `Pt → Pt`, all
instances of `postComp`:

- `transPt R t`, postcomposition with `translate R t`;
- `constPt R t`, postcomposition with `incl ∘ evalAt R t`;
- `pushPt R g`, coefficient change along `g`.

In addition, `unitValue R : Pt R A M C →* WithConv (A →ₐ[R] C)` is postcomposition with
`evalAt R 1`.

- `actPt R t φ := transPt t φ * (constPt t φ)⁻¹ * constPt 1 φ`.
  The last factor makes the action unital: `actPt_one`. `actPt_mul` gives
  `actPt (t * s) = actPt t ∘ actPt s`, and `pushPt_actPt` gives naturality in the coefficients.
  Supporting rewrite rules are `transPt_transPt`, `transPt_constPt`, `constPt_transPt`,
  `constPt_constPt`, `unitValue_constPt`, `constPt_eq`, `pushPt_transPt`, `pushPt_constPt` and
  `unitValue_pushPt`. The group identities are proved by the `group` tactic in three private
  lemmas over an arbitrary group.
- `normalize R φ := (constPt 1 φ)⁻¹ * φ` divides a point by its value at the unit section.
  It has value `1` there (`unitValue_normalize`), commutes with the action (`actPt_normalize`),
  and commutes with coefficient change (`pushPt_normalize`).
- `comulRight_eq`: `comulRight R f` is the convolution product of `inclFirst ∘ f` and
  `inclSecond ∘ f`. `counitMap_eq`: `counitMap R f = evalAt R 1 ∘ f`.
- `constPt_one_of_isHopfPoint` and `normalize_of_isHopfPoint`: a Hopf point has value `1` at the
  unit section, so normalising does not change it.
- `actPt_of_isHopfPoint`: every Hopf point is fixed by every character. Applying `splitEval R t`
  to the comultiplication identity `comulLeft φ = comulRight φ` gives
  `transPt t φ = φ * constPt t φ`.
- `isHopfPoint_of_actPt`: let `φ` have value `1` at the unit section. Suppose that, after
  coefficient extension along `incl : C → C ⊗[R] R[M]`, `φ` is fixed by `universalChar R`. Then
  `φ` is a Hopf point. Applying `swapAssoc R` to the fixed-point identity
  `transPt u ψ = ψ * constPt u ψ` gives `comulLeft φ = comulRight φ`. The counit condition is the
  hypothesis on the unit section.

## Formal smoothness (`section Smooth`)

Here `A` is also finitely presented over `R` and `M` is finite, so `R[M]` is finite free and the
Weil restriction `Weil R A R[M]` exists.

- `weilObj R A M` is `Weil R A R[M]` as an object of `CommAlgCat (CommRingCat.of R)`.
- `weilPtEquiv C : (weilObj R A M ⟶ C) ≃ Pt R A M C` is the Library's
  `TauCeti.Algebra.WeilRestriction.tensorHomEquiv`. It is natural in `C` (`weilPtEquiv_comp`,
  from `tensorHomEquiv_comp`).
- `weilAction : CharacterAction.Action (weilObj R A M)` is the Library's notion of an action of
  characters `Multiplicative M →* Cˣ` on the points of `weilObj`. It is obtained by transporting
  `actPt`, and `weilPtEquiv_act` computes it.
- `isFixed_of_isHopfPoint`: a point whose image under `weilPtEquiv` is a Hopf point is fixed in
  the Library's sense (`CharacterAction.IsFixed`, i.e. after every refinement).
- `isHopfPoint_normalize_of_isFixed`: if `x` is fixed in the Library's sense, then
  `normalize (weilPtEquiv x)` is a Hopf point. Fixedness is used only for the refinement
  `C → C ⊗[R] R[M]` and the character `universalChar R`, as in `isHopfPoint_of_actPt`.
- `formallySmooth_homAlgebra` uses `Algebra.FormallySmooth.of_comp_surjective`. Let `I` be a
  square-zero ideal of `B` and `g : HomAlgebra →ₐ[R] B ⧸ I`. Its Weil point `x` is a Hopf point,
  hence fixed. `Weil R A R[M]` is formally smooth by the Library instance
  `TauCeti.Algebra.WeilRestriction.instFormallySmooth`, since Mathlib makes `R[M] ⊗[R] A`
  formally smooth over `R[M]`. So `CharacterAction.exists_fixed_lift` gives a fixed lift `y` of
  `x` to `B`. The normalisation of `y` is a Hopf point over `B`, and `homEquiv` turns it into an
  algebra map `HomAlgebra → B`. Since `x` is already normalised, this map lifts `g`.
- `smooth_homAlgebra` combines this with the finite presentation instance from
  `Langlands.Algebra.FiniteBialgebraHom`.
