# Tensor homology presheaves and extension of scalars

Let `R, S : CommRingCat.{u}` with an algebra structure `[Algebra R S]`, and
write `j = Spec.map (CommRingCat.ofHom (algebraMap R S)) : Spec S → Spec R`.
Let `K` be an integer cochain complex of `R`-modules. Write
`K_S = (ModuleComplex.baseChange (algebraMap R S)).obj K` for the
Library's degreewise extension of scalars `S ⊗[R] K`, built with Mathlib's
`ModuleCat.extendScalars`.

The main result is
`TensorSections.homologyPresheafBaseChangeIso K n`, a natural isomorphism

`(Over.map j).op ⋙ homologyPresheaf K n ≅ homologyPresheaf K_S n`

of presheaves on the entire slice over `Spec S`. At a test `T` over `Spec S`,
the left side is `Hⁿ(Γ(T,𝒪_T) ⊗[R] K)`. Here `Γ(T,𝒪_T)` is an `R`-algebra
through the composite structure map `T → Spec S → Spec R`. The right side
is `Hⁿ(Γ(T,𝒪_T) ⊗[S] (S ⊗[R] K))`. Both values carry the Library's
explicit lift to `Type (u+1)`. Nonaffine tests and all morphisms of the
slice are included.

The construction proceeds as follows.

1. `sectionScalars_map` identifies the coefficient map of the image test
   `(Over.map j).obj T` with the composite of `algebraMap R S` and the
   coefficient map of `T`. The proof uses Mathlib's naturality of
   `Scheme.ΓSpecIso`. Hence `isScalarTower_sections` holds: with the
   `R`-algebra structure `restrictedAlgebra R T` of the image test, the
   sections form a scalar tower `R → S → Γ(T,𝒪_T)`.
2. `cancelEquiv T M` is an `R`-linear equivalence from the restriction of
   scalars of `Γ(T,𝒪_T) ⊗[S] (S ⊗[R] M)` to `Γ(T,𝒪_T) ⊗[R] M`, for every
   `R`-module `M`. It composes the Library's
   `Scheme.Modules.extendScalarsAlgebraEquiv` with Mathlib's
   `TensorProduct.AlgebraTensorModule.cancelBaseChange`. The Library
   equivalence compares Mathlib's categorical scalar extension with the
   algebra tensor product; the two `R`-module structures on `S` agree only
   propositionally. The result is `S`-linear, and `R`-linearity follows from
   the scalar tower. On pure tensors it sends `γ ⊗ (c ⊗ m)` to `(c γ) ⊗ m`
   (`cancelEquiv_tmul`).
3. `cancelEquiv_naturality` proves naturality in `M`, and
   `cancelEquiv_naturality_sections` proves naturality along every map of
   tests. The latter uses `pullSections_smul`: pullback of global sections
   is `S`-linear. Both proofs reduce to pure tensors by tensor-product
   induction.
4. `tensorComplexBaseChangeIso T K` assembles the degreewise equivalences
   into an isomorphism of complexes of `R`-modules, and
   `complexesBaseChangeIso K` makes it natural in `T`. The commutation with
   differentials is step 3 applied to the differentials of `K`.
5. `restrictScalarsHomologyIso n` uses Mathlib's
   `ShortComplex.mapHomologyIso` to show that restriction of scalars, which
   is exact, commutes with degree `n` homology of cochain complexes.
   `restrictScalarsForgetIso` records that restriction of scalars does not
   change underlying sets. Whiskering these isomorphisms gives
   `homologyPresheafBaseChangeIso`.

The file sets `backward.isDefEq.respectTransparency false`, as Mathlib's
change-of-rings files and the Library's `ExtendScalarsTensor` do, so that
the definitional unfoldings of Mathlib's scalar extension are accepted.

This is an internal construction. It assumes no flatness, finiteness,
boundedness or noetherian hypothesis. It is used with `S` a principal
localization of `R`, to compare the restriction of a tensor homology
presheaf to a principal open chart with the tensor homology presheaf of the
localized complex.
