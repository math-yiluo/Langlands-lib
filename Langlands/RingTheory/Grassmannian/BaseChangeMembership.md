# Membership in base changes of points of quotient Grassmannians

Author: Worker 1399. Internal helper module for the proof of
`Langlands.GroupScheme.GeneralLinearSolvableStabilizerStatement`; it has no literature source.
It describes base change of points of the Library's quotient Grassmannian
`Module.Grassmannian A (A ⊗[R] M) k`, whose points are submodules `N` of `A ⊗[R] M` with
finite projective quotient of rank `k`, and its base change
`Module.Grassmannian.map φ N` along an `R`-algebra map `φ : A →ₐ[R] B`. The Library defines
the base change as the kernel of `baseChangeMkQ B N : B ⊗[R] M → B ⊗[A] ((A ⊗[R] M) ⧸ N)`
(`Module.Grassmannian.PrincipalDescent.map_toSubmodule'`).

Namespace `Langlands.Grassmannian`.

- `cancelBaseChange_tmul_eq_smul_l` (scalar tower `R → A → B`): the cancellation
  isomorphism `B ⊗[A] (A ⊗[R] M) ≃ B ⊗[R] M` sends `b ⊗ n` to `b • l n`. Here `l` is the
  Library's map `A ⊗[R] M → B ⊗[R] M`, `a ⊗ m ↦ algebraMap A B a ⊗ m`. Induction on `n`.
- `ker_baseChangeMkQ_eq_span`: the kernel of `baseChangeMkQ B N` is the `B`-span of
  `l '' N`. This is right exactness of `B ⊗[A] -`: Mathlib's `lTensor_mkQ` identifies the
  kernel of `B ⊗ N.mkQ` with the range of `B ⊗ N.subtype`. That range is transported through
  the cancellation isomorphism and the previous lemma. The reverse inclusion holds since `N`
  maps to zero in the quotient (`baseChangeMkQ_l`).
- `one_tmul_eq_zero_iff_of_comp_eq_id`: let `Q` be an `A`-module with maps
  `g : Q → A^m` and `f : A^m → Q`, `f ∘ g = id`. Then `1 ⊗ q = 0` in `B ⊗[A] Q` if and only if
  every coordinate of `g q` maps to zero in `B`. Proof: `B ⊗[A] A^m ≅ B^m`
  (`TensorProduct.piScalarRight`), and `1 ⊗ q` is the image of `1 ⊗ g q` under `B ⊗ f`.
- `l_eq_rTensor`: for the algebra structure `φ.toAlgebra`, `l` is `φ.toLinearMap.rTensor M`.
- `map_toSubmodule_eq_span`: the base change of a point is the span of the image of the point,
  `(map φ N).toSubmodule = span B (φ.rTensor M '' N.toSubmodule)`. This combines
  `map_toSubmodule'` with `ker_baseChangeMkQ_eq_span`.
- `exists_ideal_forall_rTensor_mem_map_iff`: for a point `N` and any family
  `v : τ → A ⊗[R] M` (`τ : Type u` arbitrary), there is an ideal `𝔞` of `A` such that, for
  every `R`-algebra `B` and every `φ : A →ₐ[R] B`,
  `(∀ t, φ.rTensor M (v t) ∈ (map φ N).toSubmodule) ↔ ∀ a ∈ 𝔞, φ a = 0`.
  Proof: the quotient `(A ⊗[R] M) ⧸ N` is finite projective, so Mathlib's
  `Module.Finite.exists_comp_eq_id_of_projective` gives a split embedding `g` into `A^m`.
  `𝔞` is spanned by all coordinates `g (mkQ (v t)) i`. Membership of `φ.rTensor M (v t)` in
  the kernel of `baseChangeMkQ` means that `1 ⊗ mkQ (v t)` vanishes (`baseChangeMkQ_l` and
  `l_eq_rTensor`). By `one_tmul_eq_zero_iff_of_comp_eq_id` this means that `φ` kills these
  coordinates.

The last theorem supplies the ideals required by the Library's closed-immersion criterion
`AlgebraicGeometry.Scheme.exists_isClosedImmersion_represents_of_forall_exists_ideal` in
`Langlands.RingTheory.Grassmannian.FlagLocus`.
