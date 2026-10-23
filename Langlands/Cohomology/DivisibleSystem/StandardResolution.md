# The standard resolution of ℓ-divisible systems

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem` (the
`ℓ`-divisible systems `DivisibleSystem C ℓ`, their images `T.map F` under
additive functors preserving finite limits and finite colimits, `mapNatTrans`
and `degree`) and on Mathlib. Names in the first two sections are in the
namespace `Langlands.Cohomology`, and the `DivisibleSystem` names in
`Langlands.Cohomology.DivisibleSystem`.

On pp.305–306 Harris writes `M_m^{q,H} = G_m^q(U(ẽ)_F̄)^H` and says: "We
obtain the standard resolution by iterating the functorial surjection

(2.4) `ℤ_ℓ[S(ẽ)/H] ⊗_{ℤ_ℓ} (•) → •`."

He then lets (2.5) `⋯ K_m^{-r,q,H} → K_m^{-r+1,q,H} → ⋯ K_m^{-1,q,H} →
M_m^{q,H} → 0` "be the canonical free resolution of `M_m^{q,H}` obtained via
(2.4)". He takes `C_m^{•,H}` to be the simple complex of the double complex
`K_m^{-•,•,H}` and states that "another snake lemma argument" makes it "an
ℓ-divisible system of complexes of free `ℤ/ℓ^mℤ[S(e)/H]`-modules as `m`
varies". Here `S(ẽ)/H` is a finite group.

This module builds the standard resolution for any endofunctor `P` of an
abelian category with a natural transformation `ε : P ⟶ 𝟭`. It shows that
`ℓ`-divisible systems pass to systems of resolutions when `P` is additive and
exact, and specializes `P` to induction from the trivial subgroup of a finite
group. The simple complex `C_m^{•,H}`, the exactness of the augmented
resolution and any freeness are not part of this module.

## The standard resolution of an endofunctor

`A` is an abelian category, `P : A ⥤ A` and `ε : P ⟶ 𝟭 A`.

- `standardPow P n : A ⥤ A` is the iterate `P^n`: `P^0 = 𝟭 A` and
  `P^(n+1) = P^n ⋙ P`, so `P^(n+1) X = P (P^n X)`.
- `standardCounit P ε n : P^(n+2) ⟶ P^(n+1)` has components
  `ε (P^(n+1) X)`. For `φ : P^(n+1) ⟶ P^n`,
  `standardPowMap P φ : P^(n+2) ⟶ P^(n+1)` has components `P (φ X)`. Both
  have `@[simps]` component lemmas.
- `standardDifferential P ε n : P^(n+1) ⟶ P^n` is defined by recursion on
  `n`. For `n = 0` it is `ε` (`standardDifferential_zero_app`). For `n + 1`
  it is `standardCounit P ε n - standardPowMap P (standardDifferential P ε n)`
  (`standardDifferential_succ`, by `rfl`). Writing `d_n` for it,
  `d_0 = ε` and `d_{n+1} X = ε (P^(n+1) X) - P (d_n X)`. The Lean
  definition is this recursion. When `P` is additive, `P` distributes over
  the difference, and unwinding the recursion gives the alternating sum
  `d_n = Σ_i (-1)^i P^i ε P^(n-i)` of the ways of applying `ε` to one of the
  `n + 1` factors: the bar differential. This needs additivity. For a
  functor that only preserves zero morphisms, the recursion still defines a
  complex (see below), but `d_n` need not equal the alternating sum. For
  example, on `ℚ`-vector spaces take `P V = V ⊕ (V ⊗ V)`,
  `P f = f ⊕ (f ⊗ f)` and `ε` the first projection: there `d_2` and the
  alternating sum differ by a sign on a nonzero element (Reviewer 1362's
  counterexample in review 3c9b446c of an earlier version of this module).
  The systems below and the group case `indResBot` use additive `P`, where
  the two descriptions agree.
- `standardPowMap_comp_standardCounit` is naturality of `ε`:
  `standardPowMap P φ ≫ standardCounit P ε n = standardCounit P ε (n + 1) ≫ φ`
  for `φ : P^(n+2) ⟶ P^(n+1)`.

From here on `P` preserves zero morphisms.

- `standardPowMap_comp_standardDifferential_succ`: if
  `φ ≫ d_n = 0` for `φ : P^(n+2) ⟶ P^(n+1)`, then
  `standardPowMap P φ ≫ d_{n+1} = standardCounit P ε (n + 1) ≫ φ`. The proof
  expands `d_{n+1}`; the term `P φ ≫ P d_n = P (φ ≫ d_n) = P 0` vanishes
  because `P` preserves zero morphisms, and the other term is naturality of
  `ε`.
- `standardDifferential_comp n : d_{n+1} ≫ d_n = 0`, by induction on `n`. In
  both cases `d_{n+1} ≫ d_n` is `standardCounit ≫ d_n - standardPowMap d_n ≫ d_n`
  and the two terms agree: for `n = 0` by naturality of `ε` at `ε`, and for
  `n + 1` by the previous lemma applied to `φ = d_{n+1}` with the induction
  hypothesis.
- `standardComplex P ε : ChainComplex (A ⥤ A) ℕ` is Mathlib's
  `ChainComplex.of` with `P^(r+1)` in degree `r` and the differential
  `d_{r+1} : P^(r+2) ⟶ P^(r+1)` from degree `r + 1` to degree `r`
  (`standardComplex_X` by `rfl`; `standardComplex_d` from Mathlib's
  `ChainComplex.of_d`).
- `standardResolution P ε : A ⥤ ChainComplex A ℕ` is Mathlib's
  `HomologicalComplex.asFunctor` of `standardComplex P ε`: the complex
  `⋯ ⟶ P^3 X ⟶ P^2 X ⟶ P X` with `P^(r+1) X` in degree `r`
  (`standardResolution_obj_X`, `standardResolution_map_f` by `rfl`;
  `standardResolution_obj_d`).
- `standardResolution_obj_d_comp X`: the differential from degree `1` to
  degree `0`, followed by `ε X : P X ⟶ X`, is zero (the case `n = 0` of
  `standardDifferential_comp`).
- `standardResolutionAugmentation P ε : standardResolution P ε ⟶
  ChainComplex.single₀ A` is the augmentation. At `X` it is the chain map to
  `X` placed in degree `0` given by `ε X` in degree `0`, built with Mathlib's
  `ChainComplex.toSingle₀Equiv` from `standardResolution_obj_d_comp`. Its
  naturality is naturality of `ε`.

Exactness instances:

- `standardPow_additive`, `standardPow_preservesFiniteLimits`,
  `standardPow_preservesFiniteColimits`: if `P` is additive, resp. preserves
  finite limits, resp. finite colimits, so does every `P^n`. This is
  induction on `n` with Mathlib's instances for `𝟭` and for composites.
- `standardResolution_additive`, `standardResolution_preservesFiniteLimits`,
  `standardResolution_preservesFiniteColimits`: the same for
  `standardResolution P ε`. Limits and colimits of complexes are computed
  degreewise (Mathlib's `HomologicalComplex.preservesLimitsOfShape_of_eval`
  and its colimit version). The degree `r` part of `standardResolution P ε` is
  `P^(r+1)`.

## Standard resolutions of ℓ-divisible systems

Now `P` is additive and preserves finite limits and finite colimits, and
`ℓ : ℕ`.

- `standardResolutionSystem P ε T : DivisibleSystem (ChainComplex A ℕ) ℓ` is
  `T.map (standardResolution P ε)` for `T : DivisibleSystem A ℓ`: the
  standard resolutions of the members of `T`, with the inclusions and
  projections of `T` applied termwise. The parent module's `map` needs
  exactly the three instances above.
- `standardResolutionSystem_degree T r`: its degree-`r` system is
  `T.map (standardPow P (r + 1))`. The equality holds by `rfl`.
- `standardResolutionSystemAugmentation P ε T` is the augmentation as a
  morphism of `ℓ`-divisible systems to `T.map (ChainComplex.single₀ A)`, the
  system `T` placed in degree `0` (the parent module's `mapNatTrans`).
- `standardResolutionDoubleComplexes P ε K`, for
  `K : DivisibleSystem (CochainComplex A ℕ) ℓ`, applies `standardResolution`
  in each degree: it is `K.map` of Mathlib's
  `(standardResolution P ε).mapHomologicalComplex (ComplexShape.up ℕ)`, an
  `ℓ`-divisible system in Mathlib's
  `HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ)`
  (cochain complexes of chain complexes). Mathlib's instances make
  `mapHomologicalComplex` of an exact functor exact.
  `standardResolutionDoubleComplexes_obj_X_X` says that its `(q, r)` term at
  level `m` is `P^(r+1)` applied to the degree-`q` term of `K m`, by `rfl`.
  This is Harris's `K_m^{-(r+1),q,H}` when `K m = M_m^{•,H}`: resolution
  degree `r` here is Harris's degree `-(r+1)`.
- `standardResolutionDoubleComplexesAugmentation P ε K` is the augmentation
  in every degree `q`, a morphism of `ℓ`-divisible systems to `K` placed in
  resolution degree `0`. It is `mapNatTrans` of Mathlib's
  `NatTrans.mapHomologicalComplex`.

## The group case

`k` is a commutative ring and `Γ` a group. Representations are Mathlib's
`Rep.{max w u v} k Γ`, with `k : Type u` and `Γ : Type v`.

- `indResBot k Γ` is Mathlib's restriction `Rep.resFunctor` along the
  inclusion of the trivial subgroup `⊥` followed by Mathlib's induction
  `Rep.indFunctor` along it. `indResBotCounit k Γ` is the counit of Mathlib's
  adjunction `Rep.indResAdjunction` (induction left adjoint to restriction),
  `Ind_1^Γ Res_1^Γ M ⟶ M`.
- With `[Finite Γ]`, instances `indFunctor_bot_additive`,
  `indFunctor_bot_preservesFiniteLimits` and
  `indFunctor_bot_preservesFiniteColimits` say that induction from `⊥` is
  additive and exact. Induction is a left adjoint (Mathlib's
  `Rep.indResAdjunction`), so it preserves colimits. It is also a right
  adjoint because `⊥` has finite index (Mathlib's `Rep.resIndAdjunction`, via
  its instance in `Mathlib.RepresentationTheory.FiniteIndex`), so it
  preserves limits. Additivity comes from preserving binary products
  (`Functor.additive_of_preserves_binary_products`). Restriction is additive
  and exact by Mathlib instances, so `indResBot k Γ` is too.
- `groupStandardResolutionSystem T` and
  `groupStandardResolutionDoubleComplexes K` are `standardResolutionSystem`
  and `standardResolutionDoubleComplexes` for `P = indResBot k Γ` and
  `ε = indResBotCounit k Γ`, for a finite group `Γ`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.305–306. Worker 61
read (2.4), (2.5) and the following paragraph in the scanned original.

1. The functor of (2.4). Mathlib's induction along `φ : G →* Γ` is
   `(k[Γ] ⊗_k A)_G`, with `h ∈ Γ` sending `⟦h₁ ⊗ a⟧` to `⟦h₁h⁻¹ ⊗ a⟧`. For
   `G = ⊥` the coinvariant relations are zero, so `indResBot k Γ` sends `M`
   to `k[Γ] ⊗_k M` with `Γ` acting on `k[Γ]` only. Up to inversion on `Γ`
   this is Harris's `ℤ_ℓ[S(ẽ)/H] ⊗_{ℤ_ℓ} M` with `k = ℤ_ℓ`,
   `Γ = S(ẽ)/H`. The counit sends `⟦h ⊗ a⟧` to `h⁻¹ · a` (Mathlib's
   `Rep.indResHomEquiv`), which under the same inversion is the multiplication
   map `g ⊗ a ↦ g · a` of (2.4). These identifications explain the choice.
   They are not formalized. `Γ` finite matches Harris's finite group
   `S(ẽ)/H`. Linking this module with the H-invariants module would need
   `Γ = G ⧸ H` with `H` of finite index; that link is not made here.
2. Integral and finite-level coefficients. In (2.4) the coefficients are
   integral: the group ring is `ℤ_ℓ[S(ẽ)/H]`, the tensor product is over
   `ℤ_ℓ`, and the same functor serves every level `m`. The module follows
   this. There is one commutative ring `k` (for Harris `k = ℤ_ℓ`), and all
   members of a system lie in the one category `Rep k Γ`, as
   `DivisibleSystem` requires. Nothing in the module uses a property of `k`
   or of `ℓ`. Finite-level coefficients are a separate step, which is not
   formalized. The member `M` of index `m` is killed by `ℓ^m` (the parent
   module's `powSMul_eq_zero`). Hence `k[Γ] ⊗_k M` is killed by `ℓ^m` and is
   `(k/ℓ^m)[Γ] ⊗_{k/ℓ^m} M`. For `k = ℤ_ℓ` this is a
   `ℤ/ℓ^mℤ[S(ẽ)/H]`-module. Harris's statement about free
   `ℤ/ℓ^mℤ[S(e)/H]`-modules on p.306 is at this finite level (item 5).
3. Bar form. "Iterating the functorial surjection" is read as the bar
   construction: terms `P^(r+1) M`, differentials defined by the recursion
   above. For additive `P`, which includes Harris's `ℤ_ℓ[S(ẽ)/H] ⊗ (•)` and
   `indResBot`, these are the alternating sums of the maps applying `ε` once.
   For non-additive `P` the recursion is the definition and is not claimed to
   be a bar complex. Iterating on kernels (Mathlib's `LeftResolution`) is
   another reading. The bar form was chosen because each term `P^(r+1)` is
   an exact functor, so the parent module's `map` applies to the resolution
   functor directly.
4. Resolution and augmentation. The augmentation `ε` is part of the data,
   and `standardResolution_obj_d_comp` shows that it is a chain map. The
   exactness of `⋯ → P^2 M → P M → M → 0`, which would make
   `standardResolution P ε` a resolution, is not proved. For `indResBot` it
   holds by the usual contracting homotopy after restriction to the trivial
   group; that argument is not formalized.
5. Freeness. Harris calls (2.5) a free resolution. `P^(r+1) M` is
   `k[Γ]^{⊗(r+1)} ⊗_k M` with `Γ` acting on the first factor only, which is
   free over `k[Γ]` when `M` is free over `k`. For Harris's `M_m^{q,H}`, killed
   by `ℓ^m`, the relevant freeness is at the finite level of item 2: over
   `ℤ/ℓ^m`, and then of `P^(r+1) M` over `ℤ/ℓ^mℤ[S(ẽ)/H]`. The parent
   module's `flat` condition says that `ker ℓ^b = ℓ^a M` on the member `M` of
   index `a + b`. For prime `ℓ` this makes the members flat, hence free, over
   `ℤ/ℓ^m`. None of this is formalized, and no term is asserted to be free.
6. Indexing. The resolution is a chain complex in degrees `r ≥ 0` with
   `P^(r+1)` in degree `r`. Harris's cohomological degree is `-(r+1)`, with
   `M_m^{q,H}` itself in degree `0` of the augmented complex. `M_m^{q,H}` is
   the target of the augmentation, not a term of `standardResolution`. The
   double complexes are cochain complexes in `q` of chain complexes in `r`,
   and their `(q, r)` term is Harris's `K_m^{-(r+1),q,H}`. In Harris's
   degrees it therefore has total degree `q - r - 1`, not `q - r`. This
   module forms no total complex.

`standardResolution`, `standardResolutionSystem` and
`standardResolutionDoubleComplexes` (and their group versions) formalize the
standard resolution (2.4)–(2.5) and its compatibility with `ℓ`-divisibility in
each degree `q`. The vanishing of `d²`, the augmentation, the exactness
instances and the identification of the terms are derived.

## Scope

The module does not prove that the augmented standard resolution is exact,
that any term is free or projective, or that it is isomorphic to
`k[Γ] ⊗_k M`. It does not form the simple complex `C_m^{•,H}` of p.306, the
isomorphism `C_m^{•,H} = [C_m^{•,H'}]^H`, the direct limit over `H`, the
quasi-isomorphism (2.6) or Lemma 2.8. It does not connect to the
H-invariants module.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
