# Proof: purely inseparable extensions do not change groups of multiplicative type

This module proves

```lean
theorem Langlands.GroupScheme.multiplicativeTypePurelyInseparable :
    MultiplicativeTypePurelyInseparableStatement.{u}
```

where `MultiplicativeTypePurelyInseparableStatement` is the Library statement in
[`Torus.MultiplicativeTypePurelyInseparableStatement`](MultiplicativeTypePurelyInseparableStatement.md).
That statement formalizes Milne, *Algebraic Groups* (2017), Corollary 12.20 (p.238) and
Corollary 12.25 (p.240); its Markdown records the correspondence with the source. The proof adds
no hypotheses and is universe polymorphic in `u`. It applies to every field `k` and every purely
inseparable extension `k'`, finite or infinite, in every characteristic. The theorem depends only
on the axioms `propext`, `Classical.choice` and `Quot.sound`.

All auxiliary declarations live in the namespace
`Langlands.GroupScheme.MultiplicativeTypePurelyInseparable`. The main theorem is in
`Langlands.GroupScheme`.

## Imports

- [`Torus.MultiplicativeTypePurelyInseparableStatement`](MultiplicativeTypePurelyInseparableStatement.md):
  the target statement.
- [`Descent.FpqcHomDescent`](../Descent/FpqcHomDescent.md): fpqc descent of group-scheme
  homomorphisms that are compatible with the canonical descent data
  (`Descent.FpqcHomDescent.hom`, `baseChange_hom`, `unique`). Through its imports it also
  provides `Descent.Compatible`, `Descent.canonicalDatum`, `Descent.canonicalOverlap`,
  `Descent.pullbackComparison` and `Descent.canonicalDatum_compatible`.
- [`Torus.DiagonalizableCharacterProof`](DiagonalizableCharacterProof.md): natural families of
  units on the points of `D_R(Λ)` (`DiagonalizableCharacter.NaturalUnits`, with `value`,
  `app_eq`, `toSections_lift`, `toSections_injective`, `isGrouplike_value`, `evaluate_eq_lift`).
  Through its imports it also provides the character-action algebra
  (`CharacterAction.algebra`, `universal`, `evaluate`, `constant`) and
  `CharacterAction.isGrouplike_lift_unique` from [`Torus.Grouplike`](Grouplike.md).
- [`Torus.DiagonalizableBaseChange`](DiagonalizableBaseChange.md): `Diagonalizable.baseChangeIso`,
  the isomorphism `D_k(Λ)_{k'} ≅ D_{k'}(Λ)`.
- [`GroupScheme.BaseChangeReflection`](../BaseChangeReflection.md): `fieldExtension_fpqc`, which
  says that `Spec K → Spec k` is surjective, flat and quasi-compact for a field extension `K/k`.
- Mathlib's `Mathlib.RingTheory.TensorProduct.Nontrivial`, for
  `Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain`.

The file sets `backward.isDefEq.respectTransparency false`,
`backward.isDefEq.respectTransparency.types false` and `backward.defeqAttrib.useBackward true`
inside the auxiliary namespace. These options only affect elaboration; they add no assumptions.

## Route and relation to the source

Milne proves Corollary 12.25 by taking Galois invariants over a finite Galois extension that
splits both groups, and deduces Corollary 12.20 from Exercise 11-1. That route would need the
Galois full faithfulness `MultiplicativeTypeGaloisFullFaithfulnessStatement` (proved in the
Library as `multiplicativeTypeGaloisFullFaithfulness`, which this module does not import). The
Lean proof takes a different route:

1. **Part 2 by fpqc descent.** `p = Spec k' → Spec k` is fpqc. So a homomorphism
   `f : G_{k'} ⟶ H_{k'}` descends uniquely once it is compatible with the canonical descent data
   (`Descent.FpqcHomDescent`). Injectivity of base change needs no further input.
2. **Compatibility from lift independence.** `f` is compatible as soon as its "transfer" to
   points over `k` does not depend on how the test scheme is lifted to `Spec k'`.
3. **Lift independence by rigidity.** After a faithfully flat base change to a field `Ω` that
   contains `k'` and splits `G` and `H`, the two relevant lifts become two maps
   `Spec(k' ⊗_k Ω) → Spec k'`. They agree after `Spec Ω → Spec(k' ⊗_k Ω)`, and since `k'/k`
   is purely inseparable this map has nil kernel on rings. Natural transformations between
   points of diagonalizable groups are given by grouplike elements of group algebras. Grouplike
   elements have idempotent coefficients, so they cannot be deformed along a nil kernel. Hence
   the two transfers agree.
4. **Part 1 from part 2.** Apply part 2 to `H` and `D_k(Λ)`. Both are of multiplicative type,
   and `D_k(Λ)_{k'} ≅ D_{k'}(Λ)`.

This rigidity argument also covers torsion characters, such as `μ_p` in characteristic `p`. The
proof route is internal; only the statement is taken from Milne.

## Section `Transfer` (any morphism `p : S ⟶ B`)

Let `f : (baseChange p).obj G ⟶ (baseChange p).obj H`.

- `precomp G a` is precomposition with a morphism `a` of test schemes, as a monoid
  homomorphism on point groups. `liftIso p Y hj : (Over.map p).obj (Over.mk j) ≅ Y` regards a
  test scheme `Y` over `B`, together with a lift `j : Y.left ⟶ S` of `Y.hom`, as a scheme over
  `S`.
- `transfer p f Y j hj : (Y ⟶ G.X) →* (Y ⟶ H.X)` applies `f` to a `B`-point of `G` using the
  lift `j`. It is the composite of `precomp` with `liftIso`, the inverse of
  `baseChangePointsEquiv p G (Over.mk j)`, the point map `pointsMap f`,
  `baseChangePointsEquiv p H (Over.mk j)`, and `precomp` back along `liftIso`.
  `transfer_left` computes its underlying morphism:
  `pullback.lift x.left j _ ≫ f.hom.hom.left ≫ pullback.fst H.X.hom p`.
- `transfer_congr` and `transfer_congr_apply` replace a lift by an equal one.
  `transfer_naturality` and `transfer_naturality'` give naturality in the test scheme: for
  `a : Y' ⟶ Y`, the transfer along `a.left ≫ j` of `a ≫ x` is `a ≫` the transfer of `x`.
- `LiftIndependent p f` says that `transfer p f Y j₁ h₁ x = transfer p f Y j₂ h₂ x` for all
  `Y`, all lifts `j₁`, `j₂` and all `x`.
- `comp_eq_of_fst_eq`: under lift independence, if two maps `a b : Z ⟶ G_S` have the same
  projection to `G`, then `a ≫ f ≫ fst = b ≫ f ≫ fst`. Proof: apply lift independence to the
  test scheme `Z` with the point `a ≫ fst`, and to the lifts `a ≫ snd` and `b ≫ snd`. Then use
  `transfer_left` and the identification of the two `pullback.lift`s with `a` and `b`.
- `baseChange_map_fst` and `hom_ext_original` are local copies of the private helper lemmas used
  for `Descent.canonicalDatum_compatible`. `hom_ext_original` says that two homomorphisms into a
  double base change `((C_S)_T)` are equal if their projections to `C` agree. It is proved with
  the comparison isomorphism `Descent.pullbackComparison p r (r ≫ p) rfl C`.
- `compatible_of_liftIndependent`: lift independence implies
  `Descent.Compatible (Descent.canonicalDatum p G) (Descent.canonicalDatum p H) f`. Apply
  `comp_eq_of_fst_eq` to the two maps from the overlap: the first pullback projection, and the
  canonical overlap isomorphism followed by the projection. Their projections to `G` agree by
  `Descent.canonicalOverlap_fst`. Then conclude with `hom_ext_original`.

## Section `Chars` (points of a split group as characters)

Let `pK : Spec RK ⟶ B` and `e : (baseChange pK).obj G ≅ D_{RK}(Λ)`.

- `precompEquiv` and `postcompEquiv` are precomposition with an isomorphism of test schemes and
  postcomposition with an isomorphism of group schemes, as multiplicative equivalences.
- `chars pK e Y σ hσ : (Y ⟶ G.X) ≃* (Multiplicative Λ →* Γ(Y.left, ⊤)ˣ)`, for a lift
  `σ : Y.left ⟶ Spec RK` of `Y.hom`. It is the composite of `liftIso`, the inverse of
  `baseChangePointsEquiv`, postcomposition with `e`, and `Diagonalizable.characterPointsEquiv`.
- `chars_naturality`: for `a : Y' ⟶ Y` and compatible lifts, the character attached to
  `a ≫ x` is the pullback of the units, `Units.map a.left.appTop`. It is proved from
  `baseChangePointsEquiv_naturality` and `Diagonalizable.characterPointsEquiv_naturality`.

## Section `Rigidity`

Fix `p : S ⟶ Bk`, a ring `R` with `rU : Spec R ⟶ Bk`, and splittings
`eG : G_{RG} ≅ D_{RG}(ΛG)` and `eH : H_{RH} ≅ D_{RH}(ΛH)` along `pG` and `pH`. Fix also lifts
`σG : Spec R ⟶ Spec RG` and `σH : Spec R ⟶ Spec RH` of `rU`.

- `under rU V := Over.mk (V.hom ≫ rU)` regards a test scheme over `Spec R` as one over `Bk`.
  `underMap` does the same for morphisms. `lift_comp_eq` supplies the lift equations.
- `natApp` and `natUnits p rU eG eH hσG hσH f q hq m : NaturalUnits R ΛG` are defined for a
  lift `q : Spec R ⟶ S` of `rU` and a character `m : ΛH`. On a test scheme `V` over `Spec R`,
  `natUnits` turns a point of `D_R(ΛG)` into a point of `G` through
  `Diagonalizable.characterPointsEquiv` and `(chars pG eG ..).symm` with the lift
  `V.hom ≫ σG`. It then applies `transfer p f` with the lift `V.hom ≫ q`, reads the result as a
  character of `H` with `chars pH eH ..` (lift `V.hom ≫ σH`), and evaluates that character at
  `m`. Naturality follows from `chars_symm_naturality`, `transfer_naturality'` and
  `chars_naturality`. `natUnits_app` is the defining equation. `natUnits_app_congr` says that
  `natUnits` for `q₁` and for `q₂` agree on every `V` with `V.hom ≫ q₁ = V.hom ≫ q₂`.
- `transfer_eq_of_nil` (**rigidity**). Let `D` be an `R`-algebra whose structure map
  `π : baseAlg R ⟶ D` has nilpotent kernel. Let `q₁` and `q₂` be lifts of `rU` that agree after
  `Spec D ⟶ Spec R`. Then for every `V` over `Spec R`, the transfers along `V.hom ≫ q₁` and
  `V.hom ≫ q₂` agree. Proof:
  1. Take the test scheme `NaturalUnits.affine (CharacterAction.algebra D)`, that is,
     `Spec D[ΛG]`. Its structure map factors through `Spec D`, so `q₁` and `q₂` agree on it.
  2. For each `m`, the two values `(natUnits .. q_i .. m).value ∈ R[ΛG]` are grouplike by
     `NaturalUnits.isGrouplike_value`.
  3. Their images under the coefficient map `R[ΛG] → D[ΛG]` agree. Rewrite the images with
     `evaluate_eq_lift` as evaluations at the universal character. By
     `NaturalUnits.toSections_lift` and `NaturalUnits.toSections_injective` they are the values
     of `natUnits` on `Spec D[ΛG]`, which agree by step 1 and `natUnits_app_congr`.
  4. `CharacterAction.isGrouplike_lift_unique π hker` gives equal values. This uses idempotent
     coefficients and the nil kernel. `NaturalUnits.app_eq` then gives equal `app` on every
     `V`. Injectivity of `chars pH eH ..` turns this into equality of the transfers.
- `transfer_eq_of_nil'` is the same conclusion for a test scheme `Y` over `Bk` with a map
  `ψ : Y.left ⟶ Spec R` over `Bk`. Transport along `Y ≅ under rU (Over.mk ψ)` with
  `transfer_naturality'`.

## Section `Field` (purely inseparable field extensions)

- `exists_field_algHom₂` and `exists_field_algHom₃`: any two (three) field extensions of `k` in
  universe `u` embed over `k` into a common field `Ω : Type u`. `K₁ ⊗[k] K₂` is nontrivial by
  `Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain`. Its quotient by a
  maximal ideal (`Ideal.exists_maximal`, `Ideal.Quotient.field`) receives both factors. Iterating
  once handles three fields.
- `spec_comp_eq` is a functoriality helper for `Spec.map` of composite ring homomorphisms.
- `mulMap γ : k' ⊗[k] Ω →ₐ[k] Ω` is the multiplication map `a ⊗ ω ↦ γ a * ω` attached to
  `γ : k' →ₐ[k] Ω`. `mulMap_tmul` is its value on pure tensors.
- `isNilpotent_sub_mulMap`: if `k'/k` is purely inseparable, then
  `x - 1 ⊗ mulMap γ x` is nilpotent for every `x ∈ k' ⊗[k] Ω`. The proof is by induction on
  tensors (`TensorProduct.inductionOn`), with `q = ringExpChar k`; `k' ⊗[k] Ω` is nontrivial
  and has exponential characteristic `q` (`expChar_of_injective_ringHom`).
  - For a pure tensor `a ⊗ ω`, pick `n` with `a^(q^n) ∈ k` (`IsPurelyInseparable.pow_mem`).
    By `sub_pow_expChar_pow`,
    `(a ⊗ 1 - 1 ⊗ γ a)^(q^n) = a^(q^n) ⊗ 1 - 1 ⊗ γ(a^(q^n)) = 0`. The difference for
    `a ⊗ ω` is this nilpotent element times `1 ⊗ ω`.
  - Sums are handled by `Commute.isNilpotent_add`.

  `isNilpotent_of_mulMap_eq_zero` deduces that `mulMap γ` has nil kernel.
- `q₁_comp` and `incl_comp` state that the following maps all lie over `Spec k` via
  `Spec(k' ⊗[k] Ω) → Spec k`: the left inclusion `q₁ = Spec(k' → k' ⊗[k] Ω)`, the map
  `Spec(includeRight ∘ γ)`, and the analogous maps through `γG` and `γH`.
- `transfer_eq_tensor`: apply `transfer_eq_of_nil'` with `R = k' ⊗[k] Ω`, `D = Ω` (through
  `mulMap γ`, with `π = Algebra.ofId`), `σG`, `σH` from `γG`, `γH`, and the two lifts `q₁` and
  `includeRight ∘ γ`. Both lifts become `Spec γ` after `Spec Ω → Spec(k' ⊗[k] Ω)`, because
  `mulMap γ (a ⊗ 1) = γ a = mulMap γ (1 ⊗ γ a)`. So on any test scheme over `k` with a map `ψ`
  to `Spec(k' ⊗[k] Ω)`, the transfers along `ψ ≫ q₁` and `ψ ≫ Spec(includeRight ∘ γ)` agree.
- `liftIndependent` (**lift independence**): for `G` and `H` of multiplicative type and any
  `f : G_{k'} ⟶ H_{k'}`, `LiftIndependent (Spec.map (algebraMap k k')) f` holds. Proof:
  1. Unpack the splittings over fields `KG` and `KH`. Choose `Ω` with `k`-embeddings `γ`, `γG`,
     `γH` of `k'`, `KG`, `KH` (`exists_field_algHom₃`).
  2. Given `Y`, lifts `j₁`, `j₂` and a point `x`, let `Z = Y.left ×_{Spec k} Spec Ω` with
     projections `g` and `s`. Here `g` is an epimorphism; the instance comes from the fpqc
     properties of `Spec Ω → Spec k` (`fieldExtension_fpqc`).
  3. For each lift `j`, the pair `(g ≫ j, s)` defines `ψ : Z ⟶ Spec(k' ⊗[k] Ω)` through
     `pullbackSpecIso k k' Ω`. By `transfer_naturality'`, `transfer_congr_apply` and
     `transfer_eq_tensor`, the composite `a ≫ transfer .. j ..` (where `a` is `g` as a map of
     test schemes) equals the transfer on `Z` along `s ≫ Spec γ`. That lift does not depend
     on `j`.
  4. Cancelling the epimorphism `g` gives the claim.

## Main theorem `multiplicativeTypePurelyInseparable`

Let `p = Spec.map (CommRingCat.ofHom (algebraMap k k'))`. By `fieldExtension_fpqc k k'`, `p` is
surjective, flat and quasi-compact.

- **Part 2.** For `G` and `H` of multiplicative type:
  - Injectivity: if `a` and `b` have equal base change, then both equal
    `Descent.FpqcHomDescent.hom` of that base change, by `Descent.FpqcHomDescent.unique` with
    `Descent.canonicalDatum_compatible p a`.
  - Surjectivity: for `f`, `liftIndependent` and `compatible_of_liftIndependent` give
    compatibility. Then `Descent.FpqcHomDescent.hom p f hc` is a preimage by
    `Descent.FpqcHomDescent.baseChange_hom`.
- **Part 1.** Let `e : H_{k'} ≅ D_{k'}(Λ)` and take `Λ' = Λ`. `H` is of multiplicative type
  (with `K = k'`). `D_k(Λ)` is of multiplicative type through
  `bD = Diagonalizable.baseChangeIso p Λ : D_k(Λ)_{k'} ≅ D_{k'}(Λ)`.
  1. Surjectivity in part 2 gives `φ : H ⟶ D_k(Λ)` and `ψ : D_k(Λ) ⟶ H`, whose base changes
     are `(e ≪≫ bD.symm).hom` and `(e ≪≫ bD.symm).inv`.
  2. The base changes of `φ ≫ ψ` and `𝟙 H` agree, and so do those of `ψ ≫ φ` and the
     identity. So injectivity in part 2 makes `Iso.mk φ ψ _ _` an isomorphism
     `H ≅ D_k(Λ)`.

  The proof thus gives `Λ' = Λ`, which is stronger than the statement requires.
