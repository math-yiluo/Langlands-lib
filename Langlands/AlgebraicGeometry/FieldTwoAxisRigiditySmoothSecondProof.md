# Two-axis rigidity over fields with a smooth, possibly non-proper second factor

Worker 1140 wrote this proof. The final comparison between the cartesian monoidal product and
`Limits.prod` is adapted, essentially verbatim, from the published proof
`Langlands.AlgebraicGeometry.fieldTwoAxisRigidity` in
`Langlands/AlgebraicGeometry/FieldTwoAxisRigidityProof.lean`, implemented by Worker 423. The
clopen-set route follows the suggested route in the task context, written by Worker 998. No
unpublished draft is reused.

The theorem `Langlands.AlgebraicGeometry.fieldTwoAxisRigiditySmoothSecond.{u}` has type exactly
`Langlands.AlgebraicGeometry.FieldTwoAxisRigiditySmoothSecondStatement.{u}`, for every universe
`u`. It imports the published statement module unchanged. The statement says that over any field
`K`, with `S = Spec K`, the following holds. Let `Y` be smooth, proper and geometrically connected
over `S`, and let `Z` be smooth and geometrically connected (not necessarily proper). Let `P` be
separated and locally of finite type over `S`. Suppose `g : Y ⨯ Z ⟶ P` in `Over S` is constant
with value `p₀` on both axes `(y₀, z)` and `(y, z₀)`. Then `g` is the constant morphism with
value `p₀`, as an equality of full morphisms in `Over S`.

## Dependencies

The proof uses two published Library theorems, both imported by Lean name:

- `Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`
  (module `Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof`). For a smooth,
  proper, geometrically connected morphism `p : X ⟶ S'` of schemes, `p.app V` is an isomorphism
  for every open `V` of `S'`.
- `Langlands.AlgebraicGeometry.factorizationOfGlobalFunctions`
  (module `Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctionsProof`). Suppose `e` is a
  section of `p`, every `p.app V` is an isomorphism, and `g x = (e ≫ g) (p x)` for every point
  `x`. Then `g = p ≫ e ≫ g`.

Everything else comes from Mathlib's scheme and category-theory APIs.

## Implemented proof

**`restrict_eq_of_affine` (private).** Let `p : X ⟶ S'` have a section `e` (`e ≫ p = 𝟙`). Let
`V` be an open of `S'` such that `p.app V` is an isomorphism. Let `g : X ⟶ T` map `p ⁻¹ᵁ V` into
an affine open `U` of `T`. Then `(p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ e ≫ g`.

The proof restricts the three maps with `Scheme.Hom.resLE`:

- `pr : p ⁻¹ᵁ V ⟶ V`;
- `er : V ⟶ p ⁻¹ᵁ V`, which is defined because `e ≫ p = 𝟙` gives `V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)`;
- `gr : p ⁻¹ᵁ V ⟶ U`.

`Scheme.Hom.resLE_comp_resLE` gives `er ≫ pr = 𝟙`. By `resLE_app_top` and `appLE_eq_app`, the
global-section map `pr.appTop` is `p.app V`, so it is an isomorphism. It is therefore a two-sided
inverse of `er.appTop`. `U` is affine, so `ext_of_isAffine` says that morphisms into `U` are
determined by their maps on global sections. Hence `gr = pr ≫ er ≫ gr`. Composing with `U.ι`
gives the claim.

**`rigidity_pullback` (private, scheme level).** Let `a : Y ⟶ Spec K` be smooth, proper and
geometrically connected, and let `b : Z ⟶ Spec K` be geometrically connected. Let `y₀` and `z₀`
be sections of `a` and `b`, let `q : P ⟶ Spec K` be any morphism with a section `p₀`, and let
`g : pullback a b ⟶ P`. Suppose `g` restricted to each axis is constant:
`lift (b ≫ y₀) (𝟙 Z) ≫ g = b ≫ p₀` (hypothesis `hy`) and `lift (𝟙 Y) (a ≫ z₀) ≫ g = a ≫ p₀`
(hypothesis `hz`). Then `g = pullback.snd a b ≫ b ≫ p₀`.

Write `p = pullback.snd a b` and `e = pullback.lift (b ≫ y₀) (𝟙 Z)`, so `e ≫ p = 𝟙`. The proof
then runs as follows.

1. `p` is a base change of `a`, so Mathlib's instances make it smooth, proper and geometrically
   connected. `smoothProperConnectedGlobalFunctions` then gives `IsIso (p.app V)` for every open
   `V`. Mathlib also makes `p` a closed map (`Scheme.Hom.isClosedMap`, from universal
   closedness) and an open map (`Scheme.Hom.isOpenMap`, from flatness and local finite
   presentation).
2. Fix a point `s` of `Spec K`. Since `Spec K` has only one point, `p₀` takes the single value
   `c = p₀ s`. By `hy`, `e ≫ g` is constant with value `c`. The set `{c}` is closed: by
   `isClosedImmersion_of_comp_eq_id`, `p₀` is a closed immersion, and its range is `{c}`.
3. Let `T = {z | ∀ x, p x = z → g x = c}`.
   - *`T` is closed.* Its complement is `p '' (g ⁻¹' {c}ᶜ)`, which is open because `p` is an
     open map.
   - *`T` is open.* For `z ∈ T`, choose an affine open `U ∋ c` with
     `exists_isAffineOpen_mem_and_subset`. Then `F = p '' (g ⁻¹' Uᶜ)` is closed because `p` is a
     closed map. Its complement `V` contains `z`, because every point over `z` maps to
     `c ∈ U`, and `p ⁻¹ᵁ V ≤ g ⁻¹ᵁ U`. By `restrict_eq_of_affine`, `g` agrees with
     `p ≫ e ≫ g` on `p ⁻¹ᵁ V`. So `g x = (e ≫ g) (p x) = c` whenever `p x ∈ V`, that is,
     `V ⊆ T`.
   - *`z₀ s ∈ T`.* The square with top `lift (𝟙 Y) (a ≫ z₀)`, left `a`, right `p` and bottom
     `z₀` is a pullback. This follows by pasting with the defining pullback square of
     `pullback a b`, using `IsPullback.of_right` and `IsPullback.of_id_fst`. By
     `Scheme.exists_preimage_of_isPullback`, every `x` with `p x = z₀ s` lies on the axis
     `lift (𝟙 Y) (a ≫ z₀)`, and `hz` gives `g x = c`.
4. `Z` is connected by `GeometricallyConnected.connectedSpace_of_subsingleton`, because
   `Spec K` has one point. Hence the clopen nonempty set `T` is all of `Z`.
5. Therefore `g x = c = (e ≫ g) (p x)` for every point `x`. `factorizationOfGlobalFunctions`
   then gives `g = p ≫ e ≫ g`, and `hy` rewrites `e ≫ g` as `b ≫ p₀`.

**`rigidityTensor` (private).** This is the same statement in `Over (Spec K)` for the cartesian
monoidal product `Y ⊗ Z`. The instance, declared in `Mathlib.AlgebraicGeometry.Pullbacks`, is
Mathlib's `Over.cartesianMonoidalCategory`. There `(Y ⊗ Z).left` is `pullback Y.hom Z.hom`, and the
lemmas `Over.lift_left` and `Over.toUnit_left` compute the underlying maps of `lift` and
`toUnit`. The proof applies `CommaMorphism.left` to both hypotheses and reduces the conclusion to
underlying scheme morphisms with `ext`. It rewrites `(Y ⊗ Z).hom = pullback.fst ≫ Y.hom` as
`pullback.snd ≫ Z.hom` by `pullback.condition`, and then applies `rigidity_pullback` with
`q = P.hom`. The commutativity conditions `y₀.w`, `z₀.w` and `p₀.w` give the section hypotheses,
because the tensor unit has structure map `𝟙`.

**`fieldTwoAxisRigiditySmoothSecond`.** This step is identical to the final step of the published
`fieldTwoAxisRigidity`. The comparison `e : Y ⊗ Z ≅ Y ⨯ Z` has forward map
`prod.lift (fst Y Z) (snd Y Z)`, and its inverse is the monoidal `lift` of the two `Limits.prod`
projections. Both inverse identities follow by projection extensionality. Uniqueness of maps to
the terminal object identifies `toUnit X` with `Over.mkIdTerminal.from X`. Both axis hypotheses
transport along `e.hom`. `rigidityTensor` applied to `e.hom ≫ g` and precomposition with
`e.inv` give the exact target conclusion. The two wrapper declarations use
`set_option backward.defeqAttrib.useBackward true`, as the published proof does.

## Hypotheses used

The proof uses that `Y` is smooth, proper and geometrically connected, and that `Z` is
geometrically connected. It does not use the interface hypotheses `Smooth Z.hom`,
`IsSeparated P.hom` and `LocallyOfFiniteType P.hom`. The final theorem introduces them and leaves
them unused. Separatedness of the target is not needed because the common value `c` is a
rational point, so `{c}` is closed. No properness, quasi-compactness or separatedness of `Z`,
algebraic closure, base change of the field, descent or integrality enters the proof. The axioms
of the final theorem are `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This is a derived proof of the unchanged published statement. The statement's original-source
scope is documented in `Langlands/AlgebraicGeometry/FieldTwoAxisRigiditySmoothSecondStatement.md`.
The clopen-set argument is the rigidity lemma with one complete factor. It is Lan's corrected
Proposition 1.3.1.4 with base `B = Z` (thesis revision, printed pp. 69–70, with the errata p. 8),
and Mumford–Fogarty–Kirwan GIT Proposition 6.1 when `Z` is separated. The Lean proof replaces the
sources' sheaf-theoretic factorization through `p_* 𝒪 = 𝒪` with the published theorems
`smoothProperConnectedGlobalFunctions` and `factorizationOfGlobalFunctions`.
