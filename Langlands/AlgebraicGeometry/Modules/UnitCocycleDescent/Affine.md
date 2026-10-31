# Local unit cocycle sections over affine opens

This helper module supports the proof of
`Langlands.Scheme.Modules.UnitCocycleDescentEffectiveStatement`. It translates the family
of units `c` over an affine open `W` of `Y` into a unit `u` of
`Γ(X, p ⁻¹ᵁ W) ⊗[Γ(Y, W)] Γ(X, p ⁻¹ᵁ W)` that satisfies the cocycle identity. It then uses
the published algebraic statement `Langlands.Algebra.UnitCocycleLocalUnitsStatement` to
produce cocycle sections that are units upstairs, near every point of `Y`. The lemmas are
internal. The algebraic input follows the proof of Stacks Project, Descent, Proposition 3.9
(Tag 023N). Everything lives in the namespace `Langlands.Scheme.UnitCocycleDescent`.

As in `UnitCocycleDescent.Submodule`, `c` assigns a unit `c U a b h` of `Γ(U, ⊤)` to every
pair `a b : U ⟶ X` with `h : a ≫ p = b ≫ p`.

## Naturality and multiplicativity

- `c_congr`: `c U a b h` only depends on `a` and `b`, not on the proof `h`.
- `IsNatural p c`: for every `q : V ⟶ U`, `c V (q ≫ a) (q ≫ b) _` is the image of
  `c U a b h` under the ring map `q.appTop`. This is the first hypothesis of the target
  statement.
- `IsMultiplicative p c`: `c U a b _ * c U b d _ = c U a d _` for every triple `a b d`
  over `Y`. This is the second hypothesis of the target statement.
- `IsCocycleSection.of_top`: for a natural family, the cocycle condition of
  `UnitCocycleDescent.Submodule` only needs to be checked on the open `⊤` of `U`, for pairs
  that map all of `U` into `p ⁻¹ᵁ W`. For an open `V`, apply the hypothesis to the pair
  `V.ι ≫ a`, `V.ι ≫ b`. Naturality along `V.ι` turns its unit into the restriction of
  `c U a b h`. The comparison of both sides on `V` with the global sections of the open
  subscheme `V` uses `ι_appLE_injective` and `appLE_comp_appLE`.

## Points with values in algebras

In this section `W` is an affine open of `Y` with affine preimage `p ⁻¹ᵁ W`. Write
`R = Γ(Y, W)` and `S = Γ(X, p ⁻¹ᵁ W)`, with an `R`-algebra structure on `S` whose algebra
map is `p.app W` (hypothesis `halg`).

- `fromSpec_comp`: `hW'.fromSpec ≫ p = Spec.map (algebraMap R S) ≫ hW.fromSpec`, by
  Mathlib's `IsAffineOpen.SpecMap_appLE_fromSpec`.
- `specPoint p hW' g` is the morphism `Spec T ⟶ X` given by `Spec.map g ≫ hW'.fromSpec`,
  for an `R`-algebra map `g : S → T`.
- `specPoint_comp`: `specPoint p hW' g ≫ p = Spec.map (algebraMap R T) ≫ hW.fromSpec`. So
  two such points have equal composites with `p`.
- `specPoint_map`: `specPoint` of `f.comp g` is `Spec.map f ≫ specPoint p hW' g`.
- `le_preimage_specPoint`: `specPoint` maps all of `Spec T` into `p ⁻¹ᵁ W`, because the
  range of `hW'.fromSpec` is `p ⁻¹ᵁ W`.
- `specPoint_appLE`: the pullback of a section `m` of `S` along `specPoint p hW' g` is the
  global function `g m` on `Spec T`, transported along `Scheme.ΓSpecIso`. This combines
  `IsAffineOpen.fromSpec_app_self` with `Scheme.ΓSpecIso_inv_naturality`.
  `comp_specPoint_appLE` gives the version after precomposition with `q : U ⟶ Spec T`.

## The unit `u`

- `cAlg p c hW hW' halg g₁ g₂` is the unit of `T` obtained by applying `c` to the pair
  `specPoint g₁`, `specPoint g₂` and transporting along `Scheme.ΓSpecIso`.
- `cAlg_map`: for a natural family and an `R`-algebra map `f : T → T'`, `f` sends
  `cAlg g₁ g₂` to `cAlg (f.comp g₁) (f.comp g₂)`. This uses `specPoint_map`, `c_congr`,
  naturality along `Spec.map f` and `Scheme.ΓSpecIso_naturality`.
- `cAlg_mul`, `cAlg_eq_mul`: for a multiplicative family,
  `cAlg g₁ g₂ * cAlg g₂ g₃ = cAlg g₁ g₃`.
- `cocycleUnit p c hW hW' halg` is `u = cAlg includeLeft includeRight`, a unit of
  `S ⊗[R] S`.
- `cocycleUnit_cocycle`: `u` satisfies the cocycle identity of
  `UnitCocycleLocalUnitsStatement`, namely
  `map id includeRight u = includeRight u * map id includeLeft u` in `S ⊗[R] (S ⊗[R] S)`.
  By `cAlg_map`, each of the three terms is `cAlg` of a pair of the three inclusions
  `S → S ⊗[R] (S ⊗[R] S)`. The identity is then `cAlg_eq_mul`. No triple fibre product of
  schemes is needed.

## From `u` to cocycle sections

- `mul_appLE_eq_of_factor`: let `m ∈ S` satisfy `u * (m ⊗ 1) = 1 ⊗ m`. Let `a b : U ⟶ X` be
  a pair over `Y` mapping `U` into `p ⁻¹ᵁ W`, and suppose that `a` and `b` factor through
  a morphism `g : U ⟶ Spec (S ⊗[R] S)` followed by the points `specPoint includeLeft` and
  `specPoint includeRight`. Then `c U a b h * a^* m = b^* m` on `U`. Naturality along `g`
  reduces this to the image of the equation `u * (m ⊗ 1) = 1 ⊗ m` under
  `Scheme.ΓSpecIso` and `g.appTop`, using `comp_specPoint_appLE`.
- `isCocycleSection_of_mul_eq`: such an `m` satisfies `IsCocycleSection p c W m`. By
  `IsCocycleSection.of_top`, consider a pair `a b` mapping `U` into `p ⁻¹ᵁ W`. Both lift
  through the open immersion `hW'.fromSpec` (`IsOpenImmersion.lift`). The lifts have equal
  composites with `Spec S ⟶ Spec R`, because `hW.fromSpec` is a monomorphism. So they
  define a morphism to the fibre product, which `pullbackSpecIso` identifies with
  `Spec (S ⊗[R] S)`. This morphism is the `g` of the previous lemma.

## Faithful flatness and local unit sections

- `faithfullyFlat_app`: if `p` is flat and surjective and `W` and `p ⁻¹ᵁ W` are affine, then
  `p.app W` is faithfully flat. Up to the isomorphisms of `app_comp_ι_appLE`, it is
  `(p ∣_ W).appTop`. The restriction `p ∣_ W` is a flat surjection of affine schemes, so
  Mathlib's `Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine` applies.
  Faithful flatness is stable under composition with isomorphisms.
- `exists_unit_cocycleSection`: assume `UnitCocycleLocalUnitsStatement.{u}` (hypothesis
  `hA`), an affine, flat, surjective `p`, and a natural, multiplicative family `c`. Then every
  point `y` of `Y` has an open neighbourhood `W` with a section `σ` over `p ⁻¹ᵁ W` that
  satisfies the cocycle condition and is a unit.

  Proof. Choose an affine open `W ∋ y`. Its preimage is affine because `p` is affine.
  Apply `hA` to `R → S`, which is faithfully flat, and to `u = cocycleUnit` with inverse
  `u⁻¹`. The resulting ideal is `⊤`, so by `IsAffineOpen.self_le_iSup_basicOpen_iff` the
  basic opens `D(r)` of its generators cover `W`. Take `r` with `y ∈ D(r)`, and `m`, `m'`
  with `u (m ⊗ 1) = 1 ⊗ m` and `p.app W r = m m'`. The restriction of `m` to
  `p ⁻¹ᵁ D(r)` satisfies the cocycle condition by `isCocycleSection_of_mul_eq` and
  `IsCocycleSection.map`. The restriction of `m m'` is the pullback of the restriction of
  `r` to `D(r)`, which is a unit (`isUnit_res_basicOpen`). Hence the restriction of `m` is a
  unit as well.
