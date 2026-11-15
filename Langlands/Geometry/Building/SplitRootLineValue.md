# Values of split apartment points along actual root lines

Lean module: `Langlands.Geometry.Building.SplitRootLineValue`.

This is internal infrastructure. It computes the values of points of a split
apartment class on the actual root subgroups. The value is read through an
arbitrary `k`-linear coordinate of the intrinsic root weight space. It derives
its content from published Library results: the Chevalley valuation of
Kaletha–Prasad (*Bruhat–Tits Theory: A New Approach*, §6.1(a), the functions
`φ_{o, a}` before Lemma 6.1.1), its normalizer-stable apartment class, the
uniqueness of split apartment classes, and the intrinsic root-point Lie
comparison. The value formula is the familiar statement that, on the split
apartment, `φ_a(x_a(u)) = ω(u) + const`. Here `x_a` is any `k`-linear
parametrization of the root line. The unit makes no further claim from the
literature.

Work at arbitrary universe `u` over a field `k`. No completeness, discreteness,
characteristic or residue-field hypothesis is made.

## Torus-equivariant additive lines

These results lie in the namespace
`Langlands.GroupScheme.VectorGroup.IsTorusEquivariant`.

- `transport`. Let `e : S ≅ S'` be an isomorphism of commutative group schemes
  and `f : G ≅ H` an isomorphism of group schemes over `Spec k`. Let
  `i : S → G` and `j : S' → H` satisfy `i ≫ f.hom = groupHom e.hom ≫ j`. If an
  additive line `x : 𝔾ₐ → H` is `j`-equivariant with character `a`, then
  `x ≫ f.inv` is `i`-equivariant with the pulled-back character `e.hom ≫ a`.
  Proof: rewrite `i` as `groupHom e.hom ≫ j ≫ f.inv` and compose the
  equivariance identity of `x` at the transported torus point with `f.inv`. The
  identity `comp_groupHom_comp` gives the character value.
- `isWeightVectorCoordinates_subgroupAction`. Let `x` be an `i`-equivariant
  additive line with character `α` that represents the intrinsic root subgroup
  `RelativeRoot.subgroup i α`. Then the natural coordinates of `𝔾ₐ` are weight
  coordinates of weight `α` for the actual torus action on the representative.
  Proof: `x` is a monomorphism, so it suffices to compare after composing with
  `x`. There the represented action is conjugation (`subgroupAction_act_comp`)
  and equivariance identifies conjugation with the weight action
  (`weightAction_comp`). The weight action acts on the natural coordinates by
  the character (`coordinates_weightAction_act`).
- `vectorPointLieEquiv_gaRationalEquiv`. The vector-group point-to-Lie
  comparison of the natural coordinates of `𝔾ₐ` sends the rational point with
  field coordinate `s` to `s` times the image of the point with coordinate `1`.
  Proof: apply injectivity of the Lie coordinates. The Lie coordinates of
  either image are the affine coordinates of the point
  (`vectorLieCoordinates_vectorPointLieEquiv`,
  `vectorAffineCoordinates_rationalCoeffEquiv`). Those coordinates are `s` and
  `1`, by `gaRationalEquiv_eq_scalarPoint` and `coordinates_scalarPoint`.
- `rootPointLieEquiv_smul` (linearity of intrinsic root coordinates along an
  equivariant line). Assume `T` is a split torus, `G` is smooth and affine,
  `α ≠ 0` has no higher roots, and `x` is an `i`-equivariant additive line with
  character `α` that represents the root subgroup. Then the intrinsic
  point-to-Lie equivalence `RelativeRoot.rootPointLieEquiv` sends the root point
  `x(s)` to `s` times the image of `x(1)`. Proof: the intrinsic equivalence
  agrees with the one built from the representative
  (`rootPointLieEquiv_eq_represented`). By
  `representedRootPointLieEquiv_apply` and `vectorPointLieEquiv_eq_of_weight`
  (applied to the weight coordinates above), the latter is the Lie target map
  of `x` composed with the vector-group comparison. Linearity then follows from
  the previous item and `k`-linearity of `Lie.targetMapLinear x k`.

## Split apartments

These results lie in the namespace `Langlands.Geometry.Building`. Let `G` be an
affine connected reductive group over `k` and `j : T → G` a split maximal
torus (a monomorphism on underlying schemes). Let
`omega : AddValuation k (WithTop ℝ)` take at least three values and let
`ω : kˣ → ℝ` agree with `omega` on units. Let `A : KPApartmentData j ω` be any
normalizer-stable apartment class.

- `exists_rootParametrization_value_of_isSplitTorus`. For every relative root
  `α` there is a monomorphic `j`-equivariant additive line
  `x : 𝔾ₐ → G` with character `α`. It has the following property: for every
  point `φ` of `A` there is a real constant `c` with
  `φ_α(x(s)) = omega(s) + c` for all `s : k`.

  Proof. The root datum existence theorem gives a reduced root datum `P` of
  `(G, j)`. Choose a base, Chevalley Lie data and a Chevalley group `Gc` for
  `P` over `k`. Let `t` be the isomorphism of split tori from `T` to the torus
  `Tk k` of `Gc` given by the canonical character identification `charEquiv`.
  Then `P` is also a root datum of the composite `groupHom t.hom ≫ Gc.t`
  (`IsRootDatumOf.precomp_torusIso`), and this composite is a maximal torus.
  The published split isomorphism theorem `splitCommonTorusIsomorphism` then
  gives `ψ : G ≅ Gc.H` compatible with the two tori. The transport of the
  Chevalley apartment `ChevalleyRootFamily.apartmentData` along `(t⁻¹, ψ⁻¹)`
  is again normalizer-stable apartment data for `j`. Uniqueness of split
  apartment classes (`KPApartmentData.eq_of_isMaximalTorus_of_isSplitTorus`)
  identifies it with `A`; its additivity hypothesis on `ω` follows from
  multiplicativity of `omega`. The root `α` corresponds to a Chevalley root
  `j0` (`relativeRoots_image_of_transport`, `mem_relativeRoots_iff`). The line
  is `x = Gc.u j0 ≫ ψ.inv`, whose equivariance comes from `transport` above.
  A point of the transported class is the transport of a translate
  `v +ᵥ family Gc omega`. Its value at `x(s)` is the Chevalley value at the
  Chevalley root point with coordinate `s`, plus the value of the root
  character at `v`. The Chevalley value is `omega(s)` (`family_root`,
  `additiveRootValue_coordinate`).

- `rootLinePoint hT j ha hhigh ℓ w` (definition). Here `G` is smooth and
  affine, `hT` says that `T` is split, `ha : α ≠ 0`, `hhigh` says that `α` has
  no higher roots, and `ℓ : k ≃ₗ[k] weightSpace j α` is a `k`-linear
  identification of `k` with the weight space of `α`. The definition is the
  rational point of `G` underlying
  `(RelativeRoot.rootPointLieEquiv hT j ha hhigh).symm (ℓ w)`. This is the
  unique actual `k`-rational point of the root subgroup of `α` whose intrinsic
  Lie coordinate is `ℓ w`. Thus `w ↦ rootLinePoint … ℓ w` is the root-group
  parametrization by `k` determined by `ℓ`. No maximality or reductivity is
  needed for the definition. `rootLinePoint_mem` records that the point lies
  in `RelativeRoot.subgroup j α`.

- `exists_rootLine_value_of_isSplitTorus` (values on actual root lines).
  Assume in addition that `G` is smooth and that the relative root `α` is
  nonzero and has no higher roots. Let `ℓ : k ≃ₗ[k] weightSpace j α` be any
  `k`-linear identification of `k` with the weight space of `α`, and let
  `φ ∈ A`. Then there is a real constant `c` such that, for every `w : k`,
  `φ_α(rootLinePoint hT j ha hhigh ℓ w) = omega(w) + c`.

  Proof. Take the line `x` and constant `c₀` from the previous result. By
  `represents_root`, `x` represents the root subgroup. Write `R` for the
  intrinsic equivalence and `p(s)` for the root point `x(s)`. By
  `rootPointLieEquiv_smul`, `R(p(s)) = s • R(p(1))`. The vector `R(p(1))` is
  nonzero because `p` is injective and `R` is an equivalence. Thus
  `m := ℓ⁻¹(R(p(1)))` is a nonzero element of `k`, and
  `R⁻¹(ℓ w) = p(w m⁻¹)` for every `w`. Hence the value is
  `omega(w m⁻¹) + c₀ = omega(w) + (ω(m⁻¹) + c₀)`, and the constant is
  `c = ω(m⁻¹) + c₀`.

The constant depends on `φ` and `ℓ`, but not on `w`. No integral-model,
filtration-normalization or descent statement is made here.
