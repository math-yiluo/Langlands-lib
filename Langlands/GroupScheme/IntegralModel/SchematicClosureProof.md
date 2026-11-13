# Proof of the schematic-closure integral-model statement

## Result

`Langlands.GroupScheme.integralModelSchematicClosure` proves
`Langlands.GroupScheme.IntegralModelSchematicClosureStatement.{u}` at an
arbitrary universe `u`. The statement and its meaning are in
`Langlands/GroupScheme/IntegralModel/SchematicClosure.md`. Its inputs are a
discrete valuation ring `R` with specified fraction field `K`, group schemes `G`
and `H` over `Spec K`, an integral model `N : IntegralModel R K G`, and a
homomorphism `j : H ⟶ G` whose underlying scheme morphism is a closed immersion.
The proof constructs an integral model `M` of `H` and a model morphism
`φ : M.Hom N j` with `φ.IsSchematicClosure`. No model of `H`, parahoric model or
other model-availability statement is assumed.

This is the existence half of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Lemma A.2.1(1), together with the group-scheme assertion of
Lemma A.2.3 (printed pp. 593–595 / PDF pp. 624–626; registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`). KP's proof is algebraic: the
closure has coordinate ring `o[𝒳]/(I ∩ o[𝒳])`, which is torsion-free and hence
flat. Its group law extends because `𝓗 × 𝓗` is flat, so it is the closure of
its generic fibre. The Lean proof follows this outline geometrically, through
scheme-theoretic images and schematic dominance rather than explicit coordinate
rings. All declarations except the final theorem are internal steps of this
proof. They live in the namespace
`Langlands.GroupScheme.IntegralModel.SchematicClosureConstruction`.

Throughout, `β = Spec.algebraMap R K : Spec K ⟶ Spec R`, and
`Φ = (j ≫ N.genericIso.inv).hom.hom : H.X ⟶ N.genericFibre.X` is the given
closed subgroup followed by the inverse of the given generic identification.

## Auxiliary facts

- `flat_of_appTop_injective`. Let `R` be a discrete valuation ring, `X` an
  affine scheme and `g : X ⟶ Spec R`. Suppose some `t : Y ⟶ X` is injective on
  global sections and sends the image of every nonzero `r : R` to a unit. Then
  `g` is flat. Proof: by `HasRingHomProperty.iff_of_isAffine`, flatness of `g`
  is flatness of the ring map `R → Γ(X)` (after the isomorphism
  `Γ(Spec R) ≅ R`). If `r • m = 0` with `r ≠ 0`, applying `t` gives
  `t(r) · t(m) = 0` with `t(r)` a unit, so `t(m) = 0` and `m = 0`. Hence
  `Γ(X)` is a torsion-free `R`-module, and Mathlib's instance for Dedekind
  domains makes it flat. This is KP's remark that torsion-free modules over a
  discrete valuation ring are flat.
- `mono_specAlgebraMap`, `flat_specAlgebraMap`,
  `isSchemeTheoreticallyDominant_specAlgebraMap` (for any domain `R` with
  fraction field `K`). `β` is a monomorphism, because `R → K` is an epimorphism
  of rings (`IsLocalization.epi`) and `Spec` is a right adjoint. It is flat
  because localization is flat. It is scheme-theoretically dominant because
  `R → K` is injective and `Spec R` is affine.
- `isMonHom_of_comp_mono`. In a cartesian monoidal category, if `m` is a
  monomorphic monoid morphism and `g ≫ m` is a monoid morphism, then so is `g`
  (cancel `m` in the unit and multiplication identities).

## The closure and its inclusion

- `genericOver N j : (Over.map β).obj H.X ⟶ N.group.X` is the morphism over
  `Spec R` with underlying scheme morphism exactly
  `j.hom.hom.left ≫ N.genericToModel` (`genericOver_left`, by `rfl`).
  `baseChangePointsEquiv_generic` identifies it with the image of `Φ` under the
  Library's multiplicative pullback-adjunction equivalence
  `baseChangePointsEquiv β N.group H.X`. By naturality of this equivalence
  (`map_comp_genericOver`), for every test object `T` over `Spec K` and every
  `a : T ⟶ H.X`, `(Over.map β).map a ≫ genericOver N j` is the image of
  `a ≫ Φ`. Since `Φ` is a group homomorphism and the equivalence is
  multiplicative, this translates the group laws of `H` into the group law of
  `N.group`.
- `closureOver N j` is Mathlib's scheme-theoretic image
  `(genericOver N j).left.image` (the closed subscheme cut out by the kernel
  ideal sheaf), over `Spec R` via `imageι ≫ N.group.X.hom`.
  `inclusionOver N j` has underlying morphism `imageι`, a closed immersion and
  a monomorphism. `projectionOver N j` has underlying morphism `toImage`, and
  `projectionOver_fac` says `projectionOver ≫ inclusionOver = genericOver`.
- The structure morphism of the closure is affine and locally of finite type,
  being a closed immersion followed by the affine finite-type `N.group.X.hom`.
- Under the closedness of `j`, `genericOver N j` is quasi-compact. The
  projection is quasi-compact and scheme-theoretically dominant
  (`ImageGeneration.isSchemeTheoreticallyDominant_toImage`, using that
  `N.group.X.left` is affine).
- `flat_closureOver` (for a discrete valuation ring `R`). The closure is
  affine. Apply `flat_of_appTop_injective` with `t` the projection, which is
  injective on global sections by dominance. Its composite with the closure's
  structure morphism is `H.X.hom ≫ β`, so a nonzero `r` maps to the image of the
  unit `algebraMap R K r` of `K`.

## The group law (KP A.2.3)

Each operation of `N.group` is restricted to the closure by
`exists_over_factor_of_schematic_precomp` (Library, `ImageGenerationDominant`).
That lemma says: if a morphism into `N.group.X` agrees after a
scheme-theoretically dominant precomposition with a morphism factoring through
the closed immersion, then it factors through the closed immersion.

- Unit (`exists_closureOne`). Precompose with the terminal morphism
  `genericBaseOver`, whose underlying map is `β`, which is dominant. The
  composite is the image of `η[H.X] ≫ Φ = 1`, hence the unit point of `N.group`.
- Multiplication (`exists_closureMul`). Precompose
  `(inclusionOver ⊗ inclusionOver) ≫ μ` with
  `squareComparison ≫ (projectionOver ⊗ projectionOver)`. Here
  `squareComparison : (Over.map β).obj (H.X ⊗ H.X) ⟶ H' ⊗ H'`, with
  `H' = (Over.map β).obj H.X`, is the canonical comparison of products over
  `Spec K` and over `Spec R`. It is an isomorphism because `β` is a monomorphism
  (`isIso_squareComparison_left`). The tensor square of the projection is
  scheme-theoretically dominant by
  `ImageGeneration.isSchemeTheoreticallyDominant_tensorHom`. This uses
  flatness of `H'` over `Spec R` (a scheme over a field followed by the flat
  `β`) and of the closure (`flat_closureOver`). This is KP's use of the flatness
  of `𝓗 × 𝓗`. The composite equals the product of the images of
  `fst ≫ Φ` and `snd ≫ Φ`, which is the image of `μ[H.X] ≫ Φ`, because `Φ` is a
  homomorphism and the point equivalence is multiplicative. It therefore
  factors through the closure via `(Over.map β).map μ[H.X] ≫ projectionOver`.
- Inverse (`exists_closureInv`). Precompose with the projection. The composite
  is the image of `ι[H.X] ≫ Φ = (𝟙 ≫ Φ)⁻¹`.

`closureGrpObj` restricts the group structure of `N.group.X` along the
monomorphism `inclusionOver` with these lifts, using the Library's
`GroupObjectDescent.grpObjOfMono`, and `isMonHom_inclusionOver` makes the
inclusion a homomorphism. `closureGroup N j` is the resulting group scheme over
`Spec R`, and `closureInclusion N j : closureGroup N j ⟶ N.group` is the
inclusion homomorphism.

## The generic fibre (KP A.2.1(1))

- `genericToClosureOver N j : H.X ⟶ ((baseChange β).obj (closureGroup N j)).X`
  is the inverse image of `projectionOver` under the pullback-point
  equivalence. Applying the equivalence to its composite with the base-changed
  inclusion gives `projectionOver ≫ inclusionOver = genericOver`. Hence
  `genericToClosureOver_comp` says that this composite is `Φ`.
- The base-changed inclusion is a monomorphism (`Over.pullback` is a right
  adjoint) and a homomorphism, and `Φ` is a homomorphism. So
  `genericToClosureOver` is a homomorphism (`isMonHom_of_comp_mono`).
- It is a closed immersion (`IsClosedImmersion.of_comp`): its composite with
  the base-changed inclusion is `j.hom.hom.left ≫ N.genericIso.inv.hom.hom.left`,
  a closed immersion, and a monomorphism is separated.
- It is scheme-theoretically dominant. The square with top `𝟙 H.X.left`, left
  side `genericToClosureOver`, right side `projectionOver` and bottom the
  generic-fibre projection `pullback.fst _ β` is a pullback
  (`IsPullback.of_horiz_isIso_mono`: the top is an isomorphism and the bottom
  is a monomorphism, being a base change of `β`). The bottom map is flat,
  being a base change of `β`. So `IsSchemeTheoreticallyDominant.of_isPullback`
  transfers the dominance of the projection.
- A scheme-theoretically dominant closed immersion has trivial kernel, so it
  is an isomorphism (`IsClosedImmersion.isIso_iff_ker_eq_bot`). Over-category
  isomorphisms are detected on underlying morphisms. `genericToClosureIso`
  packages it as a group-scheme isomorphism
  `H ≅ (baseChange β).obj (closureGroup N j)` by `Grp.mkIso`.

## The model, its morphism and the closure clauses

- `closureModel N j : IntegralModel R K H` has group `closureGroup N j`,
  affine, flat and finite-type instances from the previous sections, and
  `genericIso := (genericToClosureIso N j).symm`.
- `closureModelHom N j : (closureModel N j).Hom N j` has
  `hom := closureInclusion N j`. Its `generic_comm` is reduced by
  `Iso.eq_inv_comp` to
  `genericToClosureIso.hom ≫ (baseChange β).map closureInclusion ≫ N.genericIso.hom = j`.
  On underlying morphisms this is
  `Φ ≫ N.genericIso.hom.hom.hom = j.hom.hom`, by `genericToClosureOver_comp`
  and `Iso.inv_hom_id`.
- `closureModelHom_isSchematicClosure`. The first clause is
  `isClosedImmersion_inclusionOver`. The second clause: the underlying morphism
  of `φ.hom` is `imageι = ker.subschemeι` for the kernel of
  `j.hom.hom.left ≫ N.genericToModel`, and Mathlib's
  `Scheme.IdealSheafData.ker_subschemeι` gives equality of kernels.
- `integralModelSchematicClosure` introduces the data, turns the hypothesis
  `IsClosedSubgroup j` into the closed-immersion instance, and returns
  `⟨closureModel N j, closureModelHom N j, closureModelHom_isSchematicClosure N j⟩`.

## Scope

The base is an arbitrary discrete valuation ring, as in the statement. The
Henselian hypothesis of KP Appendix A is not used. The discrete valuation
ring is used only in `flat_closureOver` (torsion-free modules over a Dedekind
domain are flat), which the multiplication step and the model need. The
closure is constructed for this closed subgroup only. The general bijection of
A.2.1(3), the flat-algebra point formula of A.2.1(2) and the Lie-algebra
assertion of A.2.3 are not proved here.
