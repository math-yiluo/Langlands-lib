# Preimages of Borel subgroups under central isogenies over an algebraically closed field

Author: Worker 1499. Two lemmas are adapted from Worker 1459's published
`Adjoint/QuasiSplitProof.lean`: `isSolvable_of_central_kernel` and
`isBorelSubgroup_image`. Their originals,
`AdjointQuotientBorelImage.isSolvable_of_central_kernel` and
`AdjointQuotientBorelImage.isBorelSubgroup_image`, assume an adjoint quotient
`IsAdjointQuotient q`. The adapted versions assume only that the
scheme-theoretic kernel of `q` is central (`IsCentral (kernelι q)`). The rest of
the proof is the same and reuses the published
`AdjointQuotientBorelImage.surjective_identityCore_comp`.

Namespace `Langlands.GroupScheme.CentralIsogenyBorelPreimage`. Throughout, `k`
is an algebraically closed field (`[Field k] [IsAlgClosed k]`), and all group
schemes are over `Spec k`. This module is a helper for
`CentralIsogeny/QuasiSplitLift.lean`.

## `isSolvable_of_central_kernel`

Hypotheses: `q : G ⟶ A` with `IsCentral (kernelι q)`, a monomorphism
`a : C ⟶ G`, maps `r : C ⟶ J` and `j : J ⟶ A` with `a ≫ q = r ≫ j`, and a
solvable `J`. Conclusion: `IsSolvableGroupScheme C`.

Proof. Over an algebraically closed field, solvability is tested on rational
points (`isSolvableGroupScheme_iff_isSolvable_points`). Let `R : C(k) → J(k)` be
the induced homomorphism. If `x` lies in the kernel of `R`, then `x ≫ a` maps
to `1` under `q`. So `x ≫ a` lies in the centre of `G`
(`isCentral_kernelι_iff`). Since `a` is a monomorphism, the kernel of `R` is
commutative. Then `C(k)` is an extension of a subgroup of the solvable `J(k)`
by a commutative group, hence solvable (`Group.isSolvable_of_ker_le_range`).

## `isBorelSubgroup_image`

Hypotheses:

- `G` is smooth and affine, and `A` is affine.
- `i : B ⟶ G` is a Borel subgroup.
- `q : G ⟶ A` is flat, locally of finite presentation, with central kernel.
- `p : B ⟶ I` is surjective and locally of finite type.
- `j : I ⟶ A` is a closed subgroup with `I` smooth and connected.
- `i ≫ q = p ≫ j`.

Conclusion: `IsBorelSubgroup j`.

Proof. `I` is solvable because `B(k) → I(k)` is surjective
(`rationalPoints_surjective`). For maximality, let `j' : J ⟶ A` be a smooth
connected solvable closed subgroup with `f : I ⟶ J` and `f ≫ j' = j`.

1. Form the preimage `P = SubgroupPreimage.groupScheme q j'` and its reduced
   identity component `C` (`ReducedSubgroup.identityCore`).
2. By the previous lemma, `C` is solvable.
3. The map `B ⟶ P` (`quotientOvergroupHom`) factors through `C`, and Borel
   maximality of `i` makes `B ⟶ C` an isomorphism.
4. The projection `P ⟶ J` is a base change of `q`, so it is flat and locally
   of finite presentation. By `AdjointQuotientBorelImage.surjective_identityCore_comp`,
   `C ⟶ J` is surjective. Hence `p ≫ f` is surjective, and so is `f`.
5. `f` is a closed immersion (`IsClosedSubgroup.of_comp`) and `J` is reduced
   (smooth over a field). A surjective closed immersion into a reduced scheme
   is an isomorphism (`isIso_of_isClosedImmersion_of_surjective`). This is
   reflected through the forgetful functors to an isomorphism of group
   schemes.

## `exists_isBorelSubgroup_center_le`

Statement: if `G` is connected reductive, there is a Borel subgroup
`i : B ⟶ G` with `center G ≤ SubgroupFunctor.range i`. Both sides are subgroup
functors, so the containment holds on every test scheme. This covers the
full scheme-theoretic centre, which may be nonreduced.

Proof. The route uses the centralizer `C` of a maximal torus `T`. It needs
only that `C` is smooth, connected and solvable. It does not use the
reductivity of `C` (`MaximalTorusCentralizerStatement`).

1. Choose a maximal torus `j : T ⟶ G` (`maximalTorusExistence`).
2. Over an algebraically closed field `T` is split. Choose a generic
   cocharacter `ν` (`IsSplitTorus.exists_genericCocharacter`). By
   `genericCentralizer`, the dynamic centralizer of `ν` equals the centralizer
   of `T`.
3. Take a closed representative `c : C ⟶ G` of the centralizer of `T`
   (`fieldCentralizerRepresentability`). As a dynamic centralizer, `C` is smooth
   (`dynamicSmooth`) and connected (`dynamicConnected`).
4. `T` factors through `C` as a central maximal torus
   (`torusCentralizerFactor`, `isCentral_torusCentralizerFactor`).
5. The quotient `Q = C/T` (`normalSubgroupQuotient`) contains no nontrivial
   torus (`centralMaximalTorusQuotientStatement`). So `Q` is unipotent
   (`noTorusUnipotent`) and has solvable points. Then
   `isSolvable_points_of_isFppfQuotient` makes `C` solvable.
6. `solvableSubgroupBorelContainment` puts `C` in a Borel subgroup `i`.
7. `center_le_torusCentralizer` places the centre in the centralizer of `T`,
   which is the range of `c`, hence in the range of `i`.

## `isBorelSubgroup_of_range_eq_comap`

Hypotheses:

- `G` and `A` are connected reductive.
- `π : G ⟶ A` is a central isogeny.
- `j : B ⟶ A` is a Borel subgroup.
- `i : P ⟶ G` is a closed subgroup with
  `SubgroupFunctor.range i = (SubgroupFunctor.range j).comap π`.

Conclusion: `IsBorelSubgroup i`. So the scheme-theoretic preimage of a Borel
subgroup is a Borel subgroup.

Proof.

1. Take a Borel subgroup `i₁ : B₁ ⟶ G` containing the centre, from the
   previous lemma. It then contains the kernel of `π`
   (`IsCentralIsogeny.kernel_range_le_center`).
2. `HomImage.exists_image` gives a smooth connected closed image `jI : I ⟶ A`
   of `i₁ ≫ π`, with a flat surjective factor `p`, locally of finite
   presentation. By `isBorelSubgroup_image`, `jI` is a Borel subgroup.
3. Borel conjugacy (`borelConjugacy`) gives a rational point `a` of `A` and
   `φ : I ≅ B` with `jI ≫ int a = φ.hom ≫ j`.
4. Lift `a` to a rational point `g` of `G` (`rationalPointLift`). The conjugate
   `i₀ = i₁ ≫ int g` is Borel (`IsBorelSubgroup.comp_iso`). It satisfies
   `i₀ ≫ π = (p ≫ φ.hom) ≫ j` (`innerIso_hom_comp`). It still contains the
   kernel, since conjugation fixes a central map
   (`IsCentral.comp_innerIso_hom`).
5. These data form an fppf image square (`SubgroupFunctor.IsFppfImage`), so
   `IsFppfImage.comap_eq_of_kernel_le` gives
   `(range j).comap π = range i₀`.
6. Hence `range i = range i₀`. `IsClosedSubgroup.sourceIsoOfRangeEq` gives an
   isomorphism `P ≅ B₁` compatible with the inclusions, and
   `IsBorelSubgroup.iso_comp` transports the Borel property to `i`.

The route matches the argument in Milne, *Algebraic Groups* (2017),
Proposition 17.54(a), as cited in `CentralIsogeny/QuasiSplitLiftStatement.md`:
a kernel contained in a Borel subgroup `B'` gives `B' = φ⁻¹(φ(B'))`. The Lean
proof works with scheme-theoretic kernels and subgroup functors throughout.

## Check record

`lean_check` diagnostic `63826810-98a4-42e8-9386-7a288cc67194` compiled this
module and `CentralIsogeny/QuasiSplitLift` on Library base `d2fd0b68` with
0 errors and 0 warnings. It used only the axioms `propext`, `Classical.choice`
and `Quot.sound`.
