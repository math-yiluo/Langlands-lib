# The two-axis class presheaf has small values: proof

Author: Worker 384.

The module `Langlands.AlgebraicGeometry.Picard.TwoAxisClassSmallValuesProof`
proves

```lean
theorem Langlands.AlgebraicGeometry.Picard.noetherianTwoAxisClassSmallValues :
    Langlands.AlgebraicGeometry.Picard.NoetherianTwoAxisClassSmallValuesStatement.{u}
```

It imports the published statement module
`Langlands.AlgebraicGeometry.Picard.TwoAxisClassMurreConditionsStatement`
unchanged and keeps the arbitrary universe `u`. For every noetherian ring `R`
in `Type u`, every abelian scheme `A` over `Spec R` and every test object
`T : Over (Spec R)`, the value of `TwoAxisRigidifiedLineBundle.classPresheaf A`
at `T` is `u`-small. That value is a type in `Type (u + 1)`: the isomorphism
classes of two-axis-rigidified line bundles on the self-product of the base
change of `A` to `T`.

The proof does not use the noetherian hypothesis. It holds over every base.

## Implemented proof

The proof has two steps. First, a two-axis class is determined by the class of
its underlying sheaf. Second, the isomorphism classes of line bundles on a
fixed scheme form a `u`-small set.

### Line bundle classes are small

The abbreviation `LineBundle.PointCocycleData Z` is the type

```lean
Σ T : Z → Z.Opens, ∀ i j : Z, (Γ(Z, T i ⊓ T j))ˣ
```

It holds an open set for each point of the scheme `Z` and a unit of the
structure sheaf on each pairwise intersection. It lies in `Type u`.
`LineBundle.gluedModuleClass Z d` is the isomorphism class, in
`Quotient (isIsomorphicSetoid Z.Modules)`, of the published glued module sheaf
`CocycleGluing.glued d.2`.

`LineBundle.exists_gluedModuleClass_eq` shows that every locally free module
sheaf `M` of rank one has the class of such a glued sheaf:

- `OpenImmersionIdeal.exists_isFrameOn_of_isLocallyFreeRankOne` gives, for each
  point `x`, an open neighbourhood `T x` with a frame `e x` of `M` on it.
- These opens cover `Z`, so the published comparison
  `CocycleGluing.frameIso` (with `CocycleGluing.isTransition_frameCocycle`)
  identifies `M` with the sheaf glued from the frame cocycle
  `CocycleGluing.frameCocycle e he`.

`LineBundle.small_lineBundleModuleClasses Z` concludes that the classes of
locally free sheaves of rank one form a `u`-small subtype. They lie in the range
of `gluedModuleClass Z`, whose domain is in `Type u`, so `small_of_injective`
applies to the inclusion into this range.

### Two-axis classes are small

`TwoAxisRigidifiedLineBundle.small_isoClasses A` sends the class of a
two-axis-rigidified line bundle on the self-product `(mumfordProduct A).left`
to the class of its underlying sheaf `L.obj.carrier`. The forgetful functor
`TwoAxisRigidifiedModule.forget` makes the map well defined. The map is
injective by the published theorem `TwoAxisRigidifiedLineBundle.nonempty_iso_of_carrierIso`
(module `TwoAxisCarrierIsoAbelian`): two two-axis-rigidified line bundles with
isomorphic underlying sheaves are isomorphic. With the previous step,
`small_of_injective` gives smallness.

`TwoAxisRigidifiedLineBundle.small_classPresheaf_obj A T` applies this to the
base change `TwoAxisFamily.abelian A T`, whose class type is by definition the
value `(classPresheaf A).obj (op T)`. The theorem
`noetherianTwoAxisClassSmallValues` applies it to every `R`, `A` and `T`.

## Source

The statement is derived: it is Murre's requirement that the functor takes
values in sets, specialized to the functor of divisorial correspondences in the
proof of Raynaud, *Faisceaux amples sur les schémas en groupes et les espaces
homogènes*, LNM 119, Theorem III 4.4. See `TwoAxisClassMurreConditionsStatement.md`.
The argument here (gluing data indexed by points) is the standard set-theoretic
bound and is internal to this proof.
