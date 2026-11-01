# Poincaré pullbacks along base-changed dual maps

For a morphism of schemes `b : S' ⟶ S`, an abelian scheme `A/S` with actual dual
data `hA : HasDualScheme A`, and the explicit input
`universality : PicardZeroUniversalBaseChangeStatement`, this module compares two
families. The first is the Poincaré pullback along a base-changed map into the
dual. The second is the base change of the original Poincaré pullback. This
module provides the family comparison used by `polarizationBaseChange`.

- `baseChangeParameterMate_pullback_map b g`. For `g : Q ⟶ P` over `S`, the mate
  `baseChangeParameterMate b ((Over.pullback b).map g)` (module
  `FamilyBaseChangeNaturality`) equals `baseChangeParameterMap b Q ≫ g`. It is
  proved by extensionality on the underlying scheme maps.
- `dualSchemeBaseChangeIsoPullbackIso b universality A hA f`. For
  `f : Q ⟶ dualScheme A hA` over `S`, this is a rigidified isomorphism. Its source
  is the pullback of the Poincaré family of `A_{S'}` along
  `(Over.pullback b).map f ≫ (dualSchemeBaseChangeIso ...).hom`. Its target is
  `baseChangeFamily b A Q` applied to the pullback of `poincareFamily A hA` along
  `f`. The isomorphism is the composite of:
  1. the composition isomorphism `RigidifiedLineBundle.relativePullbackComp`, which
     splits the pullback along the composite;
  2. `dualSchemeBaseChangePullbackIso` (module `DualSchemeBaseChange`), the
     property that characterizes the canonical comparison: pulling back the
     Poincaré family of `A_{S'}` along it gives the base-changed Poincaré family;
  3. `baseChangeFamilyPullbackIso`, the naturality of `baseChangeFamily` in the
     parameter;
  4. the mate identity above and `relativePullbackComp` again.
- `dualBaseChangeMapPoincareForgetIso b universality A hA f`. For
  `f : A.X ⟶ dualScheme A hA`, this is an isomorphism of ordinary line bundles on
  `A_{S'} ×_{S'} A_{S'}`. Its source is the underlying bundle of the Poincaré
  pullback along `dualBaseChangeMap A hA universality b f`. Its target is the
  pullback along `baseChangeFamilySpaceMap b A A.X` of the underlying bundle of
  the Poincaré pullback along `f`. It is obtained from the previous isomorphism
  with `Q = A.X` and `baseChangeFamilyForgetIso`.

## Scope and provenance

This is internal, derived infrastructure. Every map is the existing actual
construction: scheme pullback, the canonical `dualSchemeBaseChangeIso` and
`baseChangeFamily`. No target identification is chosen freely. The module
asserts no representability, coherence of the dual comparison under successive
base change, or polarization property.
