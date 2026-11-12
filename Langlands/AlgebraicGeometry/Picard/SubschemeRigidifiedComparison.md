# The etale-fppf comparison from a rigidifying finite subscheme

Module `Langlands.AlgebraicGeometry.Picard.SubschemeRigidifiedComparison`.

This internal module assembles the rigidification argument for
`Langlands.AlgebraicGeometry.Picard.FieldEtaleFppfClassSheafStatement`. It combines the
abstract locality engine `QuotientActionLocality` with the rigidified classes of
`SubschemeRigidifiedClasses`, `SubschemeRigidifiedDescent` and `SubschemeRigidifiedLocal`, and
with the unit group schemes of `RelativeUnitGroupSchemes`.

## A generic injectivity criterion

`QuotientActionLocality.QuotientAction.isLocallyInjective_etale` (namespace
`Langlands.AlgebraicGeometry.Picard.QuotientActionLocality.QuotientAction`). Let `D` be a
`QuotientAction S` whose presheaf `D.P` is fppf-separated and whose quotient homomorphism
`D.q` is smooth and surjective. Let `forget : D.P ⟶ F` and `toE : F ⟶ D.E` satisfy
`forget ≫ toE = D.π`. Assume the action does not change `forget`, and `forget` is
etale-locally surjective. Then `toE` is etale-locally injective.

Proof. Take sections `a, b` of `F` over `T` with the same image in `D.E`. On the etale
covering sieve where both lift along `forget`, the lifts `x, y` have the same image under
`D.π`. The engine's `etale_locally_orbit` makes them translates `x = h · y` etale-locally.
Since the action does not change `forget`, `a` and `b` agree there. Grothendieck
transitivity then shows the equalizer sieve of `a, b` is etale covering. The argument
follows Mathlib's `isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective`.

## Rigidified classes: separation and local surjectivity

Namespace `Langlands.AlgebraicGeometry.Picard.SubschemeRigidification`, for
`f : X ⟶ S`, `g : Z ⟶ S`, `z : Z ⟶ X`, `hz : z ≫ f = g`.

- `classPresheaf_isSeparated_fppf` (assuming that rigidified isomorphisms are unique): the
  presheaf of rigidified classes is separated for the slice fppf topology. The engine
  criterion `isSeparated_fppf_of_zariski_of_affine` reduces this to Zariski separation
  (`classPresheaf_isSeparated_zariski`) and separation along faithfully flat maps of affine
  schemes (`classes_flatSeparated`).
- `forgetClassNatTrans_isLocallySurjective` (for finite `g`): forgetting the rigidification is
  etale-locally surjective. Each ordinary class is represented by a line bundle
  (`RelativePicard.exists_representative`). By `exists_open_rigidification` it acquires a
  rigidification on an open neighbourhood of every point, and open immersions are etale
  (`etale_mem_of_points`).

## Over a field

Let `k` be a field, `f : X ⟶ Spec k` proper, `g : Z ⟶ Spec k` finite, `z : Z ⟶ X` and
`hz : z ≫ f = g`.

`quotientAction f g z hz Q q hker` is the `QuotientAction` with:

- `P` the rigidified classes and `E = RelativePicard.classSheafPresheaf f`, the published fppf
  Picard class sheaf;
- `π` the forgetful map followed by the fppf sheafification unit `RelativePicard.toClassSheaf f`;
- `H = fieldGroup g`, the units of `T ×_k Z`, acting through `fieldPointsEquiv` by changing
  rigidifications (`actClasses`);
- a homomorphism `q : fieldGroup g ⟶ Q` whose kernel is described by `hker`: a point lies in the
  kernel exactly when its unit comes from `T ×_k X`.

The action laws are `actClasses_one`, `actClasses_mul` and `classesPullback_actClasses` with
`pointsEquiv_comp`. Invariance is `forgetClasses_actClasses`, and the stabilizer condition is
`actClasses_eq_self_iff` with `hker`. Fppf-local orbits come from the fppf local injectivity of
sheafification (the published instance `toClassSheaf_isLocallyInjective`) together with
`exists_eq_actClasses_of_forgetClasses_eq`.

**`isSheaf_etaleClassSheafPresheaf_of_rigidifying`.** Assume that for every test `T` the map
on global functions of `T ×_k Z ⟶ T ×_k X` (`(zRel f g z hz).app T`) is injective. Then
`RelativePicard.etaleClassSheafPresheaf f` is an fppf sheaf on the whole slice.

Proof.

1. Rigidified isomorphisms are unique (`iso_subsingleton`).
2. `exists_quotient` gives `Q` and `q`: smooth and affine, with `q` flat, surjective, of finite
   presentation, affine and smooth, and with the kernel description.
3. The engine's `isLocallySurjective_etale` shows that `RelativePicard.toClassSheaf f` is
   etale-locally surjective. Its hypotheses:
   - `P` is fppf-separated (above);
   - `E` is an fppf sheaf;
   - `π` is fppf-locally surjective, as a composite of locally surjective maps;
   - descent data of rigidified classes along affine faithfully flat maps descend to ordinary
     classes (`exists_descended_class`).
4. `isLocallyInjective_etale` shows that `RelativePicard.toClassSheaf f` is etale-locally
   injective.
5. Mathlib's factorization lemmas apply to `toEtaleClassSheaf_etaleToFppf`, using that etale
   sheafification is locally surjective. They make the canonical comparison
   `RelativePicard.etaleToFppfClassSheaf f` locally injective and locally surjective, hence an
   isomorphism (`Sheaf.isLocallyBijective_iff_isIso`).
6. The published `RelativePicard.etaleToFppfClassSheaf_isIso_iff` turns the isomorphism into
   the fppf sheaf property.

## Provenance

Internal. Rigidifying along a finite subscheme and dividing by the units of `X` is the standard
route to comparing topologies for Picard functors. The formalization uses only published Library
results, the staged internal modules named above, and Mathlib.
