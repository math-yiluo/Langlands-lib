# Proof: constructibility of every geometric component count for schemes

Worker 189. The final theorem `schemeGeometricComponentCountConstructible` proves
`SchemeGeometricComponentCountConstructibleStatement.{u}`. This is the scheme case of
Conrad, *Weil and Grothendieck approaches to adelic points*, December 31, 2011,
printed p.13 Lemma 5.1 (registered source
`conrad-2011-weil-grothendieck-adelic-points`), which refers to EGA IV₃ 9.7.7. For every
commutative ring `B`, every morphism `f : X ⟶ Spec B` that is locally of finite
presentation, quasi-compact and quasi-separated, and every `n : ℕ`, the set of points
`p` with `geometricFiberComponentCount f p = n` is constructible. No hypothesis is
added.

The Lean proof upgrades the Library's proof of constructibility of the geometrically
connected locus (`GeometricallyConnectedGenericOpenDescent`,
`GeometricallyConnectedConstructibilityFromGeneric`,
`GeometricallyConnectedFiberNoetherianReduction`, `SplitGenericFiberConnectedness`) from
a truth value to the count in `ℕ∞`. The new ingredient is the base-change invariance
`geometricFiberComponentCount_baseChange` from the helper module
`SchemeGeometricComponentCountBaseChange`.

## Steps

1. `GeometricFiberComponentCountConstancyAt f η` is an auxiliary proposition. It says
   that some open neighbourhood `U` of `η` satisfies
   `geometricFiberComponentCount f y = geometricFiberComponentCount f η` for all
   `y ∈ U`.
2. `geometricFiberComponentCountConstancyAt_of_split_components`: let `Y` be
   Noetherian, `f` locally of finite type and quasi-compact, and `η` a generic point
   of `Y`. Suppose every irreducible component of the fibre over `η` is geometrically
   irreducible (`FiberComponentsGeometricallyIrreducible f η`). Then constancy holds
   at `η`. Two published inputs, the Library lemma
   `exists_open_genericComponentClosures_geometricallyIrreducible_and_incidence` and
   the proved spreading theorem `finiteTypeGeometricallyIrreducibleGenericSpreading`,
   give an open `U ∋ η` with three properties at every `y ∈ U`:
   - the closures of the generic-fibre components cover the fibre over `y`;
   - their fibre pieces are geometrically irreducible, hence geometrically connected;
   - their incidence at `y` is the incidence of the components at `η`.

   By `geometricFiberComponentCount_eq_incidence`, the count at each `y ∈ U` is the
   number of incidence classes of the generic-fibre components, which does not
   depend on `y`.
3. `geometricFiberComponentCountConstancyAt_of_open_baseChange`: take an actual
   cartesian square `IsPullback a b f g` with `f` locally of finite type and
   quasi-compact, and `g` open. Constancy for `b` at any point gives constancy for
   `f` at a whole-space generic point `η`. The image of the open neighbourhood
   upstairs is open and contains `η`, and base-change invariance transports
   the constant value along `g`.
4. `geometricFiberComponentCountConstancyAt_of_isGenericPoint`: for a Noetherian `Y`
   with generic point `η`, the proved splitting theorem
   `finiteTypeFiniteEtaleGenericComponentSplitting` gives an open `V`, an irreducible
   affine finite étale surjection `Y' ⟶ V` and a generic point `η'` of `Y'` over which
   the pulled-back fibre components are geometrically irreducible. Step 2 applies
   upstairs. Pasting the splitting pullback with the open-restriction square
   (`isPullback_morphismRestrict`) gives an actual cartesian square whose bottom map
   is open, being étale followed by an open immersion. Step 3 then gives constancy at
   `η`.
5. `exists_open_irreducibleClosed_geometricFiberComponentCount`: let `Y` be
   Noetherian and `Z` an irreducible closed subset. Equip `Z` with its vanishing-ideal
   closed subscheme structure, and apply step 4 to the base change of `f` to it at its
   generic point. The resulting open neighbourhood is relatively open in `Z`. It has
   the form `Z ∩ V` for some open `V`, and base-change invariance shows the count is
   constant on `Z ∩ V`. Hence, for each `n : ℕ∞`, `Z ∩ V` lies inside the level set
   `{y | count = n}` or is disjoint from it.
6. `isConstructible_geometricFiberComponentCount_of_isNoetherian`: over a Noetherian
   `Y`, the Library's Noetherian induction
   `isConstructible_of_irreducibleClosed_genericConstancy` turns step 5 into
   constructibility of every level set.
7. `schemeGeometricComponentCountConstructible`: for an arbitrary ring `B`, the
   published Noetherian approximation
   `NoetherianApproximation.schemeSubalgebraDescent` (over `ULift ℤ`) is applied to
   `f`. It requires `f` to be locally of finite presentation, quasi-compact and
   quasi-separated, so all three hypotheses of the target are used here; the
   quasi-separatedness of `f` is passed implicitly as an instance. The descent gives a
   finitely generated, hence Noetherian, subring `T ⊆ B`. It also gives a morphism
   `f₀ : X₀ ⟶ Spec T`, locally of finite presentation, quasi-compact and
   quasi-separated, and a cartesian square exhibiting `f` as the base change of `f₀`
   along `Spec B ⟶ Spec T`. Base-change invariance identifies the level set of `f`
   with the preimage of the level set of `f₀`. Step 6 makes the latter constructible,
   and preimages of constructible sets under morphisms of schemes are constructible
   (`Scheme.Hom.isConstructible_preimage`).

The lemmas of steps 2–6 assume only that the morphism is locally of finite type and
quasi-compact. The quasi-separatedness of the descended morphism `f₀` returned in
step 7 is not needed afterwards. The quasi-separatedness of `f` itself is a required
input of the descent in step 7. The proof uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
