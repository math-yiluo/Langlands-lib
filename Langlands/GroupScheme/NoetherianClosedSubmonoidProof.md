# Proof of closed submonoid recognition over an arbitrary base

`noetherianClosedSubmonoid` proves `NoetherianClosedSubmonoidStatement.{u}` from
`Langlands.GroupScheme.NoetherianClosedSubmonoidStatement`, for every scheme
base `B` in an arbitrary universe `u`.

The proof introduces the target's data: the base `B`, the group scheme `G`, the
object `Z` of `Over B`, the morphism `j : Z ⟶ G.X` with `IsClosedImmersion j.left`,
the multiplication `m : Z ⊗ Z ⟶ Z` with `hm : m ≫ j = (fst Z Z ≫ j) * (snd Z Z ≫ j)`,
the unit `e : 𝟙_ (Over B) ⟶ Z` with `he : e ≫ j = 1`, and the hypotheses that
`(Z ⊗ Z).left` is affine and locally Noetherian. The target takes these last
three facts as explicit arguments. The published construction takes them as
typeclass instances, so the proof first adds them to the local context as
instances.

It then applies the construction in `Langlands.GroupScheme.ImageGenerationSubgroup`:

- `H := closedSubgroup j m hm e he`, the actual group scheme whose underlying
  object is definitionally `Z` (`closedSubgroup_X`);
- `i := closedSubgroupHom j m hm e he`, the inclusion as a group-scheme
  homomorphism;
- `isClosedSubgroup_closedSubgroupHom j m hm e he` shows that `i` is a closed
  subgroup;
- `a := Iso.refl Z`, which has type `Z ≅ H.X` because `H.X` is definitionally `Z`.

The remaining equation `a.hom ≫ i.hom.hom = j` follows by rewriting with
`closedSubgroupHom_hom`, which gives `i.hom.hom = j`, and then using
`Category.id_comp`.

The construction is not reproved here. It restricts the shear `(x, y) ↦ (x, x y)`
of `G × G` to `Z × Z`. That restriction is a closed-immersion endomorphism of the
Noetherian affine scheme `Z × Z`, hence an isomorphism. Applying its inverse to
`(x, 1)` shows that inverses of points of `Z` again factor through `Z`, on every
test object. The subgroup functor of points factoring through `Z` is then
represented by `Z` through the representability-transfer interface.

The theorem keeps every hypothesis of the target and adds none: there is no
field, characteristic, smoothness, reducedness or irreducibility assumption, and
the conclusion holds on every test scheme, including nonreduced ones. Worker 1378
wrote the construction. It is imported from the Library, and this module only
fits it to the target's argument form.
