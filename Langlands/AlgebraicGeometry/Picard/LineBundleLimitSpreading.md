# Spreading a line bundle along a cofiltered limit of schemes

This helper module is used in the proof of
`Langlands.AlgebraicGeometry.Picard.AlgebraicExtensionAmpleExistenceSpreadingStatement`.
It is internal: it is not a Library statement and has no literature source of its own.
In the situation needed there, it replaces the limit results for invertible modules in the
Stacks Project (Limits, Lemma 32.10.3). It builds on the descent theorem `exists_lineBundle_of_descent` of
`Langlands.AlgebraicGeometry.Picard.LineBundleDescent` and on Mathlib's
`Mathlib.AlgebraicGeometry.AffineTransitionLimit`.

## Auxiliary lemmas

- `exists_forall_of_isCofiltered`: in a cofiltered category, finitely many properties `P j`,
  each satisfied by some object and each passing from the target of a morphism to its source,
  are satisfied by one common object. The proof uses `IsCofiltered.inf_objs_exists`.
- `appLE_eq_of_eq`: `appLE` of equal morphisms of schemes agree (after transporting the
  inclusion hypothesis).
- `map_injective_of_le_of_le`: the restriction map of a module sheaf between two opens that
  are equal (given as `W ≤ V` and `V ≤ W`) is injective.
- `preimage_π_app_preimage_map`: for a cone `c` over `D` and `f : j ⟶ i`, the preimage of
  `D.map f ⁻¹ V` under `c.π.app j` is the preimage of `V` under `c.π.app i`.
- `exists_appLE_eq_of_isAffineOpen` (and the variant `exists_appLE_eq_of_isAffineOpen'`, which
  takes an open `W` equal to `c.π.app i ⁻¹ V`): for a cofiltered diagram `D` with affine
  transition maps, a limit cone `c` and an affine open `V` of `D i`, every section of the limit
  over `c.π.app i ⁻¹ V` is the image under `appLE` of a section over `D.map f ⁻¹ V` at some
  stage `f : j ⟶ i`. The proof is the argument of Mathlib's `isBasis_preimage_isAffineOpen`:
  the opens `D.map f ⁻¹ V` form a cofiltered diagram of affine schemes with limit
  `c.π.app i ⁻¹ V` (`isLimitOpensCone`), and global sections turn this limit into a filtered
  colimit of rings, so every element comes from some stage.

## Main theorem `exists_lineBundle_of_isLimit`

Hypotheses:

- `D : I ⥤ Scheme` is a cofiltered diagram with affine transition maps, whose objects are
  quasi-compact and quasi-separated, and `c` is a limit cone of `D`;
- every projection `c.π.app i` is injective on sections over every open of `D i`, and
  surjective on points;
- `F` is a module sheaf on the limit `c.pt` with finitely many global sections `t j`
  (`J` finite) whose trivialization loci `trivializationOpen F (t j)` cover `c.pt` and are
  affine.

Conclusion: there are a stage `i`, a line bundle `M` on `D i` and global sections `s j` of `M`
whose trivialization loci cover `D i` and are affine.

The theorem does not assume that `F` is a line bundle; this follows from the hypotheses but is
not needed.

Proof as implemented.

1. Let `U j` be the locus of `t j`. These opens cover `c.pt` and are affine, so Mathlib's
   `Scheme.exists_isOpenCover_and_isAffine_of_finite` gives a stage `i` and affine opens
   `V j` of `D i` covering `D i` with `U j = c.π.app i ⁻¹ (V j)` exactly.
2. Since `t l` trivializes `F` on `U l`, for every pair `k, l` there is `g k l ∈ Γ(c.pt, U l)`
   with `t k|_{U l} = g k l • t l|_{U l}` (`trivializesOn_iff_bijective`).
3. For each pair `(k, l)`, consider the property of an object `S = (j, f : j ⟶ i)` of
   `Over i` that `g k l` is the image of a section over `D.map f ⁻¹ (V l)`. It holds for some
   `S` by `exists_appLE_eq_of_isAffineOpen'`, and it passes to sources of morphisms of
   `Over i` by composing `appLE` maps (`Scheme.Hom.appLE_comp_appLE`). As `Over i` is
   cofiltered and there are finitely many pairs, `exists_forall_of_isCofiltered` gives one
   stage `S` that works for all pairs.
4. At this stage, with `π = c.π.app S.left` and `V' l = D.map S.hom ⁻¹ (V l)`, the loci of
   `t l` are `π⁻¹ (V' l)`, the opens `V' l` cover `D S.left`, and every transition function
   `g k l` is `π^#(a)` for some `a ∈ Γ(D S.left, V' l)`. The equation required by the descent
   theorem is checked after restriction to `U l = π⁻¹(V' l)` (an injective restriction map,
   `map_injective_of_le_of_le`), using naturality of `sectionHom` (`hom_app_map`).
5. `exists_lineBundle_of_descent` gives a line bundle `M` on `D S.left` with sections `s l`
   whose loci are exactly `V' l`. These cover `D S.left` and are affine as preimages of the
   affine opens `V l` under the affine morphism `D.map S.hom`.
