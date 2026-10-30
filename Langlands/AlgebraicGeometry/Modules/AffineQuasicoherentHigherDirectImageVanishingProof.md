# Higher direct images of quasi-coherent modules along an affine morphism vanish: proof

Author: Worker 727.

This module proves the published proposition
`Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingStatement.{u}`
from `Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingStatement`,
which it imports unchanged.

## Main result

`Langlands.AlgebraicGeometry.Modules.affineQuasicoherentHigherDirectImageVanishing` is the
theorem

```lean
theorem affineQuasicoherentHigherDirectImageVanishing :
    AffineQuasicoherentHigherDirectImageVanishingStatement.{u}
```

for an arbitrary universe `u`. Unfolded, it says: for all schemes `X S : Scheme.{u}`, every
morphism `f : X ⟶ S` with `IsAffineHom f`, every `M : X.Modules` with `M.IsQuasicoherent` and
every `q : ℕ`, `IsZero ((DerivedSections.higherDirectImage f (q + 1)).obj M)`. Here
`higherDirectImage f m` is `(Scheme.Modules.pushforward f).rightDerived m`.

The theorem uses no hypothesis beyond the statement's. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Modules used

The proof uses three new helper modules, each with its own Markdown:

- `Langlands.Cohomology.CechCochains`: the ordered Čech complex `Cech.C`, `Cech.d` of an
  abelian presheaf for a family of opens, the exactness predicate `Cech.ExactAt` (every
  `(p + 1)`-cocycle is a coboundary), and the long-exact-sequence step
  `Cech.exactAt_of_shortExact`.
- `Langlands.Cohomology.CechFlasque`: `Cech.exactAt_of_isFlasque`, Čech exactness of a flasque
  abelian sheaf for any finite family of opens.
- `Langlands.AlgebraicGeometry.Modules.AffineVanishing.QuasicoherentCech`: the family
  `cover g = fun i => X.basicOpen (g i)` for `g : ι → Γ(X, W)`, and `exactAt_cover`: for a
  quasi-coherent `M`, an affine open `W`, finite `ι` and `g` generating the unit ideal,
  `Cech.ExactAt M.presheaf (cover g) p` for every `p`.

From the Library it uses `PushforwardInjectiveAcyclic.toAbSheaf`, `isFlasque_of_injective`,
`injectiveSc` and `injectiveSc_shortExact` (module
`Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof`),
`ClosedImmersionHigherDirectImageVanishing.epi_of_isLocallySurjective`, and
`Langlands.Cohomology.DerivedPlus.rightDerivedδ`, `epi_rightDerivedδ_of_isZero`,
`rightDerived_map_comp_δ`.

## Route of the proof

The proof follows Stacks: Lemma 01EW (`lemma-cech-vanish-basis`) with the standard open
coverings of affine opens, as in the proof of Lemma 01XB, and then Lemma 01XC. Stacks deduces
01XC from the description of `R^i f_*` as a sheafification (Lemma 01E4) and from vanishing
of `H^i(f⁻¹ V, F)`. The Lean proof instead runs the dimension shift of 01EW directly for the
functor `f_*`, so 01E4 and the cohomology of open subschemes are not needed.

1. **The class.** `IsCechAcyclic G` says: for every affine open `W` of `X`, every finite
   `ι : Type u` and every `g : ι → Γ(X, W)` generating the unit ideal, the ordered Čech complex
   of `G` for `cover g` is exact in every positive degree. Quasi-coherent modules are in this
   class (`isCechAcyclic_of_isQuasicoherent`, from `exactAt_cover`; Stacks 01X9).
2. **Sections over affine opens** (`surjective_app_of_exactAt`, Stacks 01EU). Let
   `0 ⟶ F ⟶ G ⟶ H ⟶ 0` be a short exact sequence of abelian sheaves on `X`, and `V` an affine
   open such that the degree-`1` Čech complex of `F` is exact for every standard covering of
   `V`. Then `G(V) ⟶ H(V)` is surjective. Take `s ∈ H(V)`. The map `G ⟶ H` is locally
   surjective (Mathlib's `TopCat.Sheaf.isLocallySurjective_iff_epi`), and basic opens of `V`
   form a basis of `V`. So the set of `h ∈ Γ(X, V)` such that `s` lifts on `D(h)` generates
   the unit ideal (`IsAffineOpen.iSup_basicOpen_eq_self_iff`), and finitely many of them do
   too (`Ideal.span_eq_top_iff_finite`). Choose lifts `t i` on `D(g i)`. Their Čech
   differential maps to zero in `H`, so it comes from a `1`-cocycle of `F`, which is a
   coboundary `d a`. Then `t - a` is a Čech `0`-cocycle of `G` lifting `s`. Its components
   agree on overlaps (`res_eq_res_of_d_zero_eq_zero`), so they glue to a section of `G` over
   `V` (Mathlib's `existsUnique_gluing'`), and the glued section maps to `s` because the two
   agree locally (`eq_of_locally_eq'`).
3. **Passing to the cokernel** (`isCechAcyclic_X₃`, the first half of the proof of Stacks
   01EW). Let `0 ⟶ G ⟶ I ⟶ Q ⟶ 0` be short exact in `X.Modules` with `I` injective and `G`
   in the class. Apply the exact forgetful functor `toAbSheaf X`. The sheaf `I` is flasque
   (`isFlasque_of_injective`), so its Čech complexes are exact (`Cech.exactAt_of_isFlasque`;
   Stacks 01EP for injective modules). Every finite intersection of members of `cover g` is
   affine (`isAffineOpen_inter`), so by step 2 the sequence is exact on sections over each of
   them. The long-exact-sequence step `Cech.exactAt_of_shortExact` then shows that `Q` is in
   the class.
4. **The pushforward is exact on such sequences** (`epi_pushforward_map`). For an affine
   morphism `f` and a short exact sequence `0 ⟶ G ⟶ I ⟶ Q ⟶ 0` in `X.Modules` with `G` in
   the class, `f_* I ⟶ f_* Q` is an epimorphism. It suffices to show local surjectivity
   (Library `epi_of_isLocallySurjective`). For a section `t` of `f_* Q` over `V` and a point
   `y ∈ V`, choose an affine open `V'` with `y ∈ V' ⊆ V` (`Y.isBasis_affineOpens`). Then
   `f ⁻¹ᵁ V'` is affine (`IsAffineOpen.preimage`, from `IsAffineHom f`), and step 2 lifts the
   restriction of `t` to `V'`.
5. **Dimension shift** (`isZero_higherDirectImage_of_isCechAcyclic`). For `G` in the class,
   `R^{q+1} f_* G = 0`, by induction on `q`. Embed `G` in its chosen injective object `I` with
   cokernel `Q` (`injectiveSc G`). Since `R^{m+1} f_* I = 0`
   (`Functor.isZero_rightDerived_obj_injective_succ`), the connecting morphism
   `rightDerivedδ : R^m f_* Q ⟶ R^{m+1} f_* G` is an epimorphism
   (`epi_rightDerivedδ_of_isZero`).
   - For `q = 0`: `R^0 f_* I ⟶ R^0 f_* Q` is identified with `f_* I ⟶ f_* Q`
     (`Functor.rightDerivedZeroIsoSelf`), an epimorphism by step 4. Its composite with
     `rightDerivedδ` is zero (`rightDerived_map_comp_δ`), so `rightDerivedδ` is a zero
     epimorphism and its target `R^1 f_* G` is zero.
   - For `q + 1`: `Q` is in the class by step 3, so `R^{q+1} f_* Q = 0` by the induction
     hypothesis, and its epimorphic image `R^{q+2} f_* G` is zero.

   The connecting morphism is built from Mathlib's derived category, so the proof locally
   installs `HasDerivedCategory.standard` for `X.Modules` and `Y.Modules`. This choice does not
   occur in the statement, whose `higherDirectImage` uses injective resolutions.
6. **Conclusion.** Steps 1 and 5 give `affineQuasicoherentHigherDirectImageVanishing`.

## Auxiliary results

All helpers are in namespace `Langlands.AlgebraicGeometry.Modules.AffineVanishing`.

- `g_app_f_app`, `injective_f_app`, `exists_f_app_eq`: for a short complex `S` of abelian
  sheaves on a topological space, `g ∘ f = 0` on sections; if `S` is short exact, `f` is
  injective on sections and `ker g = im f` on sections (Mathlib's
  `TopCat.Sheaf.sections_exact_of_left_exact`).
- `res_eq_res_of_d_zero_eq_zero hu i j hi hj`: the components of a Čech `0`-cocycle `u` at
  `i` and `j` agree on every open contained in both `U i` and `U j`.
- `d_zero_res g P s`: the restrictions of one section `s` over `W` to the members of
  `cover g` form a Čech `0`-cocycle.
- `surjective_app_of_exactAt hS hV hG`: step 2.
- `IsCechAcyclic G`, `isCechAcyclic_of_isQuasicoherent M`, `isCechAcyclic_X₃ hS hG`: steps 1
  and 3.
- `epi_pushforward_map f hS hG`: step 4.
- `isZero_higherDirectImage_of_isCechAcyclic f q G hG`: step 5.

## Original source

The Stacks Project at git commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, registered
source `stacks-flasque-affine-vanishing-kunneth-a04446e5` (folder SHA-256
`af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`):

- `coherent.tex`, Lemma 01XC (`lemma-relative-affine-vanishing`, lines 180-199): the target.
  Lean replaces the appeal to Lemma 01E4 by the dimension shift for `f_*` in steps 4-5.
- `coherent.tex`, Lemma 01XB (`lemma-quasi-coherent-affine-cohomology-zero`, lines 145-174):
  its proof chooses the class of standard open coverings of affine opens used in step 1.
- `coherent.tex`, Lemma 01X9 (`lemma-cech-cohomology-quasi-coherent-trivial`, lines 44-135):
  Čech vanishing for quasi-coherent modules (module `QuasicoherentCech`, by a different
  argument; see its Markdown).
- `cohomology.tex`, Lemma 01EW (`lemma-cech-vanish-basis`, lines 1695-1776): the dimension
  shift through the class of Čech-acyclic modules (steps 3 and 5).
- `cohomology.tex`, Lemma 01EU (`lemma-ses-cech-h1`, lines 1592-1628): surjectivity on
  sections from vanishing first Čech cohomology (step 2). Where Stacks picks a covering from
  a cofinal system on whose members `s` lifts, Lean picks a standard covering of the affine
  `V` with this property.
- `cohomology.tex`, Lemma 01EP (`lemma-injective-trivial-cech`, lines 1407-1431) and Lemma
  09SZ (`lemma-flasque-acyclic-cech`, lines 1963-1978): injective, and more generally flasque,
  sheaves have vanishing higher Čech cohomology (module `CechFlasque`).

The statement's Markdown records the errata check for 01XC and the related tags. No comment
changes a statement used here.
