# Maps and limits of scheme quotients of étale equivalence relations

Module `Langlands.AlgebraicGeometry.EtaleEquivalenceRelationSchemeQuotientMap`. It imports the
Library modules `EtaleEquivalenceRelationSchemeQuotient`,
`EtaleEquivalenceRelationInvariantOpenDescent`, `EtaleEquivalenceRelationCartesianAffineQuotientProof`
and `Morphisms.LocallyOfFiniteTypeSourceDescentProof`, and Mathlib's
`AlgebraicGeometry.Sites.Fpqc` and `AlgebraicGeometry.Morphisms.QuasiSeparated`.

This module is the generic bridge ("Module A") between étale presentations and their scheme
quotients. It serves the first-level step of absolute Noetherian approximation (FL task
8d02331e, Workers 706 and 416) and through it this task (Tag 07VS). The FL task builds a
cofiltered diagram of étale equivalence relations with cartesian transition morphisms. This
module turns such a diagram into a diagram of quotient schemes, shows that the induced maps
of quotients are affine, and shows that the quotient of the limit relation is the limit of
the quotients.

## Conventions

All schemes live in one universe `u`. `EtaleEquivalenceRelation.{u}` is the Library structure
with `t s : R ⟶ U`. `F.SchemeQuotient` is the Library structure with fields `M`, `q : F.U ⟶ M`,
`isPullback : IsPullback F.t F.s q q`, and instances `Etale q` and `Surjective q`.
`IsCartesianHom E' E f g` (Library) says that `f : E'.U ⟶ E.U` and `g : E'.R ⟶ E.R` commute
with `t` and that the `s`-square `E'.R → E.R`, `E'.U → E.U` is a pullback. The category of
étale equivalence relations (Library `EtaleEquivalenceRelationCartesianDiagram`) has the
cartesian morphisms as arrows, with `objMap`, `relMap` and `isCartesian`, and the functors
`objectFunctor` and `relationFunctor`.

## Statements

General lemmas in namespace `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`:

- `isPullback_of_exists_local w hom_ext exists_local`: a commutative square
  `fst ≫ f = snd ≫ g` of schemes is a pullback if two morphisms into `P` that agree after `fst`
  and after `snd` are equal, and every pair `a : T ⟶ X`, `b : T ⟶ Y` with `a ≫ f = b ≫ g` has
  a lift `d : T₁ ⟶ P` after precomposition with some effective epimorphism `e : T₁ ⟶ T`.
- `exists_iso_of_isPullback h h'`: if `q : X ⟶ Y` and `q' : X ⟶ Y'` are effective
  epimorphisms with `IsPullback t s q q` and `IsPullback t s q' q'` for the same `t s : R ⟶ X`,
  then there is an isomorphism `e : Y ≅ Y'` with `q ≫ e.hom = q'`.

In namespace `EtaleEquivalenceRelation.SchemeQuotient`, for `Q : F.SchemeQuotient`:

- `w : F.t ≫ Q.q = F.s ≫ Q.q` (with a `reassoc` form), and an `EffectiveEpi Q.q` instance.
- `comp_eq_of_comp_q_eq hg a b h`: if `g : F.U ⟶ W` satisfies `F.t ≫ g = F.s ≫ g` and
  `a ≫ Q.q = b ≫ Q.q`, then `a ≫ g = b ≫ g`.
- `desc g hg : Q.M ⟶ W` for such `g`, with `fac : Q.q ≫ Q.desc g hg = g`, and
  `hom_ext : Q.q ≫ a = Q.q ≫ b → a = b`.
- `isInvariantOpen_preimage V : F.IsInvariantOpen (Q.q ⁻¹ᵁ V)` for every open `V` of `Q.M`.
- `isPullback_chart_restrict V`: the chart relation `F.chart (Q.q ⁻¹ᵁ V).ι` has kernel-pair
  square `IsPullback (Chart.t …) (Chart.s …) (Q.q ∣_ V) (Q.q ∣_ V)`.
- `hasAffineQuotient_chart V hV`: if `V` is an affine open of `Q.M`, then
  `(F.chart (Q.q ⁻¹ᵁ V).ι).HasAffineQuotient`, with quotient `V` and map `Q.q ∣_ V`.
- `isAffineOpen_of_hasAffineQuotient_chart W h`: conversely, if the chart relation on
  `Q.q ⁻¹ᵁ W` has an affine quotient, then `W` is an affine open of `Q.M`.
- `preimage_image_eq hV`: for an invariant open `V` of `F.U`, `Q.q ⁻¹' (Q.q '' V) = V`.
- `isAffineHom_q_of_invariantOpenCover V hV hinv haff hq`: if `V : K → F.U.Opens` has
  `iSup V = ⊤`, each `V k` is invariant and affine, and each chart relation on `V k` has an
  affine quotient, then `IsAffineHom Q.q`.
- `compactSpace`: `[CompactSpace F.U] → CompactSpace Q.M`.
- `locallyOfFiniteType_terminal`: `[LocallyOfFiniteType (terminal.from F.U)] →
  LocallyOfFiniteType (terminal.from Q.M)`.
- `quasiSeparatedSpace`: `[IsAffineHom Q.q] → [QuasiSeparatedSpace F.U] →
  QuasiSeparatedSpace Q.M`.

For a cartesian morphism `h : IsCartesianHom E' E f g` and quotients `Q' : E'.SchemeQuotient`,
`Q : E.SchemeQuotient`:

- `unit_comp h : E'.unit ≫ g = f ≫ E.unit` and `comp_q_w h Q : E'.t ≫ f ≫ Q.q = E'.s ≫ f ≫ Q.q`.
- `map h Q' Q : Q'.M ⟶ Q.M`, defined as `Q'.desc (f ≫ Q.q) _`, with
  `q_map : Q'.q ≫ map h Q' Q = f ≫ Q.q`.
- `isPullback_map h Q' Q : IsPullback f Q'.q Q.q (map h Q' Q)`: the square of the cartesian
  morphism, the two quotient maps and the induced map is cartesian.
- `map_id Q : map (isCartesianHom_id E) Q Q = 𝟙 Q.M` and
  `map_comp h₁ h₂ Q₁ Q₂ Q₃ : map (h₁.comp h₂) Q₁ Q₃ = map h₁ Q₁ Q₂ ≫ map h₂ Q₂ Q₃`.
- `isAffineHom_q h Q' Q`: `[IsAffineHom Q.q] → IsAffineHom Q'.q`.
- `isAffineHom_map h Q' Q`: `[IsAffineHom f] → [IsAffineHom Q.q] → IsAffineHom (map h Q' Q)`.
- `nonempty_of_isCartesianHom h Q`: `[IsAffineHom f] → [IsAffineHom Q.q] →
  Nonempty E'.SchemeQuotient`; `ofIsCartesianHom h Q` is the chosen quotient
  (`Nonempty.some`).

For a diagram `D : I ⥤ EtaleEquivalenceRelation.{u}` with `I : Type u`, `[Category.{u} I]`, and
quotients `Q : ∀ i, (D.obj i).SchemeQuotient`:

- `quotientFunctor D Q : I ⥤ Scheme.{u}` (the selected declaration) sends `i` to `(Q i).M`
  and `a : i ⟶ j` to `map (D.map a).isCartesian (Q i) (Q j)`.
- For a cone `c : Cone D` and `Qc : c.pt.SchemeQuotient`, `quotientCone Q c Qc :
  Cone (quotientFunctor D Q)` has point `Qc.M` and legs `map (c.π.app i).isCartesian Qc (Q i)`.
- Assume `[IsCofiltered I]` and `hc : IsLimit (objectFunctor.mapCone c)` (the object schemes
  `(D.obj i).U` have limit `c.pt.U`). Then
  - `quotientCone_hom_ext Q c Qc hc`: two morphisms `x y : T ⟶ Qc.M` that agree after every leg
    of `quotientCone Q c Qc` are equal;
  - `isLimitQuotientCone Q c Qc hc : IsLimit (quotientCone Q c Qc)`.

No affineness of the transition maps is assumed in the limit statements; the relation limit is
obtained from the object limit by the Library lemma `CartesianDiagram.isLimitRelation`.

## Proofs

- `isPullback_of_exists_local`. `IsPullback.mk'` reduces to existence of lifts. A local lift
  `d` is compatible with `e` by `hom_ext`, so it descends along the effective epimorphism `e`
  (`EffectiveEpi.desc`). The two equations are checked after cancelling the epimorphism `e`.
- `exists_iso_of_isPullback`. Each of `q`, `q'` is constant on pairs of points identified by the
  other, through the common kernel pair. Descending each along the other gives inverse
  morphisms; the inverse equations are checked after cancelling `q` and `q'`.
- `desc`, `fac`, `hom_ext`. `Q.q` is étale and surjective, hence flat, locally of finite
  presentation and surjective, so Mathlib's instance makes it an effective epimorphism.
  Compatibility of `g` comes from lifting a pair with equal images in `Q.M` to `F.R` through
  `Q.isPullback`.
- `isInvariantOpen_preimage`. `F.s ⁻¹ᵁ (Q.q ⁻¹ᵁ V)` and `F.t ⁻¹ᵁ (Q.q ⁻¹ᵁ V)` are preimages
  along `F.s ≫ Q.q = F.t ≫ Q.q`.
- `isPullback_chart_restrict`. The square commutes after composing with the monomorphism
  `V.ι`. Uniqueness is `Chart.hom_ext`. A pair of points of `Q.q ⁻¹ᵁ V` with equal image in `V`
  lifts to `F.R` by `Q.isPullback` and then into the chart by `Chart.lift`.
- `hasAffineQuotient_chart`. `Q.q ∣_ V` is a base change of `Q.q`
  (`isPullback_morphismRestrict`), so it is flat, locally of finite presentation and
  surjective; with the previous square it is an affine quotient.
- `isAffineOpen_of_hasAffineQuotient_chart`. Both `Q.q ∣_ W` and the given affine quotient map
  are effective epimorphisms with the chart relation as kernel pair, so
  `exists_iso_of_isPullback` gives an isomorphism of `W` with the affine quotient scheme.
- `preimage_image_eq`. A point `x` with `Q.q x = Q.q y`, `y ∈ V`, comes from a point `z` of
  `pullback Q.q Q.q` (`Scheme.Pullback.exists_preimage_pullback`). Its image `r` in `F.R` has
  `F.t r = x` and `F.s r = y`. Invariance `F.s ⁻¹ᵁ V = F.t ⁻¹ᵁ V` gives `x ∈ V`.
- `isAffineHom_q_of_invariantOpenCover`. Use `isAffineHom_of_forall_exists_isAffineOpen`. For
  a point `Q.q x` with `x ∈ V k`, the image `W` of `V k` is open (`Q.q` is étale, hence open)
  and `Q.q ⁻¹ᵁ W = V k` by `preimage_image_eq`. So `W` is affine by the previous lemma, and its
  preimage `V k` is affine.
- `compactSpace` is the continuous surjective image. `locallyOfFiniteType_terminal` is the
  Library source descent `locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp`
  along `Q.q`. `quasiSeparatedSpace` uses `quasiSeparatedSpace_iff_forall_affineOpens`: the
  preimages of two affine opens are affine, their intersection is compact in the
  quasi-separated `F.U`, and its image under the surjection `Q.q` is the intersection of the
  two opens.
- `map`, `q_map`, `map_id`, `map_comp` follow from `desc`, `fac` and `hom_ext`. `unit_comp`
  and `comp_q_w` are checked with `E.hom_ext` and the two squares of `h`.
- `isPullback_map` uses `isPullback_of_exists_local`.
  - Uniqueness: let `l, l' : T ⟶ E'.U` have the same composite with `f` and with `Q'.q`. The
    second equation gives `r := Q'.isPullback.lift l l'` in `E'.R`. Then `r ≫ g` and
    `l' ≫ E'.unit ≫ g` have the same endpoints, so they are equal (`E.hom_ext`). With
    `r ≫ E'.s = l'`, the pullback property of the `s`-square gives `r = l' ≫ E'.unit`, and so
    `l = r ≫ E'.t = l'`.
  - Local existence: for `a : T ⟶ E.U`, `b : T ⟶ Q'.M` with `a ≫ Q.q = b ≫ map h Q' Q`, take
    the effective epimorphism `e := pullback.fst b Q'.q` (a base change of `Q'.q`) and
    `c := pullback.snd b Q'.q`. The pair `(e ≫ a, c ≫ f)` lifts to `E.R` through
    `Q.isPullback`. Its `s`-endpoint is `c ≫ f`, so it lifts along the `s`-square to `r'` in
    `E'.R` with `r' ≫ E'.s = c`. Then `d := r' ≫ E'.t` satisfies `d ≫ f = e ≫ a` and
    `d ≫ Q'.q = c ≫ Q'.q = e ≫ b`.
- `isAffineHom_q`: `Q'.q` is a base change of `Q.q` by `isPullback_map`.
- `isAffineHom_map`. For an affine open `V` of `Q.M`, the preimage of
  `(map h Q' Q) ⁻¹ᵁ V` under `Q'.q` is `f ⁻¹ᵁ (Q.q ⁻¹ᵁ V)`. The restriction of `h` to the
  invariant open `Q.q ⁻¹ᵁ V` is cartesian (Library `isCartesianHom_invariantOpenMap`), so the
  published `etaleEquivalenceRelationCartesianAffineQuotient` gives the chart relation on
  `f ⁻¹ᵁ (Q.q ⁻¹ᵁ V)` an affine quotient. Both object schemes are affine because `f` and
  `Q.q` are affine. `isAffineOpen_of_hasAffineQuotient_chart` concludes.
- `nonempty_of_isCartesianHom` applies the Library `nonempty_schemeQuotient_of_invariantOpenCover`
  to the family `f ⁻¹ᵁ (Q.q ⁻¹ᵁ V)` over the affine opens `V` of `Q.M`. These opens are
  invariant (Library `IsCartesianHom.isInvariantOpen_preimage`) and cover `E'.U`. Their chart
  relations have affine quotients as in the previous item.
- `quotientFunctor` and `quotientCone` are well defined by `map_id`, `map_comp`, `q_map` and
  `hom_ext`.
- `quotientCone_hom_ext`. Take the effective epimorphism `e` from the iterated pullback of
  `Qc.q` along `x` and along `y`, with lifts `u, v` to `c.pt.U` such that `u ≫ Qc.q = e ≫ x` and
  `v ≫ Qc.q = e ≫ y`. For every `i`, the images of `u` and `v` in `(D.obj i).U` have equal
  images in `(Q i).M`. So they come from `r i` in `(D.obj i).R`. The `r i` form a cone over
  `D ⋙ relationFunctor` (checked with `(D.obj j).hom_ext`). The relation limit
  `CartesianDiagram.isLimitRelation D c hc` gives `ρ` in `c.pt.R` with endpoints `u` and `v`
  (checked against the object limit `hc`). Hence `e ≫ x = e ≫ y` by `Qc.w`, and `e` is an
  epimorphism.
- `isLimitQuotientCone` uses `IsLimit.ofExistsUnique`. Given a cone `S`, choose `j₀ : I`
  (`IsCofiltered.nonempty`) and let `e : pullback (S.π.app j₀) (Q j₀).q ⟶ S.pt` be the first
  projection, an effective epimorphism. For each `k : Over j₀`, the cartesian square
  `isPullback_map` of `D.map k.hom` lifts the second projection to `b k : _ ⟶ (D.obj k).U` with
  `b k ≫ (Q k).q = e ≫ S.π.app k`. These form a cone over the diagram above `j₀`. The Library
  lemma `CartesianDiagram.isLimitObjectAbove` gives `β : _ ⟶ c.pt.U` with
  `β ≫ (c.π.app k).objMap = b k`. For arbitrary `i`, comparing through `IsCofiltered.min i j₀`
  shows `(β ≫ Qc.q) ≫ map _ Qc (Q i) = e ≫ S.π.app i`. Two morphisms equalized by `e` give
  the same `β ≫ Qc.q` by `quotientCone_hom_ext`, so `β ≫ Qc.q` descends along `e`. The
  descended morphism is the lift. Factorization and uniqueness are checked after cancelling `e`
  and with `quotientCone_hom_ext`.

## Provenance and relation to the literature

Provenance: derived. The limit statement is the scheme-quotient form of Stacks, Limits of
Algebraic Spaces, Lemma 70.4.1 (Tag 07SF): a limit of algebraic spaces along affine transition
maps exists and is computed on étale presentations `U = lim U_i`, `R = lim R_i`, with
`U/R → lim X_i` an isomorphism. The proof of `isLimitQuotientCone` follows the proof of that
lemma. Surjectivity there (a morphism `Z → lim X_i` lifts étale locally to `U`) is the
construction of `β` on the cover `e`. Injectivity there (two lifts with the same images in
all `X_i` give compatible points `c_i` of `R_i`, hence a point of `R = lim R_i`) is
`quotientCone_hom_ext`. Stacks applies Lemma 70.4.1 with affine transition maps; the FL task
supplies them through `isAffineHom_map`. Proposition 70.8.1 (Tag 07SU), absolute Noetherian
approximation, writes a space as such a limit `X = lim X_i` with affine transition maps. In
the FL task the levels are given by étale presentations, and `isLimitQuotientCone` identifies
the quotient of the limit presentation with the limit of the level quotients.

The other statements are standard facts on quotients by fppf equivalence relations, proved here
for the Library structure `SchemeQuotient`: maps of quotients induced by cartesian morphisms,
the cartesian square of quotients, and affine opens of a quotient characterized by affine
quotients of chart relations. In Stacks they appear as the statement that a morphism of
algebraic spaces `X' → X` with `U' = X' ×_X U` and `R' = X' ×_X R` makes the square
`U' → U`, `X' → X` cartesian; this is the definition of `U_i` in the proof of Lemma 70.4.1.
The packaging (the structure-level `map`, the open-cover criterion
`isAffineHom_q_of_invariantOpenCover`, the conditional constructions `ofIsCartesianHom` and
`quotientFunctor`) is internal and follows the interface agreed with the FL task.
