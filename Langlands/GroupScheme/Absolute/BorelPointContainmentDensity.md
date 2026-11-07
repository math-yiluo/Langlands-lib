# Rational points in Borel subgroups from a dense conjugation map

Author: Worker 1095.

This helper module of the proof of `BorelPointContainmentStatement`
(module `Langlands.GroupScheme.Absolute.BorelPointContainmentProof`) proves
Lemma A: if the conjugation map `G × H → G` of a subgroup has dense range and
every rational point of `H` lies in a Borel subgroup of `G`, then every
rational point of `G` does. All declarations are in the namespace
`Langlands.GroupScheme.BorelPointContainment`. The field is `k : Type u`, and
groups are `GroupScheme (Spec (CommRingCat.of k))`. A rational point of an
object `X` of `Over (Spec k)` is a morphism `Over.mk (𝟙 (Spec k)) ⟶ X`.

## Conjugation

- `conjugation j : G.X ⊗ H.X ⟶ G.X` for `j : H ⟶ G` is the morphism
  `(x, h) ↦ x j(h) x⁻¹`. It is defined in the group of morphisms
  `G.X ⊗ H.X ⟶ G.X` as `fst * (snd ≫ j.hom.hom) * fst⁻¹`.
- `lift_conjugation`: for `x : T ⟶ G.X` and `h : T ⟶ H.X`,
  `lift x h ≫ conjugation j = x * (h ≫ j.hom.hom) * x⁻¹`. This follows by
  `simp` from the fact that composition preserves products and inverses
  of morphisms into a group object.

## Rational points and closed points

These three lemmas assume `[IsAlgClosed k]` and that `X.hom` is locally of
finite type. They are thin wrappers around Mathlib's
`Mathlib.AlgebraicGeometry.AlgClosed.Basic`.

- `rationalPoint_ext`: two rational points with the same underlying point
  (the image of the closed point of `Spec k`) are equal. This is
  `ext_of_apply_closedPoint_eq`.
- `exists_rationalPoint_of_isClosed`: every closed point `z` is the
  underlying point of a rational point. This is `pointOfClosedPoint` and
  `pointOfClosedPoint_apply`.
- `isClosed_rationalPoint`: the underlying point of a rational point is
  closed. This is `pointEquivClosedPoint`.
- `comp_left_apply` (no hypotheses): the underlying point of `x ≫ f` is the
  image under `f` of the underlying point of `x`. It holds by `rfl`.

## The fixing locus of an action

Let `a : SchemeAction G Q` be an action of `G` on `Q` over `Spec k`.

- `incidence a` is the set of points of `G.X ⊗ Q` whose image under
  `(g, y) ↦ (g • y, y)`, that is `lift a.hom (snd G.X Q)`, lies in the range
  of the diagonal `lift (𝟙 Q) (𝟙 Q)`.
- `fixingLocus a` is the image of `incidence a` under the first projection.
- `isClosed_incidence`: if `Q.hom` is separated, `incidence a` is closed.
  The diagonal `lift (𝟙 Q) (𝟙 Q)` is definitionally
  `Limits.pullback.diagonal Q.hom`, a closed immersion, so its range is
  closed. The preimage under a continuous map is closed.
- `isClosed_fixingLocus`: if `Q.hom` is proper, `fixingLocus a` is closed.
  The first projection of `G.X ⊗ Q` is `Limits.pullback.fst G.X.hom Q.hom`,
  the base change of the universally closed `Q.hom`, hence a closed map.
- `mem_fixingLocus_of_act_eq`: if a rational point `g` fixes a rational point
  `y`, that is `a.act g y = y`, then the underlying point of `g` lies in
  `fixingLocus a`. The witness is the underlying point of `lift g y`.
- `exists_act_eq_of_mem_fixingLocus`: assume `[IsAlgClosed k]`, `G.X.hom`
  and `Q.hom` locally of finite type, and `Q.hom` separated. If the
  underlying point of a rational point `g` lies in `fixingLocus a`, then `g`
  fixes some rational point of `Q`. Proof: the set
  `Z = incidence a ∩ fst⁻¹ {g}` is closed and nonempty. Since `G.X ⊗ Q` is
  locally of finite type over `k`, it is a Jacobson space
  (`LocallyOfFiniteType.jacobsonSpace`), so `Z` contains a closed point `w`
  (Mathlib's `nonempty_inter_closedPoints`). Let `x` be the rational point
  with underlying point `w`. Then `x ≫ fst = g` by `rationalPoint_ext`. The
  point `y := x ≫ snd` satisfies `a.act g y = y`: by `rationalPoint_ext` it
  suffices to compare underlying points, and both are the two coordinates of
  the image of `w` under `(g, y) ↦ (g • y, y)`, which lies on the diagonal.

## From fixed points of the flag quotient to Borel subgroups

These results assume `[IsAlgClosed k]`. Let `i₀ : B₀ ⟶ G` be a Borel
subgroup, `q : G.X ⟶ Q` a morphism whose fibres are the left cosets of the
range of `i₀` (hypothesis `hfib`: `g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ range i₀`),
and `a` an action of `G` on `Q` with `a.act g (h ≫ q) = (g * h) ≫ q`
(hypothesis `hact`).

- `exists_isBorelSubgroup_of_act_eq`: assume in addition that `q.left` is
  locally of finite type and surjective. If a rational point `g` fixes a
  rational point `y` of `Q`, then `g` lies in a Borel subgroup. Proof: by
  the Library theorem `Langlands.exists_point_lift_of_locallyOfFiniteType_surjective`,
  `y = m ≫ q` for a rational point `m` of `G`. Then `m ≫ q = (g * m) ≫ q`,
  so `m⁻¹ g m = b ≫ i₀` for a rational point `b` of `B₀` by `hfib`. The
  Borel subgroup is `i₀ ≫ (G.innerIso m).hom`, which is Borel by
  `IsBorelSubgroup.comp_iso`, and `b` maps to `m (m⁻¹ g m) m⁻¹ = g`.
- `exists_act_eq_of_isBorelSubgroup`: assume `G` smooth, affine and
  connected. If `i : B ⟶ G` is a Borel subgroup and `b` a rational point of
  `B`, then `b ≫ i` fixes a rational point of `Q`. Proof: by the Library
  theorem `borelConjugacy`, `i ≫ int(g₁) = φ ≫ i₀` for some rational point
  `g₁` and isomorphism `φ : B ≅ B₀`. The point `g₁⁻¹ ≫ q` is fixed, since
  `g₁ (b ≫ i) g₁⁻¹ = b ≫ φ ≫ i₀` lies in the range of `i₀`.

## Lemma A

`exists_isBorelSubgroup_of_denseRange`: let `k` be algebraically closed,
`G` smooth, affine and connected, `H.X.hom` locally of finite type,
`j : H ⟶ G` a homomorphism with `DenseRange (conjugation j).left`, and assume
that for every rational point `h` of `H` there are a Borel subgroup
`i : B ⟶ G` and a rational point `b` of `B` with `b ≫ i = h ≫ j`. Then every
rational point `g` of `G` has this form: there are a Borel subgroup
`i : B ⟶ G` and a rational point `b` of `B` with `b ≫ i.hom.hom = g`.

Proof. The Library theorem `someBorelQuotientProper` gives a Borel subgroup
`i₀ : B₀ ⟶ G` such that every homogeneous quotient of `G` by `B₀` is proper.
The Library theorem `smoothSubgroupQuotientExistence` gives such a quotient
`q : G.X ⟶ Q` (separated and locally of finite type over `k`, with `q.left`
smooth, surjective and quasi-compact, and fibres `hfib`), so `Q.hom` is
proper. `Dynamic.flagQuotientSchemeAction` gives the action `a` of `G` on `Q`
with `hact` (`Dynamic.flagQuotientSchemeAction_act_lift`).

Let `C` be the preimage of `fixingLocus a` under `conjugation j`; it is
closed by `isClosed_fixingLocus`. Every closed point `w` of `G.X ⊗ H.X` lies
in `C`: write `w` as the underlying point of a rational point `z = (x, h)`.
By hypothesis `h ≫ j = b ≫ i` for a Borel subgroup `i`, so
`z ≫ conjugation j = b ≫ (i ≫ int(x))`, a rational point of the Borel subgroup
`i ≫ int(x)`. By `exists_act_eq_of_isBorelSubgroup` it fixes a rational point
of `Q`, so `w ∈ C` by `mem_fixingLocus_of_act_eq`. Since `G.X ⊗ H.X` is a
Jacobson space, its closed points are dense (`closure_closedPoints`), so `C`
is everything. Hence the range of `conjugation j` lies in the closed set
`fixingLocus a`, and density of this range gives `fixingLocus a = univ`.
Finally `exists_act_eq_of_mem_fixingLocus` gives a rational point of `Q`
fixed by `g`, and `exists_isBorelSubgroup_of_act_eq` concludes.

## Provenance

The closedness argument is the one of Milne, *Algebraic Groups* (2022
corrected reprint, registered source `milne-2022-algebraic-groups`),
Lemma 17.32(a), printed p.361–362 (PDF pp.372–373): for `G/H` complete the
union of the conjugates of `H` is closed, via the closed incidence subset of
`G/H × G` and the closed projection to `G`. Milne's subset
`{(ḡ, x) | g⁻¹ x g ∈ H}` is the incidence locus of `(x, ḡ) ↦ x • ḡ` used
here, up to swapping the factors. The density step corresponds to the proof
of Theorem 17.33(b) in the same place. The formal statement of Lemma A
(dense conjugation of an arbitrary subgroup `H` whose points lie in Borel
subgroups) is internal to this proof.

Axioms of the final theorem: `propext`, `Classical.choice`, `Quot.sound`.
