# Containment of closed subschemes detected on geometric points

Module `Langlands.GroupScheme.SplitExistence.ExtPoints`, namespace
`Langlands.GroupScheme.SplitExistence`. Internal helper of the proof of the split reductive
Existence Theorem (task 2132924b). It extends the Library's
`SubgroupFunctor.range_le_of_algClosed_points`, which is stated over an algebraically closed
base field, to an arbitrary field `k` with points in an algebraically closed extension `K`.
This is the Nullstellensatz argument: a reduced scheme of finite type is determined by its
closed points, and each closed point has a residue field finite over `k`.

Throughout, `K` is an algebraically closed field with a `k`-algebra structure, and
`extPoint K` is the test object `Spec K → Spec k` from `RationalProducts`.

## Declarations

- `exists_extPoint_apply K x hx`: for `X` locally of finite type over `k` and a closed point
  `x`, some `K`-valued point `q : extPoint K ⟶ X` maps the point of `Spec K` to `x`. Proof:
  `Spec κ(x) → X` is a closed immersion (`isClosed_singleton_iff_isClosedImmersion`), so
  `Spec κ(x) → Spec k` is finite (`isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`). Thus
  `κ(x)` is a finite, hence algebraic, extension of `k`, and `IsAlgClosed.lift` embeds it in
  `K` over `k`. The point is `Spec K → Spec κ(x) → X`.
- `exists_factor_of_extPoints K f g h`: let `f : X ⟶ Y` be a morphism over `Spec k` with `X`
  reduced and locally of finite type, and `g : Z ⟶ Y` a closed immersion. Assume every
  `K`-valued point of `X` composed with `f` factors through `g`. Then `f` factors through
  `g`. The proof is the Library argument: the projection `X ×_Y Z → X` is a closed immersion
  whose image contains every closed point, by the previous lemma. Closed points are dense
  (Jacobson), so the projection is surjective, and since `X` is reduced it is an isomorphism.
- `range_le_of_extPoints K hj h`: for homomorphisms `i : H ⟶ G` with `H` reduced and locally
  of finite type, and `j : B ⟶ G` a closed subgroup, if every `K`-valued point of `H` maps
  into the image of `j`, then `range i ≤ range j` as subgroup functors on every test scheme.
- `ext_of_extPoints K f g h`: two morphisms `f g : X ⟶ Y` over `Spec k` agree if they agree on
  all `K`-valued points. Here `X` is reduced and locally of finite type, and `Y` is separated
  over `k`. Every closed point of `X` lifts to the scheme-theoretic equalizer of `f` and `g`,
  by `exists_extPoint_apply`. Closed points are dense, so the equalizer is dominant. Mathlib's
  `ext_of_isDominant_of_isSeparated` concludes.
