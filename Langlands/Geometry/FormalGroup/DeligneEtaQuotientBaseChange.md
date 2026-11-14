# Actual eta stalk and Pi quotient comparisons under base change

Drinfeld, *Coverings of p-adic symmetric regions*, §2 A, printed p.110
(PDF p.4), condition (b), uses the map from the **total** integral quotient
`eta_s / Pi eta_s` to `(T_s / Pi T_s) ⊗ κ_s`. This module constructs the
source comparison under arbitrary scheme base change. Its provenance is derived:
it proves compatibility of the already constructed inverse-image lattice,
actual stalks and actual Pi operators. It does not claim the residue-fibre
comparison or preservation of injectivity in condition (b).

The source is registered as
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The constructions here are internal infrastructure for that condition, rather
than an assertion of Proposition 2.4 or representability.

For the three preliminary naturality lemmas, `O` is an arbitrary commutative
ring, `X` and `Y` are topological spaces in universe `u`, and `f : X ⟶ Y`
is any continuous map. The coefficients and spaces have the same universe.

- `moduleStalkPushforward_naturality` proves naturality of the actual
  presheaf stalk-pushforward map. The proof tests the equality on every germ;
  the two germ formulas give identical maps on sections.
- `moduleStalkPullback_naturality` proves naturality of Mathlib's actual
  presheaf inverse-image stalk isomorphism. Its forward map is the stalk
  of the presheaf adjunction unit followed by the stalk-pushforward map.
  Naturality of that unit and the preceding lemma prove the square.
- `inverseImageStalkIso_naturality` proves naturality of the existing
  `inverseImageStalkIso` from `DeligneLatticeBaseChange`. The proof follows
  its three factors: the presheaf stalk isomorphism, the stalk of the
  sheafification unit, and the inverse of the comparison between sheaf
  pullback and sheafification of presheaf pullback. It uses naturality of
  the sheafification unit and of the last comparison. Thus the equality
  concerns the previously defined isomorphism itself.

Now let `d` be a positive natural number, `pi : O`, `F` an `O`-algebra field,
`S` and `S'` arbitrary schemes in universe `u`,
`φ : O →+* Γ(S, ⊤)`, `D : SheafPreDatum d pi F φ`, and `f : S' ⟶ S`.
No additional flatness assumption on `f`, nilpotence assumption on `pi`,
or admissibility assumption on `D` is imposed. The lattice flatness,
grading, rational frame and local generation already belong to the existing
preliminary datum; no new choice is supplied.

For every `x : S'`, `SheafPreDatum.etaStalkPullbackIso` is an isomorphism
of `O`-modules

`D.etaStalk (f x) ≅ (D.pullback f).etaStalk x`.

Both sides are exactly the actual total stalks defined in
`DeligneAdmissibility`. The isomorphism first identifies the original
stalk with the stalk of the ordinary inverse image of the total lattice
with scalars restricted to `O`. It then takes the stalk of
`inverseImageLatticeScalarIso`, which compares that inverse image with
scalar restriction of the inverse image of the Pi-algebra lattice. The
latter is exactly the lattice used by the constructed `D.pullback f`.

`etaStalkPullbackIso_pi` shows that this isomorphism carries the original
actual Pi action to the pulled actual Pi action. Apply the naturality
lemma to total Pi multiplication, then take the stalk of the proved
`inverseImageLatticeScalarIso_pi` square. Evaluating the composed equality
of module morphisms proves the formula on each stalk element.

`etaStalkPullbackIso_range` identifies the image of the original Pi range
under this linear equivalence with the actual pulled Pi range. The
forward containment follows from the Pi square. For the reverse
containment, lift an arbitrary preimage of the pulled Pi operator through
the stalk isomorphism, then use the same square.

`etaPiQuotientPullbackEquiv` is consequently the `O`-linear equivalence

`D.etaPiQuotient (f x) ≃ₗ[O] (D.pullback f).etaPiQuotient x`.

It is induced by `etaStalkPullbackIso` using the established equality of
ranges. `etaPiQuotientPullbackEquiv_mk` computes it on every actual quotient
representative: the class of `e` maps to the class of the compared stalk
element. This formula is definitional for the quotient construction.

The tangent quotient residue fibre, the square with the actual map induced
by `u`, and injectivity after base change remain separate obligations.
This module does not construct the full admissible Nilp functor, its
projective-linear action, a representing object or a universal object.
