# The Galois twist on ground-field homomorphisms and on torus characters

Helper module for the proof of `GaloisBorelTwistingStatement` (Task 5268). It contains no
literature statement. Its results are internal steps of Springer's Galois-twisting argument
(Springer 1994, §3.5): the Galois action on adelic points commutes with homomorphisms defined
over `F`, and preserves norms of characters once the characters are also moved by Galois.

Throughout, `L/F` is a finite extension of number fields, `σ : L ≃ₐ[F] L`, and `galoisTwist`
is the Galois twist on the upper-field adelic points of a base-changed `F`-group (module
`AdelicGaloisTwistMap`; its descent formula is in `AdelicGaloisTwistDescent`). For an `F`-group `T₀`, `T₀_L` is
`(CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀`.

## Naturality

- `galoisTwist_comp_baseChange`: let `f : H ⟶ G` be a homomorphism of `F`-groups and `t` an
  adelic point of `H_L`. Then `galoisTwist_G σ (t ≫ f_L) = galoisTwist_H σ t ≫ f_L`.
  Proof: both sides have the same canonical descent. This uses `descentPoint_injective`,
  `descentPoint_galoisTwist` and `descentPoint_comp_baseChange`.

## Characters of a base-changed commutative group

- `characterValue_val`: the value of a character on an adelic point, read through the points
  of `𝔾_m` and the global sections of `Spec 𝔸_L` (by `rfl`).
- `galoisTwistComm` / `galoisTwistLie`: the same map `galoisTwist F L T₀.toGrp σ`, with the
  point type written in the commutative-group-scheme form `adeleTest L ⟶ T₀_L.X` and in the
  affine-point form `Lie.AffinePoints T₀_L.toGrp (Adeles L)`. These wrappers are needed because
  Lean's kernel times out when a point of one of these equal types is passed to a lemma stated
  for another.
- `descentPoint_galoisTwistComm`: the descended point of `galoisTwistComm σ t` is `t`
  restricted along `Spec σ̃`, where `σ̃ = AdeleGalois.ringEquiv F L σ` is the adele automorphism.
- `pointsEquiv_galoisTwist_character`: on `𝔾_m`-points, `σ χ` at the twisted point is `χ` at `t`
  followed by `σ̃` on global sections (`galoisRepresentation_points`, `Gm.pointsEquiv_naturality`).
- `ΓSpecIso_adeleTestIso`: on global sections of `Spec 𝔸_L`, `Spec σ̃` acts by `σ̃`
  (`Scheme.ΓSpecIso_naturality`).
- `characterValue_galoisTwist`: `(σ χ)(galoisTwistComm σ t) = σ̃ (χ t)` as units of `𝔸_L`.
- `characterValue_galoisTwistLie`: the same identity for `galoisTwistLie`, as ideles:
  `(σ χ)(galoisTwistLie σ t) = AdeleGalois.idelesMap σ (χ t)`.
- `full_characterValue_galoisTwistLie`: `|(σ χ)(galoisTwistLie σ t)| = |χ t|` for the
  normalized idele norm `IdeleAbsoluteValue.full L`. This follows from
  `AdeleGalois.full_idelesMap`.
- `normCharacter_eq_full`: `PositiveRealTorus.normCharacter_apply` restated for `T₀_L`.
- `normCharacter_galoisTwist`: `normCharacter L T₀_L (σ χ) (galoisTwistLie σ t) =
  normCharacter L T₀_L χ t`.

Every character value that enters an idele norm is stated as an element of `Ideles L`. Without
that, Lean's elaborator writes the coefficient ring as `Adeles L` in some places and as the
unfolded `NumberField.AdeleRing` in others, and the kernel times out comparing chains of the two
forms.
