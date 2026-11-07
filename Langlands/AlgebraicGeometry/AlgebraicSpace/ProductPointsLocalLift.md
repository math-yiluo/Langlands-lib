# Lifting points of an algebraic space to an étale chart over a finite free extension

Author: Worker 105.

Helper module for the proof of Conrad's Proposition 5.2,
`Langlands.Global.AdelicSpaceLevelPointsStatement`. It contains no statement from the
literature. It is the local step of Conrad's proof (printed pp.13–14): the fibres of an affine
étale chart have bounded degree `N`, and after an unramified extension of degree dividing `N!`
an integral point lifts to the chart by Hensel's lemma. The implemented construction
proves the finite free basis and henselianity needed for this lift. It then takes a finite
product to make the rank constant, and makes no étaleness or cyclic-torsor assertion.

Throughout, `X` is an algebraic space over `Spec C` and `a : h_U → X` is étale, with `U` over
`Spec C`.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsLocalLift`.

- `exists_point_of_field_point`: let `O` be a henselian local `C`-algebra and `O → K` a
  surjection onto a field. If `x ∈ X(O)` and a `K`-point of `U` maps to the image of `x`, then
  `x` is the image of an `O`-point of `U`. The `K`-point and `Spec K → Spec O` define a point of
  the étale `O`-scheme `U ×_X Spec O`. The Library's
  `HenselianSections.exists_section_of_smooth_of_surjective` gives a section through it. This
  is the `C`-relative form of the residue-field lifting in the Cor 5.7 compactness proof.
- `exists_fibre_point`: if `X` is quasi-separated, `a` is étale and surjective and `U` is
  affine, there is `D` such that every field point `x̄ ∈ X(κ)` lifts to `U` over a finite
  separable extension `L` of `κ` with `[L : κ] ≤ D`. The fibre `U ×_X Spec κ` is a nonempty
  étale `κ`-scheme. It has a point over a finite separable `L`, given by a monomorphism
  (the Library's `FieldPointEtaleLift.exists_separable_point_mono`). The `[L : κ]` embeddings of
  `L` into an algebraic closure give that many distinct points of `U` with the same image in
  `X` (`AlgHom.natCard_of_splits`). These are bounded by `D`, from the fibre bound
  `EtaleChartFibreCount.exists_fibre_card_le`.
- `exists_unramified`: let `O` be complete local with residue field `κ`, and `L` finite
  separable over `κ`. There is a henselian local `O`-algebra `E`, free of rank `[L : κ]`, with
  a surjection `ρ : E → L` compatible with `O → κ → L`. Take a primitive element `α` of `L/κ`
  (`Field.exists_primitive_element`) and a monic lift `m` of its minimal polynomial
  (`Polynomial.lifts_and_natDegree_eq_and_monic`). Then `E = O[X]/(m)`
  (`UnramifiedHensel`), and `ρ` sends `X` to `α`. `ρ` is onto since `L = κ[α]`.
- `uliftYonedaEquiv_symm_changeRing`: change of coefficients of a point on the Yoneda side.
- `exists_local_lift`: if `X` is quasi-separated, `a` étale and surjective and `U` affine, there
  is `d > 0` with the following property. For every complete local `C`-algebra `O` and
  `x ∈ X(O)` there are a finite free `O`-algebra `O'` with a basis indexed by `Fin d` and an
  `O'`-point of `U` mapping to the image of `x` in `X(O')`. Take `d = D!`. Apply
  `exists_fibre_point` to the residue point of `x`, then `exists_unramified`, then
  `exists_point_of_field_point` over `E`. Finally use `O' = Fin k → E` with `k = D!/[L : κ]`,
  whose basis is the tower basis of `E` over `O` and `Fin k → E` over `E`.
