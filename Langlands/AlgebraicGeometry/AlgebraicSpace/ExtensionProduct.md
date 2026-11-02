# Products of presheaves with represented schemes

Internal infrastructure for the proof of
`SeparatedAddCommGroupSheafSchemeRepresentabilityStatement`. Nothing here is taken from a
specific source; the constructions are the standard base change of a presheaf to a scheme
`Λ` over the base.

For a presheaf `F` on schemes over `S` and `Λ : Over S`, `extProd F Λ` is the product
presheaf `F × Y(Λ)` (`FunctorToTypes.prod`), whose `T`-points are pairs `(x, α)` with
`x ∈ F(T)` and `α : T ⟶ Λ`.

- `isPullback_of_elements`: an elementwise criterion for pullback squares of type-valued
  functors, from `IsPullback.of_forall_isPullback_app` and `Types.isPullback_iff`.
- `extProd.mapRight ρ` changes the second factor along `ρ : Λ' ⟶ Λ`. `isPullback_mapRight`
  shows it is the base change of `Y(ρ)` along the second projection. `mapRightIso ε` is the
  induced isomorphism for an isomorphism `ε : Λ' ≅ Λ`. `mapLeft φ` changes
  the first factor and `isPullback_mapLeft` shows it is the base change of `φ`.
- `fstPullbackMap x` and `isPullback_fst`: the pullback of the projection `fst` along the
  section `x ∈ F(T)` is represented by the scheme product `T ⨯ Λ`. Hence `relative_fst`:
  any base-change-stable property of `Λ ⟶ S` holds relatively for `fst`. Also included:
  `prod_fst_left` (the same property for `(T ⨯ Λ ⟶ T).left`) and `prod_left_hom_ext`.
- `yonedaProdIso U : Y(U ⨯ Λ) ≅ Y(U) × Y(Λ)`.
- `extProd.isSheaf`: the product of an fppf sheaf with `Y(Λ)` is an fppf sheaf
  (`Sheaf.tensorProd_isSheaf`).
- Diagonals:
  - `diagPair X` is the elementwise diagonal and `isClosedImmersion_diag_iff` compares it
    with `Limits.diag`.
  - `isClosedImmersion_diag_of_iso`: closedness of the diagonal is invariant under
    isomorphism of presheaves.
  - `isClosedImmersion_schemeYoneda_map` and `isClosedImmersion_diag_schemeYoneda`: a
    separated `Λ` has closed diagonal.
  - `extProd.isClosedImmersion_diag`: if `F` has closed-immersion diagonal and `Λ ⟶ S` is
    separated, then so does `F × Y(Λ)`. The proof factors the diagonal as two base changes,
    one of the diagonal of `F` and one of the diagonal of `Y(Λ)`.
- Translations: for a presheaf of commutative groups `G` and `c ∈ G(Λ)`, `translate G c`
  is `(x, α) ↦ (x + α^* c, α)`. `translateIso` is the corresponding isomorphism, with
  inverse translation by `-c`.
