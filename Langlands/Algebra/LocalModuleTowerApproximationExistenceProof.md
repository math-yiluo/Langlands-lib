# Existence of simultaneous local tower approximations, proof

The closing theorem is `Langlands.Algebra.localModuleTowerApproximationExistence.{u, v, w, z}`.
Its complete type is the published proposition
`Langlands.Algebra.LocalModuleTowerApproximationExistenceStatement.{u, v, w, z}`. This is the
construction in the proof of Stacks 00R7, Lemma 10.128.8, before the flatness argument. The
four ambient universes `u, v, w, z` stay independent, and the theorem has no further
hypotheses. The statement pair and its imports are unchanged. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Tower helpers (namespace `LocalAlgebraTowerSystem`)

- `tail D i₀` restricts a synchronized tower to the indices above `i₀`. Its lower arrow is
  the Library restriction `D.rs.tail i₀`. Its upper rings, algebra structures, transitions
  and cocone maps are those of `D` at the underlying indices. Its upper arrow
  `(D.tail i₀).st` is definitionally `D.st.tail i₀`.
- `tail_isApproximation`: restriction to a tail preserves `IsApproximation`.
  - The lower clause is `LocalAlgebraSystem.tail_isApproximation`.
  - Both upper colimit comparisons stay bijective by `ringDirectLimit_lift_tail_bijective`.
  - The other three clauses are those of `D` at the underlying indices.
- `st_isApproximation`: if `D.IsApproximation`, then the upper arrow `D.st` is a ring
  approximation system for `S → T` (`LocalAlgebraSystem.IsApproximation`). Its base rings
  `D.rs.alg i` are essentially of finite type over `ℤ` by `Algebra.EssFiniteType.comp`. This
  uses that `D.rs.base i` is essentially of finite type over `ℤ` and `D.rs.alg i` is
  essentially of finite type over `D.rs.base i`. The other clauses are clauses of
  `D.IsApproximation`.

## Proof of the closing theorem

Fix `R : Type u`, `S : Type v`, `T : Type w`, `M : Type z` and the hypotheses of the
statement. Write `U = max u v w z`.

1. **Lower ring system.** Transport `EssFinitePresentation R S` to
   `ULift.{max w z} S`, and check that `R → ULift S` is local. Apply the published 00QV theorem
   `localAlgebraApproximationExistence.{u, max v w z}`. This gives a directed index
   `ι : Type U` and a ring approximation system for `R → ULift S` with all components in
   `Type U`. Compose its algebra cocone with `ULift.algEquiv`
   (`LocalAlgebraSystem.mapAlgEquiv` and `mapAlgEquiv_isApproximation`). The result is a
   ring approximation system `D₁` for `R → S` on the same components.
2. **Presentation of `T` over `S`.**
   `LocalAlgebraTowerApproximation.nonempty_pres_upper_of_essFinitePresentation` gives a
   presentation `P : Pres S S T (RingEquiv.refl S)` from the two hypotheses over `R`. The
   tower cancellation statement is not used.
3. **Upper stages.** `exists_relLift` gives an index `i₀` and lifts
   `L : RelLift (D₁.tail i₀) P` of the relations of `P`. The tail `D₁.tail i₀` is still a ring
   approximation system (`tail_isApproximation`). So `L.tower`, whose lower arrow is
   `D₁.tail i₀`, satisfies `LocalAlgebraTowerSystem.IsApproximation` by
   `tower_isApproximation`. Its upper rings are localizations of quotients of polynomial
   rings over the components of `D₁`, so they also lie in `Type U`.
4. **Module system.** `exists_matrix_presentation` writes `M` as
   `(Fin n → T) ⧸ range A.mulVecLin` for a matrix `A` over `T`, through a `T`-linear
   equivalence `eA`. By `st_isApproximation`, `L.tower.st` is a ring approximation system for
   `S → T`, so the entries of `A` lift to one upper stage `Tᵢ₁` (`exists_algι_eq_fun`). The
   lifted matrix therefore lies over the upper stage ring. Then
   `L.tower.st.presentationSystem A i₁ a ha` is the cokernel system of the lifted matrices on
   `L.tower.st.tail i₁`. `presentationSystem_isApproximation` shows that it is a module
   approximation system. `mapLinearEquiv eA` moves its cocone to `M`, and
   `mapLinearEquiv_isApproximation` keeps the approximation property.
5. **Witness.** The witness has these components:
   - the index type is the tail `{j // i₁ ≤ j}` of the index of `L.tower`;
   - the tower is `L.tower.tail i₁`;
   - the module system is the `LocalModuleTowerSystem` whose `stModule` is the transported
     presentation system. This typechecks because `(L.tower.tail i₁).st` is definitionally
     `L.tower.st.tail i₁`.

   `E.IsApproximation` is proved clause by clause:
   - the ring clause is `tail_isApproximation`;
   - the additive colimit bijection, the finiteness of the stage modules over the upper stage
     rings, and the bijectivity of the scalar-first module base-change maps are the
     corresponding clauses of the module approximation property from step 4.

The index, all three families of component rings, and the component modules lie in `Type U`:
the index is a tail of a tail of `ι`, and the module components are quotients of finite
powers of the upper stage rings. These are the universes required by the statement.
