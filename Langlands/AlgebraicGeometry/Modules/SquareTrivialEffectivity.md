# Effectivity for globally trivial modules over a nilpotent-surjective leg

This internal construction works in an arbitrary universe `u` and uses actual
scheme-module pullbacks. For a scheme morphism `f : X ⟶ Y`, assume that its
actual map on global sections `f.appTop.hom` is surjective with nilpotent kernel.
If two modules on `Y` have specified global trivializations, `exists_iso` lifts
every isomorphism between their pullbacks to an isomorphism on `Y`.
`liftIso` chooses such a lift and `pullback_liftIso` proves that its ordinary
pullback equals the prescribed isomorphism. No uniqueness is claimed.

The proof normalizes the given isomorphism using the two pulled-back frames and
the canonical `pullbackUnitIso`. Its scalar is a global unit on `X`.
`NilpotentUnitReduction.unitsMap_surjective` lifts that unit to `Y`.
Naturality of `structureAutScalar` and its injectivity identify the pullback of
the corresponding structure-module automorphism with the normalized input.
Transporting back through the frames gives the desired lift. This is the
unit-lifting version of the normalization argument implemented in
`TrivialIsoDescentProof`; unlike compatible effective-epimorphism descent, it
uses surjectivity of the actual global unit map and does not assert uniqueness.

For any commuting square of actual schemes
`i₁ : Y₀ ⟶ Y₁`, `i₂ : Y₀ ⟶ Y₂`, `j₁ : Y₁ ⟶ Y`, `j₂ : Y₂ ⟶ Y`,
assume only that `i₂.appTop.hom` is a nilpotent surjection. Given globally
trivial modules `M₁`, `M₂` on the two legs and any actual overlap isomorphism
`e : i₁* M₁ ≅ i₂* M₂`, the definitions `leftIso` and `rightIso` identify the
two pullbacks of the structure module on `Y` with `M₁` and `M₂`.
`compatible` and `exists_compatible_isos` show that these identifications realize
`e` using the ordinary `squarePullbackIso`, including its canonical composition
and equality comparisons. The first leg uses its given frame. The second lifts
the isomorphism obtained by composing the inverse square comparison with the
first leg and the prescribed overlap.

This construction is derived from the published actual global-unit lifting,
structure-module scalar, and coherent ordinary pullback APIs. It does not
require the square of global rings to be a pullback, nor an affine, field,
properness, flatness, or finiteness hypothesis. Applications must separately
supply the global frames and nilpotent-surjective sections map. Passing from
these local object realizations to global effectivity for arbitrary line
bundles remains an obligation of the host infinitesimal-gluing task.
