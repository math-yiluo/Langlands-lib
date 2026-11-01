# Actual generic line bundles over normal finite fraction-field stages

This internal adapter combines the imported `FiniteFractionFieldStages` constructions
with the published theorem `lineBundleSubalgebraDescent`. It supplies an actual
line-bundle model over a stage's fraction field and an actual module-sheaf
comparison. Both normal-stage existence conclusions explicitly assume
`NormalFiniteTypeSubalgebraStatement.{u}`. No proof of that proposition or of the
arbitrary-valuation two-axis extension theorem is supplied here.

## Base maps and finite field algebras

Fix a commutative domain `R` and a field `K` in an arbitrary universe `u`, with
`Algebra R K` and `IsFractionRing R K`. For integer subalgebras `C ≤ T` of `R`,
`fractionFieldStageBaseMap R C T hCT` is the actual ring map

`C → T → FractionRing T`,

where the first arrow is `Subalgebra.inclusion hCT` and the second is the
fraction-field algebra map. `stageFractionFieldMap_comp_baseMap` proves that its
composite with `stageFractionFieldMap R K T` equals the actual composite
`C → R → K`.

`exists_normal_fractionFieldFactor_over` additionally assumes that `R` is
integrally closed, `hNormal : NormalFiniteTypeSubalgebraStatement.{u}`, that `C`
is finitely generated over the integers, and an `Algebra C K` whose algebra map
is the composite `C → R → K`. Given a finite subset `sR` of `R` and a finitely
generated `C`-subalgebra `B` of `K`, it produces:

- an integer subalgebra `T` of `R` containing both `C` and `sR`, finitely
  generated over the integers, integrally closed, and noetherian;
- an actual injective ring map `j : B →+* FractionRing T`;
- the equality `stageFractionFieldMap R K T ∘ j = B.val` of ring maps;
- the equality `j ∘ algebraMap C B = fractionFieldStageBaseMap R C T hCT`.

The proof first uses transitivity of finite type to regard `B` as a finitely
generated integer subalgebra of `K`. It pins the action of `C` on `K` to the
supplied algebra structure; uniqueness of integer ring maps then constructs the
required scalar tower. Include a finite set of generators of `C` in `sR` and
apply the imported `exists_normal_fractionFieldFactor`. The resulting stage
contains `C` by the universal property of algebra adjoin. Finally, injectivity of
`stageFractionFieldMap` reduces the equality over `C` to the given compatibility
of `Algebra C K`.

## An actual line-bundle model

`exists_normal_fractionField_lineBundle_model` has the same ring assumptions,
including `hNormal`, and takes a quasi-compact, quasi-separated morphism
`f₀ : X₀ → Spec C`. Let `X` fit into the given pullback square with sides
`a : X → X₀` and `f : X → Spec K`, over the specified map `Spec K → Spec C`.
For an actual Library `LineBundle M` on `X` and finite ring data `sR`, the theorem
produces a stage `T` with all the properties above. Put

`P_T = X₀ ×_(Spec C) Spec (FractionRing T)`,

using Mathlib's chosen pullback and the actual map
`fractionFieldStageBaseMap R C T hCT`. It supplies an actual Library line bundle
`N` on `P_T` and a morphism `c : X → P_T` with the following data:

- `c` composed with the first projection is `a`;
- `c` composed with the second projection is `f` followed by the spectrum map
  induced by `stageFractionFieldMap R K T`;
- the square with sides `c` and `f`, over that spectrum map and the second
  projection of `P_T`, is a pullback square;
- there exists an isomorphism `(Scheme.Modules.pullback c).obj N.obj ≅ M.obj`.

To construct these witnesses, apply the imported `lineBundleSubalgebraDescent`
to `M.obj` and its local rank-one property, with empty prescribed field data.
This gives a finitely generated `C`-subalgebra `B` of `K` and a locally free
rank-one module `NB` on `P_B = X₀ ×_(Spec C) Spec B`. Apply the algebraic factor
theorem above to `B`. The equalities of ring maps become equalities of spectrum
maps by contravariance. They define `p : P_T → P_B` and `c : X → P_T` by
`pullback.lift`. Their projection equations show that `c ≫ p` is compatible with
both projections to `P_B`, so the original descent comparison applies along
this composite. Set `N.obj = (Scheme.Modules.pullback p).obj NB`; local rank one
is preserved by pullback. Compose `Scheme.Modules.pullbackComp c p` with the
descent comparison to obtain the displayed isomorphism. The asserted pullback
square follows from `IsPullback.of_right`, cancelling the canonical pullback
square defining `P_T` from the original square for `X`.

The proof uses only the named Library descent and algebraic constructions and
Mathlib's universal properties. This is derived internal content, not a new
translation of a literature statement. The geometric theorem does not descend
any specified axis trivializations or rigidifications. It neither extends `M`
over the total original base nor constructs a correspondence; those obligations
and the unconditional proof of `hNormal` remain separate.
