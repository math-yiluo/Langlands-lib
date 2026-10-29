# Bundles algebraically trivial via a smooth family are translation invariant

This module proves the forward direction of the field smooth-family
comparison. Over an algebraically closed field `K`, a line bundle on an
abelian variety that is algebraically trivial via a smooth family is
translation invariant. The theorem of the cube with a smooth, not
necessarily proper, third factor is an explicit hypothesis of the final
theorem.

## Declarations

In namespace `Langlands.AbelianScheme.TranslationOfSmoothFamily`:

- `geometricallyConnected_of_geometricallyIntegral f`: a geometrically
  integral morphism of schemes is geometrically connected, because an
  irreducible space is connected.
- `pairMap A C c a`: for an abelian scheme `A` over `S`, `C : Over S` and
  morphisms `c : W ⟶ C`, `a : W ⟶ A.X` over `S`, the scheme map
  `W.left ⟶ C ×_S A` with coordinates `c` and `a`. The product is the
  parameter-first product `(relativeSpace A.X.hom).obj C`. The lemmas
  `pairMap_fst`, `pairMap_snd` give its coordinates, `pairMap_pullback` its
  naturality in `W`, and `pairMap_const` says that a constant parameter
  `c₀` factors it through `smoothFamilyPointMap A C c₀`.
- `cubeShape A N N' c a b`: for modules `N`, `N'` on `C ×_S A`, the module
  `N(c, a + b) ⊗ (N'(c, a) ⊗ (N'(c, b) ⊗ N(c, 0)))` on `W.left`. Each factor
  is a pullback along a `pairMap`, and `a + b` is the product `a * b` in the
  group structure of `A.X`.
- `pairPullbackIso` and `cubeShapePullbackIso`: the cube shape is natural
  in `W`. Pulling back along `g : V ⟶ W` gives the cube shape of `g ≫ c`,
  `g ≫ a` and `g ≫ b`. These use the tensor preservation statement
  `preservation`.
- `tensorFourTrivialIso`: `U ⊗ (U' ⊗ (Z' ⊗ Z))` is trivial when `U ⊗ U'`
  and `Z ⊗ Z'` are.
- `pairEvaluation`: the evaluation `ev : N ⊗ N' ≅ 𝒪` pulled back along a
  pair map.
- `firstFaceIso`, `secondFaceIso`, `thirdFaceIso`: the cube shape is
  trivial when `a = 0`, when `b = 0`, and when `c` is the constant `c₀` and
  `N(c₀, -)` is trivial. The helpers are `constPairIso` (a pair factor with
  constant parameter `c₀` where the module is trivial) and
  `inverseAtPointIso` (`N'(c₀, -)` is trivial when `N(c₀, -)` is).
- `cubeModule A N N'`: the cube shape on `A × (A × C)` with coordinates
  `(x, y, c)`, that is `cubeShape` at `c = pr₃`, `a = pr₁`, `b = pr₂`.
- `first_face_trivial`, `second_face_trivial`, `third_face_trivial`: the
  pullbacks of `cubeModule A N N'` along `CubeFace.first A.X A.X C 1`,
  `CubeFace.second A.X A.X C 1` and `CubeFace.third A.X A.X C c₀` are
  isomorphic to the structure sheaf. These are the three face hypotheses
  of the cube statement.
- `cubeBundle A preservation N N'`: the same module as an actual
  `LineBundle`, with `cubeBundle_obj` stating that its underlying module
  is `cubeModule A N.obj N'.obj` by definition.
- `restrictionIso`, `restrictionMap`, `translate_tensor_trivial`: over a
  field, for points `c₁` of `C` and `x` of `A`, the map
  `restrictionMap A c₁ x : A ⟶ A × (A × C)`, `a ↦ (x, a, c₁)`, pulls the
  cube shape back to `t_x^*N(c₁, -) ⊗ N'(c₁, -)`. Two of the four factors
  are pullbacks along constant maps. The Library's
  `MumfordPicardZero.constantIso` trivializes them, using the field
  triviality statement `triviality`. So a trivialization of
  `cubeModule A N.obj N'.obj` gives a trivialization of
  `t_x^*N(c₁, -) ⊗ N'(c₁, -)`.
- `cubeModule_trivial A cube preservation hSm hConn N N' ev c₀ e₀`: the
  cube hypothesis `cube`, applied with `X = Y = A.X`, `Z = C`,
  `x₀ = y₀ = 1`, `z₀ = c₀` and the bundle `cubeBundle A preservation N N'`,
  trivializes `cubeModule A N.obj N'.obj`. The hypotheses on `A.X` hold
  because `A` is an abelian scheme. The hypotheses on `C` are `hSm` and
  `hConn`.
- `pullback_iso_of_tensor_trivial`: for `s : X ⟶ P`, `t : X ⟶ X`, a
  tensor inverse `N'` of `N` on `P` and `h : s^*N ≅ L`, a trivialization
  of `t^*(s^*N) ⊗ s^*N'` gives `t^*L ≅ L`. It uses the Library's
  `LineBundle.tensorInverseComparisonIso`: both `t^*(s^*N)` and `s^*N` are
  tensor inverses of `s^*N'`.

In namespace `Langlands.AbelianScheme`:

- `isTranslationInvariant_of_isAlgebraicallyTrivialViaSmoothFamily`:
  takes the hypothesis
  `cube : Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialitySmoothThirdStatement.{u}`.
  Then for an algebraically closed field `K`, an abelian scheme `A` over
  `Spec K` and `L : LineBundle A.X.left` with
  `IsAlgebraicallyTrivialViaSmoothFamily A L`, it proves
  `GroupScheme.IsTranslationInvariant A.toGrp L`.

## Proof

The hypothesis `IsAlgebraicallyTrivialViaSmoothFamily A L` gives a scheme
`C` over `K` that is smooth and geometrically integral, points `c₀` and
`c₁` of `C`, and a line bundle `N` on `C ×_K A`, with `N(c₀, -)` trivial
and `N(c₁, -) ≅ L`. The Library lemma
`LineBundle.exists_tensorObj_iso_structureSheaf` gives a tensor inverse
`N'` of `N` with `ev : N ⊗ N' ≅ 𝒪`. Tensor preservation is the Library
theorem `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`.

The bundle `M(x, y, c) = N(c, x + y) ⊗ N'(c, x) ⊗ N'(c, y) ⊗ N(c, 0)` on
`A × A × C` is trivial on the three faces. On `x = 0`, `N(c, y)` cancels
`N'(c, y)` and `N'(c, 0)` cancels `N(c, 0)`. The face `y = 0` is the same
with `x`. On `c = c₀`, every factor is a pullback of `N(c₀, -)` or
`N'(c₀, -)`, and both are trivial. `C` is geometrically connected because
it is geometrically integral. So `cube` trivializes `M`
(`cubeModule_trivial`).

Fix a point `x`. Restrict `M` along `a ↦ (x, a, c₁)`. The factors
`N'(c₁, x)` and `N(c₁, 0)` are pullbacks along constant maps `A → Spec K`
and are trivial. So `t_x^*N(c₁, -) ⊗ N'(c₁, -)` is trivial
(`translate_tensor_trivial`). Since `N(c₁, -) ≅ L`,
`pullback_iso_of_tensor_trivial` gives `t_x^*L ≅ L`. This is
translation invariance at `x`.

## Sources

Milne, *Abelian Varieties* (1986 article, author revision 2022), Remark
9.3, page 15, states this direction: a sheaf occurring in an algebraic
family over a connected variety containing a trivial sheaf lies in
`Pic⁰`, by the theorem of the cube. The cube theorem with a connected,
locally noetherian, not necessarily complete third factor is Theorem
(2.5) of Edixhoven, van der Geer and Moonen, *Abelian Varieties*, printed
page 18 (PDF page 22). The Lean proof follows this route. The cube
theorem is the hypothesis `cube`, not proved here.

## Scope

The algebraically closed field `K`, the abelian scheme `A` and the bundle
`L` are arbitrary; algebraic closedness matches
`SmoothFamilyTranslationInvarianceStatement` and is not used by the proof.
The only hypothesis besides the predicate is `cube`. The Library theorems
`Langlands.AlgebraicGeometry.Picard.fieldLineBundleTriviality` and
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso` are used
directly, not as hypotheses. The cube statement
is applied with a third factor `C` that is smooth and geometrically
connected but not proper. The Library's `FieldCubeTrivialityStatement`,
which requires `C` proper, does not apply here. This module does not
prove the reverse direction of the comparison.
