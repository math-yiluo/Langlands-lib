# Sections of the Poincaré bundle along a nonzero tangent vector: proof

`Langlands.AbelianScheme.algClosedFieldPoincareTangentSections` proves the exact
published proposition
`Langlands.AbelianScheme.AlgClosedFieldPoincareTangentSectionsStatement.{u}`.
Its type is that proposition, with all binders and with no extra hypothesis: an
arbitrary universe `u`, an algebraically closed field `K`, an abelian scheme `A`
over `Spec K` with dual datum `hA`, a `K[ε]`-point `t` of `D = dualScheme A hA`
that is a nonzero tangent vector at the origin, and any fibre product `X` of the
projection `p : A ×_K D ⟶ D` along `t`, with projections `q` and `f`. The theorem
shows that `(relativeGlobalSections f).obj (q^* P)` is not isomorphic to `K[ε]`
as a `K[ε]`-module, where `P = (poincareLineBundle A hA).obj`. Algebraic
closedness of `K` is not used in the proof.

The module also proves three auxiliary results, all in namespace
`Langlands.AbelianScheme`. It imports the statement module, the helper modules
`Picard/DualNumberSectionTrivialization` and `Picard/DualPointOriginTriviality`,
and the published modules `Modules/SectionVanishingTransportProof`,
`LinearSystem/SectionRatio` and `SmoothProperConnectedGlobalFunctionsProof`.

## Auxiliary results

Throughout, `S` is a scheme, `A` an abelian scheme over `S`, and
`hA : HasDualScheme A`, with `D = dualScheme A hA`.

- `originFibreSection A hA : A.X.left ⟶ pullback A.X.hom D.hom` is the map
  `a ↦ (a, 0)`: the pullback lift of `𝟙` and `A.X.hom ≫ (dualOrigin A hA).left`.
  It is well defined because `(dualOrigin A hA).left ≫ D.hom = 𝟙 S` (`Over.w`).
  The simp lemmas `originFibreSection_fst` and `originFibreSection_snd` record its
  two components.
- `nonempty_dualPointFamily_origin_iso A hA`: the underlying line bundle of
  `dualPointFamily A hA (dualOrigin A hA)` is isomorphic to the trivial line
  bundle on `(relativeSpace A.X.hom).obj (Over.mk (𝟙 S))`. The published
  `dualPointClass_origin` with `T = Over.mk (𝟙 S)` (and the published proof
  `picardZeroPullback`) says that the class of `Over.homMk (𝟙 S) ≫ dualOrigin A hA`
  is the trivial Picard-zero class. `Over.homMk (𝟙 S)` is the identity, checked
  with `Over.OverMorphism.ext`. Taking underlying classes and `Quotient.exact`
  gives an isomorphism of rigidified line bundles with
  `RigidifiedLineBundle.trivial`, and `RigidifiedLineBundle.forget` maps it to
  the stated isomorphism.
- `nonempty_originFibreSection_pullback_iso A hA`: the pullback of `P` along
  `originFibreSection A hA` is isomorphic to `structureModule A.X.left`. The
  Poincaré bundle is by definition (`familyLineBundle`) the pullback of the
  carrier `L₀` of `poincareFamily A hA` along
  `(relativeSpaceSymmetry A.X.hom D).inv`. Let
  `r₀ = pullback.lift A.X.hom (𝟙 A.X.left)` into
  `(relativeSpace A.X.hom).obj (Over.mk (𝟙 S))` and
  `m = (relativeSpace A.X.hom).map (dualOrigin A hA)`. The equation
  `originFibreSection A hA ≫ (relativeSpaceSymmetry A.X.hom D).inv = r₀ ≫ m`
  is checked with `pullback.hom_ext`. The two components are explicit `calc`
  chains using `pullbackSymmetry_inv_comp_fst`/`_snd` and the lift equations
  of `r₀` and `m`. The isomorphism is the composite of
  `Scheme.Modules.pullbackComp`, `Scheme.Modules.pullbackCongr` along that
  equation, the inverse of `pullbackComp r₀ m`, the pullback along `r₀` of the
  previous isomorphism, and `Langlands.Scheme.Modules.pullbackUnitIso r₀`.
- `eq_zero_or_isUnit_of_abelianScheme A c`: for an abelian scheme `A` over
  `Spec K` (any field `K`), every `c : Γ(A.X.left, ⊤)` is zero or a unit. The
  published `Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`
  applies, since `A.X.hom` is smooth, proper and geometrically connected. It
  makes `A.X.hom.app ⊤` an isomorphism, so `c` is the image of an element of `K`
  under the ring maps `(Scheme.ΓSpecIso _).inv` and `A.X.hom.app ⊤`. A
  nonzero element of `K` is a unit, and ring maps preserve zero and units.

## Proof of the theorem

Let `φ` be an isomorphism of `K[ε]`-modules from the sections of `M = q^* P` to
`K[ε]`; we derive `False`. From `IsNonzeroTangentVectorAt` we use
`t ≫ D.hom = dualNumberProjection K` (`ht₁`),
`dualNumberAugmentation K ≫ t = (dualOrigin A hA).left` (`ht₂`) and
`t ≠ dualNumberProjection K ≫ (dualOrigin A hA).left`.

1. **A section not killed by `ε`.** Let `s = φ.inv 1`, a global section of `M`.
   The `K[ε]`-module structure of `relativeGlobalSections f` is scalar
   multiplication through `structureRingHom f`. If
   `structureRingHom f ε • s = 0`, then `φ.inv (ε • 1) = 0` by linearity, and
   applying `φ.hom` gives `ε = 0` in `K[ε]`. That is false, since the
   second coordinate of `ε` is `1`. So `structureRingHom f ε • s ≠ 0` (`hs`).
   This is the only property of `φ` that is used.
2. **`X` is the thickening of `A`.** Pasting `h` with the pullback square of
   `A ×_S D` (`IsPullback.paste_horiz`) and rewriting with `ht₁` gives
   `IsPullback (q ≫ pullback.fst A.X.hom D.hom) f A.X.hom (dualNumberProjection K)`.
   Its `isoPullback` is an isomorphism `ψ` from `X` to the published
   `DualNumberThickening.thickening A.X.hom`. Write `j = ψ.inv`. Then
   `j ≫ f` is the structure map of the thickening and
   `j ≫ q ≫ pullback.fst _ _` is its projection (`isoPullback_inv_snd`,
   `isoPullback_inv_fst`). Let `L` be the line bundle `j^* q^* P` on the
   thickening.
3. **Trivial closed fibre.** With `c` the zero section `closedPoint A.X.hom` of
   the thickening, `(c ≫ j) ≫ q = originFibreSection A hA` (`hc₀`). This is
   checked with `pullback.hom_ext`. The first component uses
   `closedPoint_projection`. The second uses the square `h.w`, `j ≫ f`,
   `closedPoint_structure` and `ht₂`. So
   `pullbackComp`, `pullbackCongr` and `nonempty_originFibreSection_pullback_iso`
   give a trivialization `e : c^* L ≅ structureModule A.X.left`.
4. **Transport of the section.** Let `s' = pullbackSection j M s`, a global
   section of `L`. The global epsilon of the thickening
   (`DualNumberThickening.globalEpsilon`) is `j.appTop (structureRingHom f ε)`.
   This follows from rewriting the structure map as `j ≫ f` and
   `Scheme.Hom.comp_appTop`. The published `pullbackSection_smul`
   (`Langlands.AlgebraicGeometry.LinearSystem`) and
   `pullbackSection_iso_eq_zero_iff` (`j` is an isomorphism) turn `hs` into
   `globalEpsilon A.X.hom • s' ≠ 0`.
5. **Triviality.** `DualNumberThickening.isIso_sectionHom_of_globalEpsilon_smul_ne_zero`
   applies to `L`, `e` and `s'`, with
   `eq_zero_or_isUnit_of_abelianScheme A` as its hypothesis on global functions.
   It shows that `sectionHom L.obj s'` is an isomorphism. Together with
   `pullbackComp j q` this gives
   `(j ≫ q)^* P ≅ SheafOfModules.unit` on the thickening.
6. **Universality.** `IsPullback.of_iso` transports `h` along `ψ` to
   `IsPullback (j ≫ q) (structureMap A.X.hom) p t`. The helper theorem
   `dualPoint_eq_origin_of_isPullback`, applied with
   `T = Over.mk (t ≫ D.hom)` and the over-morphism `Over.homMk t`, then gives
   `Over.homMk t = Over.homMk T.hom ≫ dualOrigin A hA`. Taking `.left` and
   rewriting with `ht₁` gives `t = dualNumberProjection K ≫ (dualOrigin A hA).left`,
   which contradicts the nonzero-tangent-vector hypothesis.

## Provenance

The statement's Markdown explains the source: Edixhoven, van der Geer and Moonen,
*Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), (9.5) and (9.8), printed
pp.128–130 (PDF pp.132–134). The Lean proof follows the informal argument given
there. The closed fibre is trivial, and a section with `ε s ≠ 0` reduces to a
nonzero constant, so it trivializes the bundle; the universal property then forces
`t` to be the zero tangent vector. The local step "a homomorphism of line bundles
that is an isomorphism modulo `ε` is an isomorphism" is implemented in
`DualNumberSectionTrivialization` with the published normalized affine frames of
`DualNumberAffineFrames`. The universal-property step is Worker 1165's
`dualPoint_eq_origin_of_isPullback` in `DualPointOriginTriviality`.
