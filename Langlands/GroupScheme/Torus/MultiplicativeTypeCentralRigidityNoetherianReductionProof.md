# Proof: central rigidity for groups of finite presentation from the noetherian case

Worker 396 wrote this module. It proves

```lean
theorem Langlands.GroupScheme.multiplicativeTypeCentralRigidityNoetherianReduction :
    MultiplicativeTypeCentralRigidityNoetherianReductionStatement.{u}
```

for the published statement
`Langlands.GroupScheme.MultiplicativeTypeCentralRigidityNoetherianReductionStatement`
([`MultiplicativeTypeCentralRigidityNoetherianReductionStatement`](MultiplicativeTypeCentralRigidityNoetherianReductionStatement.md)),
in every universe `u` and with no further hypotheses. Suppose SGA 3, IX, Théorème 5.1 holds
over every locally noetherian base. Then it holds over an arbitrary base `S`, provided the
structure morphism of `G` is locally of finite presentation, quasi-compact and
quasi-separated.

The proof follows the order suggested in the task, not the order of SGA 3. It first passes to
an affine chart of an fppf cover over which `H` is diagonalizable, and only then uses
noetherian approximation. It never makes `S` local.

## Notation and helper predicates

All helper declarations are in the namespace
`Langlands.GroupScheme.CentralRigidityNoetherianReduction`. Throughout, `S` is a scheme,
`H, G : GroupScheme S` and `u, v : H ⟶ G`.

* `FibreHyp u v s` (a `Prop`-valued `def`) is the hypothesis of Théorème 5.1 at `s ∈ S`. It
  is the conjunction of `u_s = v_s` and `IsCentral u_s`, where
  `u_s = (baseChange (S.fromSpecResidueField s)).map u`. These are the same Lean expressions
  as in the target statement.
* `LocalEq u v s` (a `Prop`-valued `def`) is the conclusion. It says there is
  `U : S.Opens` with `s ∈ U` and `(baseChange U.ι).map u = (baseChange U.ι).map v`. Again
  this is the same expression as in the target statement.
* `NoetherianHyp` (a `Prop`-valued `def`) is the hypothesis of the target statement written
  with these two predicates. For every locally noetherian `S`, every `H` of multiplicative
  type and every `G`, `FibreHyp u v s → LocalEq u v s`. The main theorem derives it from
  the hypothesis of the target statement by splitting the conjunction.

These three definitions are internal abbreviations for this proof. They are not new
mathematical notions and do not appear in the statement that is proved.

## Transfer lemmas (section `Transfer`)

* `baseChange_map_injective b h`: base change along a flat surjective `b : S' ⟶ S` is
  faithful on homomorphisms. The projection `pullback.fst H.X.hom b` is flat and surjective,
  so it is an epimorphism by Mathlib's `Flat.epi_of_flat_of_surjective`. The underlying
  morphisms of `u` and `v` agree after composing with it (`pullback.lift_fst`).
* `map_eq_comp_iff a b u v`: `u` and `v` agree after base change along `b ≫ a` if and only
  if they agree after base change along `a` and then `b`. The proof uses the comparison
  isomorphism `Descent.pullbackComparison` and its naturality
  `Descent.pullbackComparison_naturality`, from
  [`Descent/Data`](../Descent/Data.md).
* `FibreHyp.conj` and `LocalEq.of_conj`: conjugating `u, v` by isomorphisms `eH : H ≅ H'`
  and `eG : G ≅ G'` preserves `FibreHyp`. `LocalEq` for the conjugates gives `LocalEq` for
  `u, v`. Centrality is preserved under composition with an isomorphism by the Library's
  `IsCentral.comp` and `IsCentral.comp_iso`.
* `flat_surjective_specMap_residueFieldMap f t`: for `f : S' ⟶ S` and `t ∈ S'`, the map
  `Spec κ(t) ⟶ Spec κ(f t)` is flat and surjective. This is the Library's
  `fieldExtension_fpqc` ([`BaseChangeReflection`](../BaseChangeReflection.md)) applied to
  the residue field extension.
* `FibreHyp.pull f t`: `FibreHyp u v (f t)` implies `FibreHyp` of the base changes along `f`
  at `t`. The square `Spec κ(t) ⟶ Spec κ(f t) ⟶ S` equals `Spec κ(t) ⟶ S' ⟶ S` (Mathlib's
  `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`). So the fibre of the base
  change at `t` is the base change of the fibre at `f t`. Equality is then rewritten with
  `map_eq_comp_iff`, and centrality with `HopfFiberCentralityResidue.isCentral_baseChange_comp_iff`
  ([`HopfFiberCentralityResidue`](../HopfFiberCentralityResidue.md)). Centrality is stable
  under base change by `IsCentral.baseChange`
  ([`CentralIsogeny/BaseChange`](../CentralIsogeny/BaseChange.md)).
* `FibreHyp.descend f t`: the converse. It uses the same square together with
  `baseChange_map_injective` and the Library's `IsCentral.of_baseChange`
  ([`CentralIsogeny/FpqcReflectionHelpers`](../CentralIsogeny/FpqcReflectionHelpers.md)) along
  the flat surjective map `Spec κ(t) ⟶ Spec κ(f t)`.
* `LocalEq.pull f t`: an open `U ∋ f t` pulls back to `f ⁻¹ᵁ U ∋ t`. This uses
  `morphismRestrict_ι`, which says that `f ⁻¹ᵁ U ⟶ S'` followed by `f` is `f ∣_ U` followed
  by `U ⟶ S`.
* `LocalEq.descend f t`: let `f` be flat and locally of finite presentation, and suppose
  `u, v` agree after base change to an open `U' ∋ t` of `S'`. Then `V = f(U')` is open,
  since `f` is an open map (Mathlib, `UniversallyOpen` of flat morphisms locally of finite
  presentation). The restriction `g : U' ⟶ V` (`Scheme.Hom.resLE`) is flat and surjective,
  and `g ≫ V.ι = U'.ι ≫ f`. So the base changes of `u, v` to `V` become equal after base
  change along `g`, hence are equal by `baseChange_map_injective`. This step needs no
  quasi-compactness.

## Models (section `Model`)

* `model_transfer φ eH eG hu hv s h hloc`: let `φ : S ⟶ S₀` and `u₀, v₀ : H₀ ⟶ G₀` over
  `S₀`, with isomorphisms `eH : φ^*H₀ ≅ H` and `eG : φ^*G₀ ≅ G` such that
  `φ^*u₀ = eH.hom ≫ u ≫ eG.inv` and similarly for `v`. Suppose `FibreHyp u v s`, and
  suppose `FibreHyp u₀ v₀ (φ s)` implies `LocalEq u₀ v₀ (φ s)`. Then `LocalEq u v s`. The
  proof combines `FibreHyp.conj`, `FibreHyp.descend`, `LocalEq.pull` and `LocalEq.of_conj`.
* `isNoetherianRing_of_fg`: a finitely generated subalgebra of an algebra over a noetherian
  ring is noetherian (Mathlib's `Subalgebra.fg_iff_finiteType` and
  `Algebra.FiniteType.isNoetherianRing`).

## The affine case (section `Affine`, assuming `hyp : NoetherianHyp`)

* `spec_core`: `R` is a noetherian ring with an algebra `A`. `H₀, G₀` are groups over
  `Spec R` with `H₀` of multiplicative type, `H₀ → Spec R` quasi-compact and
  quasi-separated, and `G₀ → Spec R` locally of finite presentation. The homomorphisms
  `u, v` go between the base changes of `H₀` and `G₀` to `Spec A`. Then `FibreHyp u v s`
  implies `LocalEq u v s`.
  1. The Library's `Descent.FiniteCoefficient.homGeneral`
     ([`Descent/FiniteCoefficientHomGeneral`](../Descent/FiniteCoefficientHomGeneral.md))
     gives a finitely generated `R`-subalgebra `T₃ ⊆ A` and `g₃` over `Spec T₃` whose
     base change to `A` is `u`, up to the comparison isomorphisms `cH, cG`.
  2. Apply `homGeneral` again over `T₃` to `cH.hom ≫ v ≫ cG.inv`. This gives a finitely
     generated `T₃`-subalgebra `T₄ ⊆ A` and `g₄` over `Spec T₄` whose base change to `A`
     is that morphism, up to the comparison isomorphisms `dH, dG`.
  3. `T₃` and `T₄` are noetherian by `isNoetherianRing_of_fg`, so `Spec T₄` is locally
     noetherian. The base change of `H₀` to `Spec T₄` is of multiplicative type
     (`IsMultiplicativeType.baseChange` twice).
  4. With `φ = Spec A ⟶ Spec T₄`, `eH = dH ≪≫ cH` and `eG = dG ≪≫ cG`, apply
     `model_transfer` to `u₀ = (base change of g₃ to T₄)` and `v₀ = g₄`. The identity for
     `u₀` follows from `pullbackComparison_naturality` and step 1, and the identity for
     `v₀` is step 2. The hypothesis `hloc` is `hyp` over `Spec T₄`.
* `spec_case`: the base is `Spec R` for `R : CommRingCat`, `H` is diagonalizable (`H ≅ D(Λ)`
  with `Λ` finitely generated), and `G → Spec R` is locally of finite presentation,
  quasi-compact and quasi-separated. Then `FibreHyp u v s` implies `LocalEq u v s`.
  1. Write `R = CommRingCat.of A` (Mathlib's `CommRingCat.of_carrier`, by `rfl`).
  2. Take `A₀ = ⊥ : Subalgebra ℤ A`, which is noetherian because it is finitely generated
     over `ℤ`. The Library's `schemeSubalgebraDescent`
     ([`SchemeSubalgebraDescentProof`](../../AlgebraicGeometry/NoetherianApproximation/SchemeSubalgebraDescentProof.md))
     gives a finitely generated `A₀`-subalgebra `T₁ ⊆ A`. It also gives a scheme `X₀`
     that is locally of finite presentation, quasi-compact and quasi-separated over
     `Spec T₁`, with `G.X.left` the pullback of `X₀`.
  3. The Library's `GroupScheme.subalgebraDescent`
     ([`GroupSchemeSubalgebraDescentProof`](../../AbelianScheme/GroupSchemeSubalgebraDescentProof.md))
     gives a finitely generated `T₁`-subalgebra `T₂ ⊆ A`, a group `G₀` over `Spec T₂` and
     an isomorphism from `G` to the base change of `G₀`. `G₀ → Spec T₂` is a base change of
     `X₀ → Spec T₁` (`IsPullback`), hence locally of finite presentation
     (`MorphismProperty.of_isPullback`).
  4. `H₀ = D_{Spec T₂}(Λ)` is diagonalizable, hence of multiplicative type. It is affine
     over its base by the Library's `isAffineHom_diagonalizable`
     ([`RelativeMultiplicativeTypeGeometry`](RelativeMultiplicativeTypeGeometry.md)), so
     it is quasi-compact and quasi-separated. `H` is isomorphic to its base change by
     `diagonalizableBaseChangeIso`.
  5. Conjugate `u, v` by these isomorphisms (`FibreHyp.conj`, `LocalEq.of_conj`) and apply
     `spec_core` with `R = T₂`.

## Proof of `multiplicativeTypeCentralRigidityNoetherianReduction`

Let `hyp` be the hypothesis of the statement. Take `S, H, G` with `H` of multiplicative type
and `G` of finite presentation, `u, v : H ⟶ G`, `s ∈ S`, `u_s = v_s` and `u_s` central.

1. `hyp` gives `NoetherianHyp` directly.
2. `IsMultiplicativeType H` gives a cover `𝒰` of `S` by morphisms that are flat and locally
   of finite presentation, with each `𝒰.f i^* H` diagonalizable. By `Cover.exists_eq`, pick
   `i` and `t ∈ 𝒰.X i` with `𝒰.f i t = s`.
3. Pick a member `a : Spec (𝒱.X j) ⟶ 𝒰.X i` of the affine open cover
   `𝒱 = (𝒰.X i).affineOpenCover` and `w` with `a w = t`. Set `f = a ≫ 𝒰.f i`. It is flat and
   locally of finite presentation, being an open immersion followed by `𝒰.f i`, and
   `f w = s`.
4. `f^* H` is diagonalizable: it is isomorphic (`pullbackComparison`) to the base change
   along `a` of the diagonalizable `𝒰.f i^* H` (`IsDiagonalizable.baseChange`, `of_iso`).
   `f^* G → Spec (𝒱.X j)` is a base change of `G → S`. So it is locally of finite
   presentation, quasi-compact and quasi-separated.
5. `FibreHyp.pull f w` gives `FibreHyp` of `f^*u, f^*v` at `w`. `spec_case` gives
   `LocalEq` of `f^*u, f^*v` at `w`, and `LocalEq.descend f w` gives `LocalEq u v (f w)`,
   that is, an open `U ∋ s` with `u_U = v_U`.

## Relation to the source

SGA 3, IX, proof of Théorème 5.1 b) (Gille–Polo recomposed edition, p.49), makes `S` local
and then passes to a faithfully flat extension over which `H` is diagonalizable. It writes
the local ring as the filtered union of its finitely generated `ℤ`-subalgebras, descends `G`,
`u` and `v`, and applies case a) over a noetherian base. This module uses the same
ingredients: the faithfully flat diagonalizing cover, descent to a finitely generated
subalgebra, fibres at the image point and case a). It does not localize. It works on an
affine chart of an fppf cover and transports open neighbourhoods by openness of flat
morphisms locally of finite presentation (`LocalEq.descend`). Fibres are compared along the
residue field extension `κ(s_i) ⟶ κ(s)` (`FibreHyp.descend`), as in the source.

## Axioms

`lean_check` inspection of `multiplicativeTypeCentralRigidityNoetherianReduction` reports
only `propext`, `Classical.choice` and `Quot.sound`.
