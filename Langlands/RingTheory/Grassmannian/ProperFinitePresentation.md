# The represented quotient Grassmannian is proper and of finite presentation

The theorem
`Module.Grassmannian.exists_scheme_represents_isProper_locallyOfFinitePresentation`
states that for a finite projective module the quotient Grassmannian is represented by
a scheme that is proper and locally of finite presentation over the base. Each
representing scheme that comes with the Library's affine chart cover has these two
properties.

## Provenance

This module is internal supporting content for the task proving
`Langlands.GroupScheme.SelfNormalizingProperAmbientStatement`. There, the ambient
scheme of a self-normalizing subgroup is a Grassmannian of quotients of a finite
projective module of jets. The statements are derived from the Library modules
`Langlands.RingTheory.Grassmannian.Representability`,
`Langlands.RingTheory.Grassmannian.Charts` and
`Langlands.RingTheory.Grassmannian.ProjectiveEmbedding`. Algebraic geometry has long
known that Grassmannians are proper and of finite presentation over the base. The
proofs here are new Lean proofs built on those Library modules; they port no outside
source.

## Conventions

The universe is `u`, and `R`, `M` and every test algebra lie in it. For a commutative
`R`-algebra `A`, `Module.Grassmannian A (A ⊗[R] M) k` is Mathlib's type of submodules
whose **quotients** are finite projective of constant rank `k`, and base change is
`Module.Grassmannian.map`. `IsProper` and `LocallyOfFinitePresentation` are Mathlib's
scheme morphism properties.

## Declarations

### Algebra

- `Algebra.FinitePresentation.of_retract`: let `A` be a finitely presented `R`-algebra
  and let `f : A →ₐ[R] B` and `g : B →ₐ[R] A` satisfy `f.comp g = AlgHom.id R B`. Then
  `B` is finitely presented over `R`.
- `SymmetricAlgebra.finitePresentation_of_projective`: if `M` is finite and projective
  over `R`, then `SymmetricAlgebra R M` is finitely presented over `R`.
- `Module.Grassmannian.ChartAlgebra.finitePresentation`: if `M` is finite projective,
  then for every `x : Fin k → M` the chart algebra `ChartAlgebra.S R x` is finitely
  presented over `R`. This algebra is the quotient of `SymmetricAlgebra R (Fin k → M)`
  by the span of `ChartAlgebra.rels R x`.

### The affine charts of a representing scheme

The declarations below live in the namespace `Module.Grassmannian.ProjectiveEmbedding`.
They use its structure `Rep R M k`, which bundles a representing scheme `D.Gr`, the
structure morphism `D.p`, the point equivalences `D.pt` with their naturality `D.hpt`,
and the chart cover `D.V` with `D.hV`, `D.hVaff` and `D.hVchart`. For a chart index `x`,
`S D x` is the ring of sections `Γ(D.Gr, D.V x)`.

- `chartClassifier x A` is the equivalence from the standard chart points `Chart R x A`
  to `ChartAlgebra.S R x →ₐ[R] A`. It composes `ChartLinear.chartEquiv` with
  `ChartAlgebra.homEquivPt`. `chartClassifier_map` shows that it commutes with base
  change along every `φ : A →ₐ[R] B`.
- `univChart x` is the chart point over `ChartAlgebra.S R x` classified by the identity.
- `toChartAlg D x : ChartAlgebra.S R x →ₐ[R] S D x` classifies the chart point `NS D x`,
  the point whose morphism is the affine chart inclusion `gS D x`.
- `univSpecLift D x` is the factorization of the morphism of `univChart x` through the
  open immersion `gS D x`. `univSpecLift_fac` and `univSpecLift_over` state that it
  factors that morphism and lies over `Spec R`.
- `fromChartAlg D x : S D x →ₐ[R] ChartAlgebra.S R x` is an algebra map whose `Spec` is
  `univSpecLift D x` (`specMap_fromChartAlg`).
- `fromChartAlg_comp_toChartAlg` and `toChartAlg_comp_fromChartAlg` show that the two
  maps are mutually inverse, and `chartAlgEquiv D x : S D x ≃ₐ[R] ChartAlgebra.S R x` is
  the resulting algebra equivalence.
- `finitePresentation_S`: if `M` is finite projective, then `S D x` is finitely
  presented over `R`.
- `Rep.locallyOfFinitePresentation_p`: if `M` is finite projective, then `D.p` is
  locally of finite presentation.
- `Rep.isProper_p`: if `M` is finite (projectivity is not needed), then `D.p` is
  proper.

### Export

`Module.Grassmannian.exists_scheme_represents_isProper_locallyOfFinitePresentation R M k`
takes `R : Type u` a commutative ring, `M : Type u` an `R`-module that is finite and
projective, and `k : ℕ`. It produces a scheme `Gr`, a morphism
`p : Gr ⟶ Spec (CommRingCat.of R)` and, for every commutative `R`-algebra `A`, an
equivalence

```
pt A : Module.Grassmannian A (A ⊗[R] M) k ≃
  {g : Spec (CommRingCat.of A) ⟶ Gr // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))}
```

such that

1. for every `φ : A →ₐ[R] B` and every `N`,
   `(pt B (Module.Grassmannian.map φ N)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1`;
2. `IsProper p`;
3. `LocallyOfFinitePresentation p`.

The data `Gr`, `p` and `pt` have exactly the shape of the output of
`Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover`. The export
does not include the chart cover.

## Proof

**Retracts.** Take a finite generating set `s` of `A`. The map `f` is surjective, since
`f (g b) = b`. Its kernel is the ideal `I` spanned by the finitely many elements
`a - g (f a)` for `a ∈ s`. These lie in the kernel. Conversely, the quotient map by `I`
and its composite with `g.comp f` agree on the generators `s`, so they agree everywhere
(`AlgHom.ext_of_adjoin_eq_top`). Hence each `a` with `f a = 0` maps to `0` modulo `I`.
`Algebra.FinitePresentation.of_surjective` then concludes.

**Symmetric algebras.** `Module.Finite.exists_comp_eq_id_of_projective` gives
`f : (Fin n → R) →ₗ[R] M` and `g : M →ₗ[R] (Fin n → R)` with `f ∘ g = id`. The universal property
`SymmetricAlgebra.lift` turns them into algebra maps between `SymmetricAlgebra R M` and
`SymmetricAlgebra R (Fin n → R)` whose composite is the identity of the first. This is
checked on generators with `SymmetricAlgebra.algHom_ext`. The algebra
`SymmetricAlgebra R (Fin n → R)` is isomorphic to a polynomial ring in `n` variables by
`SymmetricAlgebra.equivMvPolynomial`, so it is finitely presented. The retract lemma
finishes the proof.

**Chart algebras.** `Fin k → M` is again finite projective, so its symmetric algebra
is finitely presented. The relation set `rels R x` is the image of the finite set
`Fin k × Fin k`, so `Algebra.FinitePresentation.quotient` applies.

**Chart coordinate rings.** The universal chart point `univChart x` lies in the chart.
By `D.hVchart`, the image of its morphism lies in `D.V x`, so the morphism factors
through `gS D x` as `univSpecLift D x`. This factorization lies over `Spec R`, and
`exists_algHom` writes it as `Spec` of `fromChartAlg D x`.

- **First composite.** Base change of `NS D x` along `fromChartAlg D x` has the same
  morphism as `univChart x` (`map_eq_of_pt`). Its classifying map is therefore the
  identity. By `chartClassifier_map` that classifying map is
  `(fromChartAlg D x).comp (toChartAlg D x)`.
- **Second composite.** Base change of `univChart x` along `toChartAlg D x` has
  classifying map `toChartAlg D x`, so it equals `NS D x`, because `chartClassifier` is
  injective. Applying `D.hpt`, the `Spec` of `(toChartAlg D x).comp (fromChartAlg D x)`
  composed with the open immersion `gS D x` equals `gS D x`. Cancelling the
  monomorphism `gS D x` and using that `Spec.map` is injective, this composite is the
  identity.

**Finite presentation of `p`.** `D.V` is an open cover. Mathlib provides
`IsZariskiLocalAtSource` for `LocallyOfFinitePresentation` through
`HasRingHomProperty`. Instance search does not find it in this file, so the proof
supplies `HasRingHomProperty.instIsZariskiLocalAtSource` explicitly. By
`IsZariskiLocalAtSource.of_iSup_eq_top` it suffices to treat `(D.V x).ι ≫ D.p`. By
`sV_gS` and `specMap_algebraMap_S`, this composite is the isomorphism `sV D x` followed
by `Spec` of `algebraMap R (S D x)`.

- **The second factor.** It is locally of finite presentation by
  `HasRingHomProperty.Spec_iff`, `RingHom.finitePresentation_algebraMap` and
  `finitePresentation_S`.
- **The isomorphism.** It is an open immersion and therefore locally of finite
  presentation. `locallyOfFinitePresentation_comp` concludes.

**Properness of `p`.** `Module.Grassmannian.exists_isClosedImmersion_toProjSpace_of_represents`
gives `m` and a closed immersion `ι : D.Gr ⟶ ProjSpace R m` with
`ι ≫ ProjSpace.π R m = D.p`. The morphism `ProjSpace.π R m` is definitionally
`projectiveSpaceToSpec R m`, which is proper by
`Langlands.AlgebraicGeometry.projectiveSpaceToSpec_isProper`. A closed immersion is
proper, so the composite is proper.

**Export.** Apply `exists_scheme_represents_and_isAffineOpen_chart_cover R M k` and
bundle its output as `D : Rep R M k`. Then return `D.Gr`, `D.p`, `D.pt`, `D.hpt`,
`D.isProper_p` and `D.locallyOfFinitePresentation_p`.
