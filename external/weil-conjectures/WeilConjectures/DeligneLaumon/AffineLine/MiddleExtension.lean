/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Perverse

/-!
# Irreducible middle extensions under the Fourier transform

The simple objects of the curve perverse heart are the punctual ones and the middle extensions
`(j_*M)[1]` of irreducible lisse sheaves. The Fourier transform preserves simplicity, and the
inverse transform of a punctual object is geometrically a sum of shifted linear Artin–Schreier
sheaves. So, as soon as no geometric irreducible constituent of `M` is a linear character
`ℒ_{ψ(a x)}`, the transform of `(j_*M)[1]` is again a middle extension `(j'_*M')[1]` on the
dual line. Such an `M` is called *nonexceptional*.

A nonzero linear character is ramified at infinity: inertia at infinity acts on the
Artin–Schreier cover `u^q - u = a x` by all translations `u ↦ u + c`, `c ∈ 𝔽_q`
(`LaurentSeries.exists_algEquiv_apply_eq_add_C_of_pow_sub_eq_single`), hence on `ℒ_{ψ(a x)}`
through the nontrivial character `ψ`. The trivial linear character would make `M`
geometrically constant, so an irreducible `M` that is unramified at infinity and not
geometrically constant is automatically nonexceptional. Only arithmetic irreducibility is
assumed: restriction to the normal geometric subgroup of the Weil group is semisimple.

Nonexceptionality quantifies over the elements of `AlgebraicClosure k₀` rather than over an
arbitrary algebraically closed extension: any two algebraic closures of `k₀` are isomorphic
over `k₀`, so nothing is lost, and the condition becomes a property of `M` alone.

The proof that the transform is a middle extension runs in the curve perverse heart: `(j_*M)[1]`
is simple there (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.simple_middleExtension`), the
transform preserves simple objects (`AlgebraicGeometry.simple_fourierTransform_obj`), the simple
objects are punctual or middle extensions (`AlgebraicGeometry.WeilComplex.simple_iff`),
and nonexceptionality excludes the punctual case.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.IsNonexceptional`: the nonexceptionality condition, on the
  geometric irreducible constituents.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.IsFourierNonexceptional`: the condition on the
  whole geometric sheaf, and its comparison
  `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isFourierNonexceptional_of_isNonexceptional`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.IsFourierPartner`: the relation
  `FT_ψ((j_*M)[1]) ≃ (j'_*M')[1]` between a datum and its transform.
- `AlgebraicGeometry.exists_middleExtension_fourierTransform`: the transform of an irreducible
  nonexceptional middle extension is a middle extension.
- `AlgebraicGeometry.isNonexceptional_of_isUnramifiedAtInfinity`: the nonexceptionality test.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- A lisse Weil sheaf `M` on `U₀` is *nonexceptional* if none of its geometric irreducible
constituents is a linear Artin–Schreier sheaf `ℒ_{ψ(a x)}|_U`, for any `a` in the algebraic
closure of `k₀`, the value `a = 0` included; for `a = 0` the excluded constituent is the trivial
rank-one sheaf. (blueprint: `proposition-fourier-transform-middle-extension`) -/
def IsNonexceptional {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) (ψ : AddChar k₀ (PadicAlgCl l)) (j : U ⟶ affineLine k₀)
    [j.IsOver (Spec (CommRingCat.of k₀))] : Prop :=
  ∀ a : AlgebraicClosure k₀, ¬ F.HasLinearArtinSchreierConstituent ψ a j

/-- The middle extension `j_*M` of a lisse sheaf `M` on a dense open `j : U₀ ↪ 𝔸¹` is
*Fourier-nonexceptional* if after geometric base change it is neither a constant sheaf (up to a
constant Weil twist) nor the Artin–Schreier sheaf `ℒ_{ψ(a x)}` for any `a ∈ k`.

The condition is phrased on `U`, using `j^* j_* M = M` and `j_*(ℒ|_U) = ℒ` for `ℒ` lisse on the
whole line: `M_k̄` is not constant, and it is not isomorphic to `ℒ_{ψ(a x)}|_U`. The latter
isomorphism is phrased as "`M_k̄` is irreducible and `ℒ_{ψ(a x)}|_U` is a constituent of it",
which is equivalent since the Artin–Schreier sheaves are irreducible.
(blueprint: `def-fd-nonexceptional`) -/
def LisseOnDenseOpen.IsFourierNonexceptional (ψ : AddChar k₀ (PadicAlgCl l))
    (D : LisseOnDenseOpen k₀ l) : Prop :=
  ¬ D.IsGeometricallyConstant ∧ ∀ a : AlgebraicClosure k₀,
    ¬ (D.sheaf.IsGeometricallyIrreducible ∧ D.sheaf.HasLinearArtinSchreierConstituent ψ a D.j)

/-- `D'` is a *Fourier partner* of `D` if the Fourier transform of the curve perverse middle
extension `(j_*M)[1]` of `D` is the middle extension `(j'_*M')[1]` of `D'`.
(blueprint: `proposition-fourier-transform-middle-extension`) -/
def LisseOnDenseOpen.IsFourierPartner (ψ : AddChar k₀ (PadicAlgCl l))
    (D D' : LisseOnDenseOpen k₀ l) : Prop :=
  Nonempty ((fourierTransform ψ).obj D.middleExtension ≅ D'.middleExtension)

namespace LisseOnDenseOpen

variable (ψ : AddChar k₀ (PadicAlgCl l)) (D : LisseOnDenseOpen k₀ l)

/-- **Constituent-nonexceptional implies Fourier-nonexceptional.** If no geometric constituent
of the irreducible lisse sheaf `M` is a linear character `ℒ_{ψ(a x)}|_U`, then `M_k̄` is neither
constant, since a nonzero constant sheaf has the trivial constituent `ℒ_{ψ(0 · x)}`, nor
isomorphic to some `ℒ_{ψ(a x)}|_U`, which would be its constituent.
(blueprint: `lem-a1-constituent-nonexceptional-comparison`, part 1) -/
theorem isFourierNonexceptional_of_isNonexceptional (hD : D.sheaf.IsIrreducibleLisse)
    (h : D.sheaf.IsNonexceptional ψ D.j) : D.IsFourierNonexceptional ψ :=
  ⟨fun hc ↦ h 0 (D.hasLinearArtinSchreierConstituent_zero_of_isGeometricallyConstant ψ hD.2.1 hc),
    fun a ha ↦ h a ha.2⟩

/-- **For geometrically irreducible sheaves the two notions coincide.** If `M_k̄` is
irreducible, its only geometric constituent is `M_k̄` itself, so a constituent `ℒ_{ψ(a x)}|_U`
would be isomorphic to `M_k̄`. (blueprint: `lem-a1-constituent-nonexceptional-comparison`) -/
theorem isNonexceptional_iff_isFourierNonexceptional (hD : D.sheaf.IsIrreducibleLisse)
    (hirr : D.sheaf.IsGeometricallyIrreducible) :
    D.sheaf.IsNonexceptional ψ D.j ↔ D.IsFourierNonexceptional ψ :=
  ⟨D.isFourierNonexceptional_of_isNonexceptional ψ hD, fun h a ha ↦ h.2 a ⟨hirr, ha⟩⟩

/-- A lisse sheaf unramified at infinity has no geometric constituent `ℒ_{ψ(a x)}|_U` with
`a ≠ 0`: on the punctured disc at `∞` the sheaf becomes constant, so such a constituent would be
a subquotient of a constant sheaf there, while the inertia group at `∞` acts on `ℒ_{ψ(a x)}`
through the nontrivial character `ψ`
(the primed variant, `not_hasLinearArtinSchreierConstituent_of_isUnramifiedAtInfinity'`,
which needs no irreducibility). (blueprint: `lemma-unramified-at-infinity-no-linear-characters`,
case `a ≠ 0`) -/
theorem not_hasLinearArtinSchreierConstituent_of_isUnramifiedAtInfinity (hψ : ψ ≠ 1)
    (_hD : D.sheaf.IsIrreducibleLisse) (hinf : D.IsUnramifiedAtInfinity)
    {a : AlgebraicClosure k₀} (ha : a ≠ 0) :
    ¬ D.sheaf.HasLinearArtinSchreierConstituent ψ a D.j :=
  D.not_hasLinearArtinSchreierConstituent_of_isUnramifiedAtInfinity' ψ hψ hinf ha

/-- **The punctual case is excluded.** For `M` irreducible lisse and nonexceptional, the
transform of `(j_*M)[1]` is not a sheaf of finite support in degree `0`: otherwise inverting the
transform gives `(j_*M)[1](-1) ≅ FT_{ψ⁻¹}(G)`, whose underlying geometric sheaf is a sum of
linear characters `ℒ_{ψ(a x)}` over the geometric points of the support of `G`, so that `M_k̄`
would surject onto some `ℒ_{ψ(a x)}|_U`
(`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.exists_hasLinearArtinSchreierConstituent_of_iso`).
(blueprint: `proposition-fourier-transform-middle-extension--1`, Steps 2 and 3) -/
theorem isEmpty_iso_fourierTransform_middleExtension_toComplex (hψ : ψ ≠ 1)
    (hD : D.sheaf.IsIrreducibleLisse) (hne : D.sheaf.IsNonexceptional ψ D.j)
    (G : WeilSheaf k₀ l (affineLine k₀)) (hG : (WeilSheaf.support G).Finite) :
    IsEmpty ((fourierTransform ψ).obj D.middleExtension ≅ WeilSheaf.toComplex.obj G) := by
  refine ⟨fun e ↦ ?_⟩
  obtain ⟨a, ha⟩ := D.exists_hasLinearArtinSchreierConstituent_of_iso ψ hψ hD.2.1 G hG e
  exact hne a ha

end LisseOnDenseOpen

end WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable (ψ : AddChar k₀ (PadicAlgCl l))

/-- **The transform of an irreducible nonexceptional middle extension.** If `M` is a nonzero
irreducible lisse Weil sheaf on a dense open `U₀` of the affine line and is nonexceptional for a
nontrivial `ψ`, then there are a dense open `j' : U'₀ ↪ A'₀` of the dual line and an irreducible
lisse Weil sheaf `M'` on it whose middle extension is the transform:

```
    U₀ ──j──▶ 𝔸¹              U'₀ ──j'──▶ 𝔸'¹
     M                          M'

               FT_ψ
    (j_*M)[1] ──────≃──────▶ (j'_*M')[1]
```
Irreducibility is meant among lisse sheaves (`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse`),
not simplicity in the category of all Weil sheaves: a nonzero lisse sheaf on a curve is never
simple there. A lisse `M` with `[Simple M]` is irreducible lisse by
`AlgebraicGeometry.WeilSheaf.IsLisse.isIrreducibleLisse`.

The object `(j_*M)[1]` is simple in the curve perverse heart, hence so is its transform; a simple
perverse object is punctual or a middle extension, and the punctual case is excluded by
nonexceptionality. (blueprint: `proposition-fourier-transform-middle-extension`,
`proposition-fourier-transform-middle-extension--1`) -/
theorem exists_middleExtension_fourierTransform (hψ : ψ ≠ 1)
    (D : WeilSheaf.LisseOnDenseOpen k₀ l) (hD : D.sheaf.IsIrreducibleLisse)
    (hne : D.sheaf.IsNonexceptional ψ D.j) :
    ∃ D' : WeilSheaf.LisseOnDenseOpen k₀ l, D'.sheaf.IsIrreducibleLisse ∧
      D.IsFourierPartner ψ D' := by
  have := D.simple_middleExtension hD
  have := simple_fourierTransform_obj ψ hψ ⟨D.middleExtension, D.isCurvePerverse_middleExtension⟩
  rcases (WeilComplex.simple_iff ⟨(fourierTransform ψ).obj D.middleExtension,
      (isCurvePerverse_fourierTransform_obj_iff ψ hψ _).2 D.isCurvePerverse_middleExtension⟩).1
        this with ⟨G, -, hG, ⟨e⟩⟩ | ⟨D', hD', ⟨e⟩⟩
  · exact ((D.isEmpty_iso_fourierTransform_middleExtension_toComplex ψ hψ hD hne G hG).false
      e).elim
  · exact ⟨D', hD', ⟨e⟩⟩

/-- An irreducible lisse Weil sheaf on a dense open of the affine line which is unramified at
infinity and not geometrically constant is nonexceptional: the nonzero linear characters are
excluded by their ramification at infinity, and a geometric constant constituent of an
irreducible Weil representation forces geometric constancy. Only arithmetic irreducibility is
used. (blueprint: `proposition-fourier-transform-middle-extension`,
`lemma-unramified-at-infinity-no-linear-characters`) -/
theorem isNonexceptional_of_isUnramifiedAtInfinity (hψ : ψ ≠ 1)
    (D : WeilSheaf.LisseOnDenseOpen k₀ l) (hD : D.sheaf.IsIrreducibleLisse)
    (hinf : D.IsUnramifiedAtInfinity) (hconst : ¬ D.IsGeometricallyConstant) :
    D.sheaf.IsNonexceptional ψ D.j := by
  intro a ha
  rcases eq_or_ne a 0 with rfl | ha0
  · exact hconst (D.isGeometricallyConstant_of_hasLinearArtinSchreierConstituent_zero ψ hD ha)
  · exact D.not_hasLinearArtinSchreierConstituent_of_isUnramifiedAtInfinity ψ hψ hD hinf ha0 ha

end AlgebraicGeometry
