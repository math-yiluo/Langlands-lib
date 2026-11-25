/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.WeilSheaf.Defs

/-!
# Lisse Weil sheaves on a dense open of the affine line

This file fixes the conventions of the Deligne–Laumon affine-line estimate
(`WeilConjectures.DeligneLaumon.AffineLine.Upper`) and of its auxiliary statements, following
the blueprint subsection `lemma-unramified-at-infinity-no-linear-characters--1`. The `ℓ`-adic
formalism they are phrased against is the provisional interface of `WeilConjectures.WeilSheaf.Defs`;
what this block owns is the two conditions on a lisse Weil sheaf on a dense open of the affine line,
and the bundling of that situation.

The affine line `A₀ = 𝔸¹_{k₀}` is `AlgebraicGeometry.affineLine k₀`, and the dual affine line
`A'₀` of the Fourier transform is another copy of it. It sits in `ℙ¹_{k₀}` through the standard
chart `AlgebraicGeometry.ProjectiveLine.affineChart`, `x ↦ [x : 1]`, whose complement is the
point `∞ = [1 : 0]`.

Both conditions are phrased without the geometric fundamental group, which does not exist in
the repository yet. Geometric constancy asks that the underlying `ℓ`-adic sheaf be constant,
a finite sum of copies of `ℚ̄_ℓ`, on every connected open of the geometric fiber
`Ū = U ⊗ k̄`. Being unramified at infinity asks that the sheaf extend to a lisse Weil sheaf on
`U₀ ∪ {∞} ⊆ ℙ¹_{k₀}`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant`: constancy on the geometric fiber.
- `AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity`: extension to a lisse sheaf at `∞ ∈ ℙ¹`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen`: a dense open immersion `j : U₀ ↪ 𝔸¹_{k₀}`
  together with a lisse Weil sheaf on `U₀`, with its direct image, its extension by zero, its
  boundary sheaf, its curve perverse middle extension and the map
  `j_!M[1] ⟶ j_*M[1]` (`shiftedExtensionByZeroToMiddleExtension`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

open scoped ProEtale

namespace WeilSheaf

section Infinity

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]

/-- A Weil sheaf `F` on `U` is *geometrically constant* if its underlying `ℓ`-adic sheaf is
constant on every connected open `V` of the geometric fiber `Ū = U ⊗ k̄`, where `k̄` is an
algebraic closure of `k₀`: its restriction to `V` is a finite direct sum of copies of the
constant `ℓ`-adic sheaf `ℚ̄_ℓ`. Its Frobenius module may still be nontrivial. When the connected
components of `Ū` are open, for instance when `U` is of finite type over `k₀`, this says that
`F` is constant on each connected component of `Ū`. For `Ū` connected, as for `U` an open of
`𝔸¹_{k₀}`, it is the constancy of `F` on `Ū`, which motivates the definition: the geometric
fundamental group `π₁(Ū)` acts trivially on the stalks of `F`.
(blueprint: `lemma-unramified-at-infinity-no-linear-characters--1`) -/
def IsGeometricallyConstant (F : WeilSheaf k₀ l U) : Prop :=
  ∀ V : (U ↘ Spec (CommRingCat.of k₀)).geometricFiber.Opens, ConnectedSpace V →
    ∃ n : ℕ, Nonempty ((V.ι)^*ᵃ[l].obj F.obj.carrier ≅
      ⨁ fun _ : Fin n ↦ ProEtale.AdicSheaf.unit l V.toScheme)

/-- A lisse Weil sheaf `F` on an open `U₀` of the affine line, embedded by `j : U₀ ↪ 𝔸¹`, is
*unramified at infinity* if it extends to a lisse Weil sheaf on `U₀ ∪ {∞} ⊆ ℙ¹`. Here `𝔸¹`
sits in `ℙ¹` through the standard chart `ι = ProjectiveLine.affineChart`, whose complement is
the point `∞`, and the extension is a lisse Weil sheaf `G` on an open `W ⊆ ℙ¹` with
`ι.opensRange ⊔ W = ⊤` (that is, `∞ ∈ W`) and `ι⁻¹(W) = U₀`, together with an isomorphism
`j'^* G ≅ F` along the factorization `j'` of `j ≫ ι` through `W`:
```
  U₀ ──j'──▶ W
  │          │
  j          W.ι
  ▼          ▼
  𝔸¹ ──ι───▶ ℙ¹
```
The choice of chart does not matter: two open immersions `𝔸¹ ↪ ℙ¹` of `k₀`-schemes differ by
a `k₀`-automorphism of `ℙ¹`. This condition is equivalent to the inertia group at `∞` acting
trivially on the geometric generic fiber of `F`.
(blueprint: `lemma-unramified-at-infinity-no-linear-characters--1`) -/
def IsUnramifiedAtInfinity (F : WeilSheaf k₀ l U) (j : U ⟶ affineLine k₀) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] : Prop :=
  let ι := ProjectiveLine.affineChart (Spec (CommRingCat.of k₀))
  ∃ (W : (ProjectiveLine (Spec (CommRingCat.of k₀))).Opens) (hW : ι ⁻¹ᵁ W = j.opensRange),
    ι.opensRange ⊔ W = ⊤ ∧ ∃ G : WeilSheaf k₀ l W, G.IsLisse ∧
      Nonempty ((WeilSheaf.upperStar (IsOpenImmersion.lift W.ι (j ≫ ι) (by
        rintro _ ⟨x, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (hW ▸ j.mem_opensRange.2 ⟨x, rfl⟩ : j x ∈ ι ⁻¹ᵁ W)))).obj G ≅ F)

end Infinity

/-- The standing situation of the affine-line estimate: a dense open immersion
`j : U₀ ↪ 𝔸¹_{k₀}` together with a lisse Weil `ℚ̄_ℓ`-sheaf on `U₀`. Bundling the data avoids
carrying six instance arguments through every statement, and makes the existential statements
of the block — which produce a new dense open of the dual line — readable. -/
structure LisseOnDenseOpen (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] where
  /-- The dense open subscheme `U₀`. -/
  U : Scheme.{u}
  [overBase : U.Over (Spec (CommRingCat.of k₀))]
  /-- The open immersion `j : U₀ ↪ 𝔸¹_{k₀}`. -/
  j : U ⟶ affineLine k₀
  [isOpenImmersion : IsOpenImmersion j]
  [quasiCompact : QuasiCompact j]
  [isOver : j.IsOver (Spec (CommRingCat.of k₀))]
  [isDominant : IsDominant j]
  /-- The lisse Weil sheaf on `U₀`. -/
  sheaf : WeilSheaf k₀ l U
  /-- The sheaf is lisse. -/
  lisse : sheaf.IsLisse

namespace LisseOnDenseOpen

attribute [instance] overBase isOpenImmersion quasiCompact isOver isDominant

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable (D : LisseOnDenseOpen k₀ l)

/-- The sheaf of the datum is unramified at infinity. -/
def IsUnramifiedAtInfinity : Prop := D.sheaf.IsUnramifiedAtInfinity D.j

/-- The sheaf of the datum is geometrically constant. -/
def IsGeometricallyConstant : Prop := D.sheaf.IsGeometricallyConstant

/-- The ordinary direct image `j_*M` of the datum, a Weil sheaf on the whole affine line. -/
noncomputable def directImage : WeilSheaf k₀ l (affineLine k₀) :=
  (WeilSheaf.directImage D.j).obj D.sheaf

/-- The extension by zero `j_!M` of the datum. -/
noncomputable def extensionByZero : WeilSheaf k₀ l (affineLine k₀) :=
  (WeilSheaf.extensionByZero D.j).obj D.sheaf

/-- The curve perverse middle extension `j_{!*}(M[1]) = (j_*M)[1]` of the datum. -/
noncomputable def middleExtension : WeilComplex k₀ l (affineLine k₀) :=
  (WeilSheaf.toComplex.obj D.directImage)⟦(1 : ℤ)⟧

/-- The boundary sheaf `B = j_*M / j_!M`: the cokernel of the canonical map `j_!M → j_*M`, a
punctual sheaf supported on the finite complement of `U₀`. -/
noncomputable def boundarySheaf : WeilSheaf k₀ l (affineLine k₀) :=
  Limits.cokernel ((WeilSheaf.extensionByZeroToDirectImage D.j).app D.sheaf)

/-- The shifted zero extension `j_!M[1]`, a curve perverse sheaf. -/
noncomputable def shiftedExtensionByZero : WeilComplex k₀ l (affineLine k₀) :=
  (WeilSheaf.toComplex.obj D.extensionByZero)⟦(1 : ℤ)⟧

/-- The shift `j_!M[1] ⟶ j_*M[1] = j_{!*}(M[1])` of the canonical map `j_!M ⟶ j_*M`, the middle
arrow of the rotated triangle `B ⟶ j_!M[1] ⟶ j_*M[1] ⟶ B[1]`. -/
noncomputable def shiftedExtensionByZeroToMiddleExtension :
    D.shiftedExtensionByZero ⟶ D.middleExtension :=
  (WeilSheaf.toComplex.map ((WeilSheaf.extensionByZeroToDirectImage D.j).app D.sheaf))⟦(1 : ℤ)⟧'

end LisseOnDenseOpen

end WeilSheaf

end AlgebraicGeometry
