import Langlands.Automorphic.AutomorphicAdmissibilityStatement
import Langlands.Automorphic.IrreducibleOperatorSubquotient
import Langlands.Automorphic.OperatorSubquotientPlaceAction
import Langlands.Automorphic.OperatorSubquotientLieAction
import Langlands.Representation.Archimedean.GKModule
import Langlands.Correspondence.AutomorphicRelations
import Langlands.Global.CompletionPadic

/-!
# Local components of automorphic representations of `GL_n`

Getz–Hahn (2024), Definition 6.3.5, Lemma 6.3.6 and Theorem 6.3.7, and Flath (1979),
Theorem 3, for `GL_(r+1)` over a number field `F`, read through the restriction of an
automorphic representation to one place.

* `Archimedean.gkHoms ρ π ρ' π'`: the linear maps intertwining two compact actions and two
  Lie algebra actions.
* `Archimedean.IsGKIsotypic ρ π ρ' π'`: the target is spanned by the images of these maps.
* `OperatorSubquotient.IsFinitePlaceIsotypic Q v ρ`: the restriction of `Q` to
  `GL_n(F_v)` is spanned by the images of the intertwining maps from `ρ`.
* `OperatorSubquotient.IsRealPlaceIsotypic Q v ρ π`,
  `OperatorSubquotient.IsComplexPlaceIsotypic Q v ρ π`: the same for the compact action
  of `O(n)` or `U(n)` and the complexified Lie action at an infinite place `v`.
* `LocalComponentExistenceStatement`: an irreducible jointly admissible operator
  subquotient is isotypic at every finite place for an irreducible admissible smooth
  representation of `GL_(r+1)(F_v)`, and at every infinite place for an irreducible
  admissible `(𝔤, K)`-module.
* `LocalComponentEmbeddingStatement`: for such a subquotient and an irreducible local
  representation `ρ`, the restriction is `ρ`-isotypic exactly when `ρ` has a nonzero
  intertwining map into it.
* `LocalComponentDeterminationStatement`: two such subquotients are equivalent exactly when
  at every place some irreducible local representation is a local component of both.

None of the statements is proved here.
-/

noncomputable section
universe u uV uW

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Archimedean

section GKHoms

variable {K : Type*} [Group K] {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The linear maps `f : V → W` intertwining the compact actions `ρ`, `ρ'` and the Lie
actions `π`, `π'`: `f (ρ k x) = ρ' k (f x)` and `f (π X x) = π' X (f x)`. -/
def gkHoms (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ρ' : Representation ℂ K W) (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W) :
    Submodule ℂ (V →ₗ[ℂ] W) where
  carrier := {f | (∀ (k : K) (x : V), f (ρ k x) = ρ' k (f x)) ∧
    ∀ (X : L) (x : V), f (π X x) = π' X (f x)}
  zero_mem' := ⟨fun k x => by simp, fun X x => by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    exact ⟨fun k x => by simp [hf k x, hg k x], fun X x => by simp [hf' X x, hg' X x]⟩
  smul_mem' := by
    rintro c f ⟨hf, hf'⟩
    exact ⟨fun k x => by simp [hf k x], fun X x => by simp [hf' X x]⟩

theorem mem_gkHoms (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ρ' : Representation ℂ K W) (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W) (f : V →ₗ[ℂ] W) :
    f ∈ gkHoms ρ π ρ' π' ↔ (∀ (k : K) (x : V), f (ρ k x) = ρ' k (f x)) ∧
      ∀ (X : L) (x : V), f (π X x) = π' X (f x) :=
  Iff.rfl

/-- `(W, ρ', π')` is `(V, ρ, π)`-isotypic: `W` is spanned by the images of the maps in
`gkHoms ρ π ρ' π'`. -/
def IsGKIsotypic (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ρ' : Representation ℂ K W) (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W) : Prop :=
  ⨆ f ∈ gkHoms ρ π ρ' π', LinearMap.range f = ⊤

end GKHoms

end Archimedean

namespace Automorphic

open Langlands.Global
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)

local instance localComponentRationalGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance localComponentContinuousGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance localComponentSmoothGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance localComponentFormGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance localComponentStableGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance localComponentRealizationGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The canonical matrix topology on `GL_n(F_v)`, the one of the correspondence
category `AutomorphicObject (padicField v)`. -/
local instance localComponentGeneralLinearTopology {F : Type u} [Field F] [NumberField F]
    (v : FinitePlace F) (n : ℕ) : TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

namespace OperatorSubquotient

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (Q : OperatorSubquotient F n)

/-- The restriction of `Q` to `GL_n(F_v)` is `ρ`-isotypic: the quotient space of `Q` is
spanned by the images of the `GL_n(F_v)`-intertwining maps from `ρ` into it. -/
def IsFinitePlaceIsotypic (v : FinitePlace F) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (FiniteLocalGL F n v) W) : Prop :=
  ⨆ f : ρ.IntertwiningMap (Q.localRepresentation v), LinearMap.range f.toLinearMap = ⊤

/-- At a real place `v`, `Q` is `(ρ, π)`-isotypic for the compact action of `O(n)` and
the complexified Lie action of `𝔤𝔩_n(ℝ)` at `v`. -/
def IsRealPlaceIsotypic (v : {v : NumberField.InfinitePlace F // v.IsReal})
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  Archimedean.IsGKIsotypic ρ π (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v)

/-- At a complex place `v`, `Q` is `(ρ, π)`-isotypic for the compact action of `U(n)`
and the complexified Lie action of `𝔤𝔩_n(ℂ)`, regarded as a real Lie algebra, at `v`. -/
def IsComplexPlaceIsotypic (v : {v : NumberField.InfinitePlace F // v.IsComplex})
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  Archimedean.IsGKIsotypic ρ π (Q.complexPlaceCompactRepresentation v)
    (Q.complexPlaceLieAction v)

end OperatorSubquotient

/-- **Local components** (Getz–Hahn, Theorem 6.3.7; Flath, Theorem 3) for `GL_(r+1)` over
a number field `F`: let `Q` be an irreducible operator subquotient that is jointly
admissible. At every finite place `v` there is an irreducible admissible smooth
representation `A` of `GL_(r+1)(F_v)` for which the restriction of `Q` to
`GL_(r+1)(F_v)` is `A`-isotypic. At every real place `v` there is an irreducible
admissible `(𝔤𝔩_(r+1)(ℝ), O(r+1))`-module `(V, ρ, π)` for which `Q` is `(ρ, π)`-isotypic
at `v`, and at every complex place likewise with `(𝔤𝔩_(r+1)(ℂ), U(r+1))`-modules. -/
def LocalComponentExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (r : ℕ) (Q : IrreducibleOperatorSubquotient F r),
    Q.subquotient.IsJointlyAdmissible →
    (∀ v : FinitePlace F, ∃ A : AutomorphicObject.{u, u} (padicField v) r.succPNat,
      Q.subquotient.IsFinitePlaceIsotypic v A.obj.representation) ∧
    (∀ v : {v : NumberField.InfinitePlace F // v.IsReal},
      ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
        (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
        Archimedean.IsRealGKModule (r + 1) ρ π ∧ Archimedean.IsIrreducibleGKModule ρ π ∧
          Archimedean.IsAdmissibleGKModule ρ ∧ Q.subquotient.IsRealPlaceIsotypic v ρ π) ∧
    ∀ v : {v : NumberField.InfinitePlace F // v.IsComplex},
      ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
        (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
        Archimedean.IsComplexGKModule (r + 1) ρ π ∧ Archimedean.IsIrreducibleGKModule ρ π ∧
          Archimedean.IsAdmissibleGKModule ρ ∧ Q.subquotient.IsComplexPlaceIsotypic v ρ π

/-- **Embedded irreducible local representations are the local components** (Flath, the
isotypic restriction at the end of the proof of Theorem 1, with Theorem 3): let `Q` be an
irreducible jointly admissible operator subquotient of `GL_(r+1)`. An irreducible
representation `ρ` of `GL_(r+1)(F_v)` has a nonzero intertwining map into the restriction
of `Q` to `GL_(r+1)(F_v)` exactly when that restriction is `ρ`-isotypic; likewise at the
real and complex places for pairs `(ρ, π)` irreducible as `(𝔤, K)`-modules. -/
def LocalComponentEmbeddingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (r : ℕ) (Q : IrreducibleOperatorSubquotient F r),
    Q.subquotient.IsJointlyAdmissible →
    (∀ (v : FinitePlace F) (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (FiniteLocalGL F (r + 1) v) W), ρ.IsIrreducible →
      (Q.subquotient.IsFinitePlaceIsotypic v ρ ↔
        ∃ f : ρ.IntertwiningMap (Q.subquotient.localRepresentation v), f ≠ 0)) ∧
    (∀ (v : {v : NumberField.InfinitePlace F // v.IsReal}) (V : Type uW)
      [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      Archimedean.IsIrreducibleGKModule ρ π →
      (Q.subquotient.IsRealPlaceIsotypic v ρ π ↔
        ∃ f ∈ Archimedean.gkHoms ρ π (Q.subquotient.realPlaceCompactRepresentation v)
          (Q.subquotient.realPlaceLieAction v), f ≠ 0)) ∧
    ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex}) (V : Type uW)
      [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
      (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
      Archimedean.IsIrreducibleGKModule ρ π →
      (Q.subquotient.IsComplexPlaceIsotypic v ρ π ↔
        ∃ f ∈ Archimedean.gkHoms ρ π (Q.subquotient.complexPlaceCompactRepresentation v)
          (Q.subquotient.complexPlaceLieAction v), f ≠ 0)

/-- **Automorphic representations are determined by their local components** (Getz–Hahn,
Theorem 6.3.7 and the uniqueness of the factors; Flath, Theorem 3): two irreducible
jointly admissible operator subquotients `Q`, `Q'` of `GL_(r+1)` are equivalent for all
operators exactly when at every finite place some irreducible representation of
`GL_(r+1)(F_v)` is a local component of both, and at every infinite place some
irreducible `(𝔤, K)`-module is a local component of both. -/
def LocalComponentDeterminationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (r : ℕ) (Q Q' : IrreducibleOperatorSubquotient F r),
    Q.subquotient.IsJointlyAdmissible → Q'.subquotient.IsJointlyAdmissible →
    (Nonempty (Q.Equivalence Q') ↔
      (∀ v : FinitePlace F, ∃ (W : ModuleCat.{u} ℂ)
          (ρ : Representation ℂ (FiniteLocalGL F (r + 1) v) W), ρ.IsIrreducible ∧
        Q.subquotient.IsFinitePlaceIsotypic v ρ ∧ Q'.subquotient.IsFinitePlaceIsotypic v ρ) ∧
      (∀ v : {v : NumberField.InfinitePlace F // v.IsReal},
        ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
          (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
          Archimedean.IsIrreducibleGKModule ρ π ∧
            Q.subquotient.IsRealPlaceIsotypic v ρ π ∧ Q'.subquotient.IsRealPlaceIsotypic v ρ π) ∧
      ∀ v : {v : NumberField.InfinitePlace F // v.IsComplex},
        ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
          (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
          Archimedean.IsIrreducibleGKModule ρ π ∧
            Q.subquotient.IsComplexPlaceIsotypic v ρ π ∧
              Q'.subquotient.IsComplexPlaceIsotypic v ρ π)

end Automorphic

end Langlands
