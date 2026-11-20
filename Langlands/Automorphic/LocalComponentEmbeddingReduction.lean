import Mathlib.Algebra.FreeMonoid.Basic
import Langlands.Representation.IrreducibleIsotypicEmbedding
import Langlands.Automorphic.OperatorSubquotientLocalComponentStatement

/-!
# Embedded irreducible local representations are the local components

This module proves that `LocalComponentExistenceStatement` implies
`LocalComponentEmbeddingStatement`. It is Flath's argument for the uniqueness of the local
factors (Flath 1979, end of the proof of Theorem 1, p.180): the restriction of an
irreducible automorphic representation to one place is isotypic for its local component,
so every irreducible representation that embeds in it is that local component.

* `Archimedean.gkFreeRepresentation ρ π`: a `(𝔤, K)`-module `(V, ρ, π)` read as one
  representation of the free monoid on `K ⊕ L`, a generator `k` acting by `ρ k` and a
  generator `X` by `π X`.
* `Archimedean.mem_gkHoms_iff_isIntertwiningMap`: the maps of `(𝔤, K)`-modules are the
  intertwining maps of these free-monoid representations.
* `Archimedean.isIrreducible_gkFreeRepresentation`: an irreducible `(𝔤, K)`-module gives an
  irreducible free-monoid representation.
* `Archimedean.isGKIsotypic_iff_exists_ne_zero`: the archimedean form of
  `IsotypicEmbedding.isotypic_iff_exists_ne_zero`.
* `Automorphic.localComponentEmbedding_of_localComponentExistence`: the implication.
-/

noncomputable section

set_option autoImplicit false

open scoped TensorProduct

namespace Langlands

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Archimedean

universe uK uL uA uV uQ

section FreeRepresentation

variable {K : Type uK} [Group K] {L : Type uL} [LieRing L] [LieAlgebra ℂ L]
  {VA : Type uA} [AddCommGroup VA] [Module ℂ VA]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uQ} [AddCommGroup W] [Module ℂ W]

/-- A `(𝔤, K)`-module `(V, ρ, π)` as a representation of the free monoid on `K ⊕ L`: the
generator `k : K` acts by `ρ k` and the generator `X : L` by `π X`. Its subrepresentations
are the subspaces stable under `ρ` and `π`, and its intertwining maps are the maps of
`(𝔤, K)`-modules. -/
def gkFreeRepresentation (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) :
    Representation ℂ (FreeMonoid (K ⊕ L)) V :=
  FreeMonoid.lift (Sum.elim (fun k => ρ k) (fun X => π X))

@[simp] theorem gkFreeRepresentation_of_inl (ρ : Representation ℂ K V)
    (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (k : K) :
    gkFreeRepresentation ρ π (FreeMonoid.of (Sum.inl k)) = ρ k :=
  rfl

@[simp] theorem gkFreeRepresentation_of_inr (ρ : Representation ℂ K V)
    (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (X : L) :
    gkFreeRepresentation ρ π (FreeMonoid.of (Sum.inr X)) = π X :=
  rfl

/-- **Maps of `(𝔤, K)`-modules are intertwining maps of the free-monoid
representations.** A linear map intertwines `(ρ, π)` with `(ρ', π')` exactly when it
intertwines the actions of every word in `K ⊕ L`. -/
theorem mem_gkHoms_iff_isIntertwiningMap (ρ : Representation ℂ K V)
    (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (ρ' : Representation ℂ K W)
    (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W) (f : V →ₗ[ℂ] W) :
    f ∈ gkHoms ρ π ρ' π' ↔
      ∀ (w : FreeMonoid (K ⊕ L)) (x : V),
        f (gkFreeRepresentation ρ π w x) = gkFreeRepresentation ρ' π' w (f x) := by
  constructor
  · rintro ⟨hK, hL⟩ w
    induction w using FreeMonoid.inductionOn' with
    | one => intro x; simp
    | of_mul a w ih =>
      intro x
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← ih x]
      rcases a with k | X
      · exact hK k _
      · exact hL X _
  · intro h
    exact ⟨fun k x => h (FreeMonoid.of (Sum.inl k)) x, fun X x => h (FreeMonoid.of (Sum.inr X)) x⟩

/-- The intertwining map of free-monoid representations given by a map of
`(𝔤, K)`-modules. -/
def gkHomsIntertwiningMap (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ρ' : Representation ℂ K W) (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W) (f : gkHoms ρ π ρ' π') :
    (gkFreeRepresentation ρ π).IntertwiningMap (gkFreeRepresentation ρ' π') :=
  (f : V →ₗ[ℂ] W).intertwiningMap_of_isIntertwiningMap _ _
    ((mem_gkHoms_iff_isIntertwiningMap ρ π ρ' π' f).mp f.2)

theorem gkHomsIntertwiningMap_toLinearMap (ρ : Representation ℂ K V)
    (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (ρ' : Representation ℂ K W)
    (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W) (f : gkHoms ρ π ρ' π') :
    (gkHomsIntertwiningMap ρ π ρ' π' f).toLinearMap = f :=
  rfl

/-- The linear map underlying an intertwining map of free-monoid representations is a map
of `(𝔤, K)`-modules. -/
theorem toLinearMap_mem_gkHoms (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ρ' : Representation ℂ K W) (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W)
    (g : (gkFreeRepresentation ρ π).IntertwiningMap (gkFreeRepresentation ρ' π')) :
    g.toLinearMap ∈ gkHoms ρ π ρ' π' :=
  (mem_gkHoms_iff_isIntertwiningMap ρ π ρ' π' g.toLinearMap).mpr g.isIntertwining

/-- The span of the images of the maps of `(𝔤, K)`-modules is the span of the images of the
intertwining maps of the free-monoid representations. -/
theorem iSup_range_gkHoms_eq (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ρ' : Representation ℂ K W) (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W) :
    (⨆ f ∈ gkHoms ρ π ρ' π', LinearMap.range f) =
      ⨆ g : (gkFreeRepresentation ρ π).IntertwiningMap (gkFreeRepresentation ρ' π'),
        LinearMap.range g.toLinearMap := by
  apply le_antisymm
  · refine iSup₂_le fun f hf => ?_
    have h := le_iSup
      (fun g : (gkFreeRepresentation ρ π).IntertwiningMap (gkFreeRepresentation ρ' π') =>
        LinearMap.range g.toLinearMap) (gkHomsIntertwiningMap ρ π ρ' π' ⟨f, hf⟩)
    exact h
  · refine iSup_le fun g => ?_
    exact le_iSup₂_of_le (f := fun (f : V →ₗ[ℂ] W) (_ : f ∈ gkHoms ρ π ρ' π') =>
      LinearMap.range f) g.toLinearMap (toLinearMap_mem_gkHoms ρ π ρ' π' g) le_rfl

/-- Isotypy of `(𝔤, K)`-modules is isotypy of the free-monoid representations. -/
theorem isGKIsotypic_iff (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ρ' : Representation ℂ K W) (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W) :
    IsGKIsotypic ρ π ρ' π' ↔
      ⨆ g : (gkFreeRepresentation ρ π).IntertwiningMap (gkFreeRepresentation ρ' π'),
        LinearMap.range g.toLinearMap = ⊤ := by
  unfold IsGKIsotypic
  rw [iSup_range_gkHoms_eq]

/-- A nonzero map of `(𝔤, K)`-modules is a nonzero intertwining map of the free-monoid
representations, and conversely. -/
theorem exists_mem_gkHoms_ne_zero_iff (ρ : Representation ℂ K V)
    (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (ρ' : Representation ℂ K W)
    (π' : L →ₗ⁅ℂ⁆ Module.End ℂ W) :
    (∃ f ∈ gkHoms ρ π ρ' π', f ≠ 0) ↔
      ∃ g : (gkFreeRepresentation ρ π).IntertwiningMap (gkFreeRepresentation ρ' π'), g ≠ 0 := by
  constructor
  · rintro ⟨f, hf, hne⟩
    refine ⟨gkHomsIntertwiningMap ρ π ρ' π' ⟨f, hf⟩, fun h0 => hne ?_⟩
    have := congrArg Representation.IntertwiningMap.toLinearMap h0
    exact this
  · rintro ⟨g, hne⟩
    refine ⟨g.toLinearMap, toLinearMap_mem_gkHoms ρ π ρ' π' g, fun h0 => hne ?_⟩
    exact Representation.IntertwiningMap.ext h0

/-- **An irreducible `(𝔤, K)`-module is an irreducible free-monoid representation.** The
subrepresentations of `gkFreeRepresentation ρ π` are the subspaces stable under `ρ` and
`π`. -/
theorem isIrreducible_gkFreeRepresentation (ρ : Representation ℂ K V)
    (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (h : IsIrreducibleGKModule ρ π) :
    (gkFreeRepresentation ρ π).IsIrreducible := by
  obtain ⟨hV, hstable⟩ := h
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h0 => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h1 : (⊥ : Submodule ℂ V) = ⊤ :=
      congrArg Subrepresentation.toSubmodule h0
    exact bot_ne_top h1
  · rcases hstable S.toSubmodule
        (fun k w hw => S.apply_mem_toSubmodule (FreeMonoid.of (Sum.inl k)) hw)
        (fun X w hw => S.apply_mem_toSubmodule (FreeMonoid.of (Sum.inr X)) hw) with h1 | h1
    · exact Or.inl (Subrepresentation.ext h1)
    · exact Or.inr (Subrepresentation.ext h1)

/-- **An irreducible `(𝔤, K)`-module embedded in an isotypic one is its type.** Let
`(W, ρQ, πQ)` be nonzero and `(VA, ρA, πA)`-isotypic for an irreducible `(𝔤, K)`-module
`(VA, ρA, πA)`. An irreducible `(𝔤, K)`-module `(V, ρ, π)` makes `W` `(ρ, π)`-isotypic exactly
when some nonzero map of `(𝔤, K)`-modules goes from `V` to `W`. -/
theorem isGKIsotypic_iff_exists_ne_zero [Nontrivial W] (ρA : Representation ℂ K VA)
    (πA : L →ₗ⁅ℂ⁆ Module.End ℂ VA) (ρQ : Representation ℂ K W)
    (πQ : L →ₗ⁅ℂ⁆ Module.End ℂ W) (hA : IsIrreducibleGKModule ρA πA)
    (hiso : IsGKIsotypic ρA πA ρQ πQ) (ρ : Representation ℂ K V)
    (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (h : IsIrreducibleGKModule ρ π) :
    IsGKIsotypic ρ π ρQ πQ ↔ ∃ f ∈ gkHoms ρ π ρQ πQ, f ≠ 0 := by
  have := isIrreducible_gkFreeRepresentation ρA πA hA
  have := isIrreducible_gkFreeRepresentation ρ π h
  rw [isGKIsotypic_iff, exists_mem_gkHoms_ne_zero_iff]
  exact IsotypicEmbedding.isotypic_iff_exists_ne_zero (gkFreeRepresentation ρA πA)
    (gkFreeRepresentation ρ π) (gkFreeRepresentation ρQ πQ) ((isGKIsotypic_iff _ _ _ _).mp hiso)

end FreeRepresentation

end Archimedean

namespace Automorphic

universe u uA uW

open Langlands.Global
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)

/- The statement module registers these instances locally; registering the same declarations
here makes the instance terms of this module agree syntactically with those of the
statements. -/
attribute [local instance] localComponentRationalGroup localComponentContinuousGroup
  localComponentSmoothGroup localComponentFormGroup localComponentStableGroup
  localComponentRealizationGroup localComponentGeneralLinearTopology

section Places

variable {F : Type u} [Field F] [NumberField F] {r : ℕ} (Q : IrreducibleOperatorSubquotient F r)

/-- **Finite places.** If the restriction of `Q` to `GL_(r+1)(F_v)` is `ρA`-isotypic for an
irreducible `ρA`, then for an irreducible `ρ` it is `ρ`-isotypic exactly when some
intertwining map from `ρ` into it is nonzero. -/
theorem finitePlaceIsotypic_iff_exists_ne_zero (v : FinitePlace F)
    {A : Type uA} [AddCommGroup A] [Module ℂ A]
    (ρA : Representation ℂ (FiniteLocalGL F (r + 1) v) A) (hAirr : ρA.IsIrreducible)
    (hA : Q.subquotient.IsFinitePlaceIsotypic v ρA) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (FiniteLocalGL F (r + 1) v) W) (hρ : ρ.IsIrreducible) :
    Q.subquotient.IsFinitePlaceIsotypic v ρ ↔
      ∃ f : ρ.IntertwiningMap (Q.subquotient.localRepresentation v), f ≠ 0 := by
  have := hAirr
  have := hρ
  exact IsotypicEmbedding.isotypic_iff_exists_ne_zero ρA ρ (Q.subquotient.localRepresentation v) hA

/-- **Real places.** If `Q` is `(ρA, πA)`-isotypic at the real place `v` for an irreducible
`(𝔤, K)`-module, then for an irreducible `(𝔤, K)`-module `(V, ρ, π)` it is `(ρ, π)`-isotypic
exactly when some nonzero map of `(𝔤, K)`-modules goes from `V` into it. -/
theorem realPlaceIsotypic_iff_exists_ne_zero (v : {v : NumberField.InfinitePlace F // v.IsReal})
    {VA : Type uA} [AddCommGroup VA] [Module ℂ VA]
    (ρA : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) VA)
    (πA : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ VA)
    (hAirr : Archimedean.IsIrreducibleGKModule ρA πA)
    (hA : Q.subquotient.IsRealPlaceIsotypic v ρA πA) {V : Type uW} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hρ : Archimedean.IsIrreducibleGKModule ρ π) :
    Q.subquotient.IsRealPlaceIsotypic v ρ π ↔
      ∃ f ∈ Archimedean.gkHoms ρ π (Q.subquotient.realPlaceCompactRepresentation v)
        (Q.subquotient.realPlaceLieAction v), f ≠ 0 :=
  Archimedean.isGKIsotypic_iff_exists_ne_zero ρA πA _ _ hAirr hA ρ π hρ

/-- **Complex places.** The same as `realPlaceIsotypic_iff_exists_ne_zero` at a complex
place, with `U(r+1)` and `𝔤𝔩_(r+1)(ℂ)`. -/
theorem complexPlaceIsotypic_iff_exists_ne_zero
    (v : {v : NumberField.InfinitePlace F // v.IsComplex})
    {VA : Type uA} [AddCommGroup VA] [Module ℂ VA]
    (ρA : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) VA)
    (πA : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ VA)
    (hAirr : Archimedean.IsIrreducibleGKModule ρA πA)
    (hA : Q.subquotient.IsComplexPlaceIsotypic v ρA πA) {V : Type uW} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hρ : Archimedean.IsIrreducibleGKModule ρ π) :
    Q.subquotient.IsComplexPlaceIsotypic v ρ π ↔
      ∃ f ∈ Archimedean.gkHoms ρ π (Q.subquotient.complexPlaceCompactRepresentation v)
        (Q.subquotient.complexPlaceLieAction v), f ≠ 0 :=
  Archimedean.isGKIsotypic_iff_exists_ne_zero ρA πA _ _ hAirr hA ρ π hρ

end Places

section Existence

variable (hex : LocalComponentExistenceStatement.{u}) {F : Type u} [Field F] [NumberField F]
  {r : ℕ} (Q : IrreducibleOperatorSubquotient F r) (hQ : Q.subquotient.IsJointlyAdmissible)

include hex hQ

/-- The finite-place part of `localComponentEmbedding_of_localComponentExistence`. -/
theorem finitePlaceEmbedding_of_localComponentExistence (v : FinitePlace F)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (FiniteLocalGL F (r + 1) v) W) (hρ : ρ.IsIrreducible) :
    Q.subquotient.IsFinitePlaceIsotypic v ρ ↔
      ∃ f : ρ.IntertwiningMap (Q.subquotient.localRepresentation v), f ≠ 0 := by
  have h := (hex F r Q hQ).1 v
  obtain ⟨A, hA⟩ := h
  exact finitePlaceIsotypic_iff_exists_ne_zero Q v A.obj.representation A.property.1 hA ρ hρ

/-- The real-place part of `localComponentEmbedding_of_localComponentExistence`. -/
theorem realPlaceEmbedding_of_localComponentExistence
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) {V : Type uW} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hρ : Archimedean.IsIrreducibleGKModule ρ π) :
    Q.subquotient.IsRealPlaceIsotypic v ρ π ↔
      ∃ f ∈ Archimedean.gkHoms ρ π (Q.subquotient.realPlaceCompactRepresentation v)
        (Q.subquotient.realPlaceLieAction v), f ≠ 0 := by
  have h := (hex F r Q hQ).2.1 v
  obtain ⟨VA, ρA, πA, -, hAirr, -, hA⟩ := h
  exact realPlaceIsotypic_iff_exists_ne_zero Q v ρA πA hAirr hA ρ π hρ

/-- The complex-place part of `localComponentEmbedding_of_localComponentExistence`. -/
theorem complexPlaceEmbedding_of_localComponentExistence
    (v : {v : NumberField.InfinitePlace F // v.IsComplex}) {V : Type uW} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hρ : Archimedean.IsIrreducibleGKModule ρ π) :
    Q.subquotient.IsComplexPlaceIsotypic v ρ π ↔
      ∃ f ∈ Archimedean.gkHoms ρ π (Q.subquotient.complexPlaceCompactRepresentation v)
        (Q.subquotient.complexPlaceLieAction v), f ≠ 0 := by
  have h := (hex F r Q hQ).2.2 v
  obtain ⟨VA, ρA, πA, -, hAirr, -, hA⟩ := h
  exact complexPlaceIsotypic_iff_exists_ne_zero Q v ρA πA hAirr hA ρ π hρ

end Existence

/-- **Local components are the embedded irreducible representations** (Flath 1979, end of
the proof of Theorem 1, p.180): `LocalComponentExistenceStatement` implies
`LocalComponentEmbeddingStatement`. -/
theorem localComponentEmbedding_of_localComponentExistence :
    LocalComponentExistenceStatement.{u} → LocalComponentEmbeddingStatement.{u, uW} :=
  fun hex _ _ _ _ Q hQ =>
    ⟨fun v _ _ _ ρ hρ => finitePlaceEmbedding_of_localComponentExistence hex Q hQ v ρ hρ,
      fun v _ _ _ ρ π hρ => realPlaceEmbedding_of_localComponentExistence hex Q hQ v ρ π hρ,
      fun v _ _ _ ρ π hρ => complexPlaceEmbedding_of_localComponentExistence hex Q hQ v ρ π hρ⟩

end Automorphic

end Langlands
