import Langlands.Geometry.Analytic.SaturatedLocalizedFractions
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Berkovich's test relations on morphisms and continuous actions on analytic spaces -/

noncomputable section

universe u v w z z'

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A triple `(U, f, t)` of Berkovich's set `E(X)` on the space of a saturated presentation
`B`: an affinoid domain `U` (a chart of `B`), an analytic function `f` on `U` and a positive
number `t`. -/
structure TestTriple (B : SaturatedAtlasPresentation.{u, v, w} K) where
  /-- The chart index of the affinoid domain `U`. -/
  domain : B.presentation.atlas.Index
  /-- The analytic function `f` on `U`. -/
  function : B.presentation.atlas.algebra domain
  /-- The positive number `t`. -/
  bound : ℝ
  bound_pos : 0 < bound

namespace TestTriple

variable {B : SaturatedAtlasPresentation.{u, v, w} K} (τ : TestTriple B)

/-- The affinoid domain of a test triple, as a subset of the ambient space. -/
def locus : Set B.presentation.space :=
  Set.range (B.presentation.atlas.chart τ.domain)

end TestTriple

variable {T B : SaturatedAtlasPresentation.{u, v, w} K}

/-- A chart of the common source that both strong maps send into the affinoid domain of `τ`. -/
def IsTestPiece (τ : TestTriple B) (a b : T ⟶ B) (i : T.presentation.atlas.Index) : Prop :=
  a.baseMap '' Set.range (T.presentation.atlas.chart i) ⊆ τ.locus ∧
    b.baseMap '' Set.range (T.presentation.atlas.chart i) ⊆ τ.locus

/-- Berkovich's relation `d(a, b) < (U, f, t)` for two strong maps with a common source:
`a⁻¹(U) = b⁻¹(U)`, the charts sent into `U` by both maps cover `a⁻¹(U)`, and on each such
chart the difference of the two pullbacks of `f` has absolute value at most `t` at every
point. -/
def StrongNear (τ : TestTriple B) (a b : T ⟶ B) : Prop :=
  a.baseMap ⁻¹' τ.locus = b.baseMap ⁻¹' τ.locus ∧
    (∀ y ∈ a.baseMap ⁻¹' τ.locus, ∃ i, IsTestPiece τ a b i ∧
      y ∈ Set.range (T.presentation.atlas.chart i)) ∧
    ∀ i (h : IsTestPiece τ a b i) (p : BanachSpectrum (T.presentation.atlas.algebra i)),
      p (a.pullback i τ.domain h.1 τ.function - b.pullback i τ.domain h.2 τ.function) ≤
        τ.bound

theorem IsTestPiece.symm {τ : TestTriple B} {a b : T ⟶ B} {i : T.presentation.atlas.Index}
    (h : IsTestPiece τ a b i) : IsTestPiece τ b a i :=
  ⟨h.2, h.1⟩

theorem StrongNear.symm {τ : TestTriple B} {a b : T ⟶ B} (h : StrongNear τ a b) :
    StrongNear τ b a := by
  obtain ⟨hpre, hcov, hbound⟩ := h
  refine ⟨hpre.symm, fun y hy => ?_, fun i hi p => ?_⟩
  · obtain ⟨i, hi, hyi⟩ := hcov y (hpre ▸ hy)
    exact ⟨i, hi.symm, hyi⟩
  · rw [← map_neg_eq_map, neg_sub]
    exact hbound i hi.symm p

/-- The identity is near itself: its pieces over `U` include the chart `U` itself. -/
theorem strongNear_id (τ : TestTriple B) : StrongNear τ (𝟙 B) (𝟙 B) := by
  refine ⟨rfl, fun y hy => ⟨τ.domain, ?_, ?_⟩, fun i h p => ?_⟩
  · simp only [IsTestPiece, baseMap_id, ContinuousMap.coe_id, Set.image_id]
    exact ⟨subset_rfl, subset_rfl⟩
  · simpa [TestTriple.locus] using hy
  · simpa using τ.bound_pos.le

/-- The saturated presentation underlying an analytic space of the localized category. -/
abbrev presentationOf (X : LocalizedCategory.{u, v, w} (K := K)) :
    SaturatedAtlasPresentation.{u, v, w} K :=
  localizedObjectEquiv.symm X

/-- Berkovich's relation `d(φ, ψ) < (U, f, t)` for morphisms of analytic spaces. Both morphisms
are written as right fractions with a common quasi-isomorphic denominator `s`, and their
numerators are near in the sense of `StrongNear`. -/
def IsNear {X Y : LocalizedCategory.{u, v, w} (K := K)} (τ : TestTriple (presentationOf X))
    (φ ψ : Y ⟶ X) : Prop :=
  ∃ (T : SaturatedAtlasPresentation.{u, v, w} K) (s : T ⟶ presentationOf Y)
    (hs : s.IsQuasiIso) (a b : T ⟶ presentationOf X),
    φ = (localizedQuasiIso s hs).inv ≫ localizationFunctor.map a ∧
      ψ = (localizedQuasiIso s hs).inv ≫ localizationFunctor.map b ∧ StrongNear τ a b

section IsNear

variable {X Y : LocalizedCategory.{u, v, w} (K := K)} {τ : TestTriple (presentationOf X)}

theorem IsNear.symm {φ ψ : Y ⟶ X} (h : IsNear τ φ ψ) : IsNear τ ψ φ := by
  obtain ⟨T, s, hs, a, b, hφ, hψ, hab⟩ := h
  exact ⟨T, s, hs, b, a, hψ, hφ, hab.symm⟩

theorem localizedQuasiIso_id_inv (A : SaturatedAtlasPresentation.{u, v, w} K) :
    (localizedQuasiIso (𝟙 A) (quasiIsomorphisms.id_mem A)).inv = 𝟙 _ := by
  simpa using localizedQuasiIso_inv_hom_id (𝟙 A) (quasiIsomorphisms.id_mem A)

/-- A strong map is the right fraction with the identity denominator. -/
theorem localizationFunctor_map_eq_fraction {A B : SaturatedAtlasPresentation.{u, v, w} K}
    (a : A ⟶ B) : localizationFunctor.map a =
      (localizedQuasiIso (𝟙 A) (quasiIsomorphisms.id_mem A)).inv ≫ localizationFunctor.map a := by
  rw [localizedQuasiIso_id_inv, Category.id_comp]

/-- Strong maps that are near have near images in the localized category. -/
theorem isNear_localizationFunctor_map {A : SaturatedAtlasPresentation.{u, v, w} K}
    {a b : A ⟶ presentationOf X} (h : StrongNear τ a b) :
    IsNear (Y := localizationFunctor.obj A) τ (localizationFunctor.map a)
      (localizationFunctor.map b) :=
  ⟨A, 𝟙 A, quasiIsomorphisms.id_mem A, a, b, localizationFunctor_map_eq_fraction a,
    localizationFunctor_map_eq_fraction b, h⟩

/-- The identity morphism is near itself for every test triple. -/
theorem isNear_id (τ : TestTriple (presentationOf X)) : IsNear τ (𝟙 X) (𝟙 X) :=
  ⟨presentationOf X, 𝟙 _, quasiIsomorphisms.id_mem _, 𝟙 _, 𝟙 _,
    (localizedQuasiIso_inv_hom_id (𝟙 (presentationOf X)) (quasiIsomorphisms.id_mem _)).symm,
    (localizedQuasiIso_inv_hom_id (𝟙 (presentationOf X)) (quasiIsomorphisms.id_mem _)).symm,
    strongNear_id τ⟩

/-- The underlying continuous map of a right fraction `s⁻¹ a` is `a ∘ s⁻¹`, on preimages. -/
theorem preimage_localizedSpaceFunctor_map_fraction {A B : SaturatedAtlasPresentation.{u, v, w} K}
    (s : T ⟶ A) (hs : s.IsQuasiIso) (a : T ⟶ B) (S : Set B.presentation.space) :
    (localizedSpaceFunctor.map ((localizedQuasiIso s hs).inv ≫ localizationFunctor.map a) :
        localizedSpaceFunctor.obj (localizationFunctor.obj A) →
          localizedSpaceFunctor.obj (localizationFunctor.obj B)) ⁻¹' S =
      hs.inverseBaseMap ⁻¹' (a.baseMap ⁻¹' S) := by
  have ha : localizedSpaceFunctor.map ((localizedQuasiIso s hs).inv ≫ localizationFunctor.map a) =
      TopCat.ofHom (a.baseMap.comp hs.inverseBaseMap) :=
    localizedSpaceFunctor_map_rightFraction (MorphismProperty.RightFraction.mk s hs a)
  rw [ha]
  rfl

/-- Near morphisms have the same preimage of the affinoid domain `U` under their actual
underlying continuous maps. -/
theorem IsNear.preimage_eq {φ ψ : Y ⟶ X} (h : IsNear τ φ ψ) :
    (localizedSpaceFunctor.map φ : localizedSpaceFunctor.obj Y → localizedSpaceFunctor.obj X) ⁻¹'
        τ.locus =
      (localizedSpaceFunctor.map ψ : localizedSpaceFunctor.obj Y → localizedSpaceFunctor.obj X) ⁻¹'
        τ.locus := by
  obtain ⟨T, s, hs, a, b, rfl, rfl, hpre, -, -⟩ := h
  exact (preimage_localizedSpaceFunctor_map_fraction s hs a τ.locus).trans
    ((congrArg (hs.inverseBaseMap ⁻¹' ·) hpre).trans
      (preimage_localizedSpaceFunctor_map_fraction s hs b τ.locus).symm)

end IsNear

variable {G : Type z} [Group G] [TopologicalSpace G]

/-- Berkovich's set `G_{(U, f, t)}(X)` of automorphisms `σ` of `X` with
`d(σ, 1_X) < (U, f, t)`, that is, `σ(U) = U` and `ρ(σ*f - f) ≤ t`. -/
def nearIdentity {X : LocalizedCategory.{u, v, w} (K := K)} (τ : TestTriple (presentationOf X)) :
    Set (Aut X) :=
  {σ | IsNear τ σ.hom (𝟙 X)}

theorem one_mem_nearIdentity {X : LocalizedCategory.{u, v, w} (K := K)}
    (τ : TestTriple (presentationOf X)) : (1 : Aut X) ∈ nearIdentity τ :=
  isNear_id τ

/-- Berkovich's continuity of an action `ρ : G → G(X)` of a topological group on an analytic
space: for every test triple `τ`, the preimage of `G_τ(X)` is a neighbourhood of the identity
of `G`. -/
def IsContinuousAction {X : LocalizedCategory.{u, v, w} (K := K)} (ρ : G →* Aut X) : Prop :=
  ∀ τ : TestTriple (presentationOf X), ρ ⁻¹' nearIdentity τ ∈ 𝓝 (1 : G)

section IsContinuousAction

variable {X : LocalizedCategory.{u, v, w} (K := K)}

/-- The trivial action is continuous. -/
theorem isContinuousAction_one : IsContinuousAction (1 : G →* Aut X) := fun τ => by
  have : (1 : G →* Aut X) ⁻¹' nearIdentity τ = Set.univ :=
    Set.eq_univ_of_forall fun _ => one_mem_nearIdentity τ
  rw [this]
  exact Filter.univ_mem

/-- Every action of a discrete group is continuous. -/
theorem isContinuousAction_of_discreteTopology [DiscreteTopology G] (ρ : G →* Aut X) :
    IsContinuousAction ρ := fun τ =>
  mem_nhds_discrete.2 (by
    change ρ 1 ∈ nearIdentity τ
    rw [map_one]
    exact one_mem_nearIdentity τ)

/-- Restriction along a continuous homomorphism preserves continuity of actions. -/
theorem IsContinuousAction.comp {H : Type z'} [Group H] [TopologicalSpace H]
    {ρ : G →* Aut X} (hρ : IsContinuousAction ρ) (f : H →ₜ* G) :
    IsContinuousAction (ρ.comp f.toMonoidHom) := fun τ => by
  have h : ρ ⁻¹' nearIdentity τ ∈ 𝓝 (f 1) := by
    rw [map_one]
    exact hρ τ
  exact f.continuous.continuousAt.preimage_mem_nhds h

end IsContinuousAction

variable (K G) in
/-- Berkovich's `G`-spaces among Mathlib's actions of `G` on analytic spaces: the underlying
space is Hausdorff and the action is continuous. -/
def gSpaceProperty : ObjectProperty (Action (LocalizedCategory.{u, v, w} (K := K)) G) :=
  fun X => T2Space (localizedSpaceFunctor.obj X.V) ∧ IsContinuousAction X.ρAut

set_option linter.checkUnivs false in
variable (K G) in
/-- The category `G-𝒜n` of `G`-spaces and `G`-morphisms (equivariant morphisms). -/
abbrev GSpace := (gSpaceProperty.{u, v, w} K G).FullSubcategory

namespace GSpace

/-- Every Hausdorff analytic space with an action of a discrete group is a `G`-space. -/
theorem gSpaceProperty_of_discreteTopology [DiscreteTopology G]
    (X : Action (LocalizedCategory.{u, v, w} (K := K)) G)
    [T2Space (localizedSpaceFunctor.obj X.V)] : gSpaceProperty K G X :=
  ⟨inferInstance, isContinuousAction_of_discreteTopology _⟩

variable {H : Type z'} [Group H] [TopologicalSpace H]

/-- Restriction of a `G`-space along a continuous homomorphism `H → G`. -/
def res (f : H →ₜ* G) : GSpace.{u, v, w} K G ⥤ GSpace.{u, v, w} K H :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Action.res _ f.toMonoidHom) fun X =>
    ⟨X.2.1, X.2.2.comp f⟩

@[simp]
theorem res_obj_obj_V (f : H →ₜ* G) (X : GSpace.{u, v, w} K G) :
    ((res f).obj X).obj.V = X.obj.V := rfl

@[simp]
theorem res_obj_obj_ρ (f : H →ₜ* G) (X : GSpace.{u, v, w} K G) (h : H) :
    ((res f).obj X).obj.ρ h = X.obj.ρ (f h) := rfl

end GSpace

end Langlands.Analytic.SaturatedAtlasPresentation
