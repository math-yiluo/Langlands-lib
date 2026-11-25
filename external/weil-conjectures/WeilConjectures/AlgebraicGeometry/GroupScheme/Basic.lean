/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Normal
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.Topology.JacobsonSpace
public import WeilConjectures.Mathlib.Topology.Constructible
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Geometry of group schemes over a field

Let `G` be a group scheme over a field `k`: a group object in `Over (Spec k)`. This file states
the basic facts about the underlying scheme of `G` used for algebraic groups: left translation by a
rational point is an automorphism of `G`; a group scheme of finite type has finitely many connected
components and its identity component `G°` is open; the image of a homomorphism of group schemes of
finite type is closed; and a closed subgroup of a connected reduced group of the same dimension is
the whole group.

## Main definitions

- `AlgebraicGeometry.GrpObj.onePoint`: the identity point of `G`, the image of the unit section.
- `AlgebraicGeometry.GrpObj.mulLeft`: left translation by a rational point `g` of `G`.
- `AlgebraicGeometry.GrpObj.mulRight`, `AlgebraicGeometry.GrpObj.conjBy`,
  `AlgebraicGeometry.GrpObj.translate`: right translation, conjugation and the translate of a
  closed subgroup scheme by a rational point.
- `AlgebraicGeometry.GrpObj.mulLeftIso`, `AlgebraicGeometry.GrpObj.mulRightIso`: the
  translations as automorphisms, with inverses the translations by `g⁻¹`.
- `AlgebraicGeometry.GrpObj.identityComponentOpens`: the identity component `G°`, as an open
  subset of `G`.
- `AlgebraicGeometry.GrpObj.identityComponent`: the identity component `G°` as an open subgroup
  scheme of `G`, with its inclusion `AlgebraicGeometry.GrpObj.identityComponentι : G° ⟶ G`, a
  normal monomorphism of group objects.

## Main results

- `AlgebraicGeometry.GrpObj.irreducibleSpace_identityComponent`: `G°` is irreducible.
- `AlgebraicGeometry.GrpObj.finiteIndex_range_identityComponentι`: `G°(k)` has finite index in
  `G(k)`.
- `AlgebraicGeometry.GrpObj.image_mulLeft_connectedComponent_onePoint`: the connected components
  of `G` are the translates of `G°` by rational points.
- `AlgebraicGeometry.finite_connectedComponents`: a group scheme of finite type over `k` has
  finitely many connected components.
- `AlgebraicGeometry.GrpObj.isReduced_of_charZero`: Cartier's theorem, a group scheme locally of
  finite type over a field of characteristic zero is reduced.
- `AlgebraicGeometry.isClosed_range_of_isMonHom`: the image of a homomorphism from a group scheme
  of finite type to a group scheme locally of finite type over `k` is closed.
- `AlgebraicGeometry.irreducibleSpace_of_connectedSpace`: a connected group scheme locally of
  finite type over `k` is irreducible.
- `AlgebraicGeometry.isIso_left_of_topologicalKrullDim_eq`: a closed subgroup of a connected reduced
  group of the same dimension is the whole group.

## Blueprint

- `lemma-connected-components-images-homomorphisms`: the identity component, images of homomorphisms
and the dimension criterion.
- `def-wf-algebraic-components`: the identity component `GrpObj.identityComponent`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The identity point of a group scheme `G` over a field `k`: the image of the unique point of
`Spec k` under the unit section. (blueprint: `lemma-connected-components-images-homomorphisms`) -/
noncomputable def GrpObj.onePoint (G : Over (Spec (.of k))) [GrpObj G] : G.left :=
  η[G].left.base (show Spec (.of k) from ⟨⊥, Ideal.isPrime_bot⟩)

/-- Left translation `x ↦ g * x` on a group scheme `G` over `k` by a rational point `g` of `G`.
(blueprint: `lemma-connected-components-images-homomorphisms`) -/
noncomputable def GrpObj.mulLeft (G : Over (Spec (.of k))) [GrpObj G]
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G ⟶ G :=
  lift (toUnit G ≫ g) (𝟙 G) ≫ μ[G]

/-- Left translation by a rational point is an automorphism of the underlying scheme.
(blueprint: `lemma-connected-components-images-homomorphisms`) -/
theorem GrpObj.isIso_mulLeft_left (G : Over (Spec (.of k))) [GrpObj G]
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : IsIso (GrpObj.mulLeft G g).left := by
  have hmul (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : GrpObj.mulLeft G g = (toUnit G ≫ g) * 𝟙 G :=
    rfl
  have hcomp (g h : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
      GrpObj.mulLeft G g ≫ GrpObj.mulLeft G h = GrpObj.mulLeft G (h * g) := by
    rw [hmul, hmul, hmul, MonObj.comp_mul, ← Category.assoc, toUnit_unique (_ ≫ toUnit G),
      Category.comp_id, ← mul_assoc, MonObj.comp_mul]
  have hone : GrpObj.mulLeft G 1 = 𝟙 G := by
    rw [hmul, MonObj.comp_one, one_mul]
  have : IsIso (GrpObj.mulLeft G g) :=
    ⟨GrpObj.mulLeft G g⁻¹, by rw [hcomp, inv_mul_cancel, hone],
      by rw [hcomp, mul_inv_cancel, hone]⟩
  exact inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulLeft G g)))

section Translation

variable (G : Over (Spec (.of k))) [GrpObj G]

/-- In the group `G ⟶ G` of endomorphisms, left translation by `g` is `g * id`. -/
lemma GrpObj.mulLeft_eq_mul (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    GrpObj.mulLeft G g = (toUnit G ≫ g) * 𝟙 G := rfl

/-- Right translation `x ↦ x * g` on a group scheme `G` over `k` by a rational point `g`.
(blueprint: `def-sc-group-scheme-translate`) -/
noncomputable def GrpObj.mulRight (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G ⟶ G :=
  lift (𝟙 G) (toUnit G ≫ g) ≫ μ[G]

lemma GrpObj.mulRight_eq_mul (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    GrpObj.mulRight G g = 𝟙 G * (toUnit G ≫ g) := rfl

lemma GrpObj.mulLeft_comp_mulLeft (g h : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    GrpObj.mulLeft G g ≫ GrpObj.mulLeft G h = GrpObj.mulLeft G (h * g) := by
  rw [mulLeft_eq_mul, mulLeft_eq_mul, mulLeft_eq_mul, MonObj.comp_mul, ← Category.assoc,
    toUnit_unique (_ ≫ toUnit G), Category.comp_id, ← mul_assoc, MonObj.comp_mul]

lemma GrpObj.mulRight_comp_mulRight (g h : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    GrpObj.mulRight G g ≫ GrpObj.mulRight G h = GrpObj.mulRight G (g * h) := by
  rw [mulRight_eq_mul, mulRight_eq_mul, mulRight_eq_mul, MonObj.comp_mul, ← Category.assoc,
    toUnit_unique (_ ≫ toUnit G), Category.comp_id, mul_assoc, MonObj.comp_mul]

lemma GrpObj.mulLeft_one : GrpObj.mulLeft G 1 = 𝟙 G := by
  rw [mulLeft_eq_mul, MonObj.comp_one, one_mul]

lemma GrpObj.mulRight_one : GrpObj.mulRight G 1 = 𝟙 G := by
  rw [mulRight_eq_mul, MonObj.comp_one, mul_one]

/-- Left translation by `g` as an automorphism of `G`, with inverse the left translation by
`g⁻¹`. (blueprint: `lem-sc-translation-automorphism`) -/
@[simps]
noncomputable def GrpObj.mulLeftIso (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G ≅ G where
  hom := GrpObj.mulLeft G g
  inv := GrpObj.mulLeft G g⁻¹
  hom_inv_id := by rw [mulLeft_comp_mulLeft, inv_mul_cancel, mulLeft_one]
  inv_hom_id := by rw [mulLeft_comp_mulLeft, mul_inv_cancel, mulLeft_one]

/-- Right translation by `g` as an automorphism of `G`, with inverse the right translation by
`g⁻¹`. (blueprint: `lem-sc-translation-automorphism`) -/
@[simps]
noncomputable def GrpObj.mulRightIso (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G ≅ G where
  hom := GrpObj.mulRight G g
  inv := GrpObj.mulRight G g⁻¹
  hom_inv_id := by rw [mulRight_comp_mulRight, mul_inv_cancel, mulRight_one]
  inv_hom_id := by rw [mulRight_comp_mulRight, inv_mul_cancel, mulRight_one]

/-- Conjugation `c_g = L_g ∘ R_{g⁻¹}`, `x ↦ g * x * g⁻¹`, by a rational point `g`.
(blueprint: `def-sc-group-scheme-translate`) -/
noncomputable def GrpObj.conjBy (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : G ⟶ G :=
  GrpObj.mulRight G g⁻¹ ≫ GrpObj.mulLeft G g

lemma GrpObj.comp_conjBy {X : Over (Spec (.of k))} (f : X ⟶ G)
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    f ≫ GrpObj.conjBy G g = (toUnit X ≫ g) * f * (toUnit X ≫ g⁻¹) := by
  rw [conjBy, mulRight_eq_mul, mulLeft_eq_mul, ← Category.assoc, MonObj.comp_mul,
    MonObj.comp_mul, ← Category.assoc, ← Category.assoc, toUnit_unique (_ ≫ toUnit G),
    toUnit_unique (_ ≫ toUnit _), Category.comp_id, Category.comp_id, mul_assoc]

/-- Conjugation by a rational point is a homomorphism of group schemes:
`c_g ∘ m = m ∘ (c_g × c_g)` and `c_g ∘ e = e`. (blueprint: `lem-sc-translation-automorphism`) -/
instance GrpObj.isMonHom_conjBy (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    IsMonHom (GrpObj.conjBy G g) where
  one_hom := by
    have h1 : (η[G] : 𝟙_ _ ⟶ G) = 1 := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [comp_conjBy, toUnit_unit, Category.id_comp, Category.id_comp, h1, mul_one,
      mul_inv_cancel]
  mul_hom := by
    have hμ : μ[G] = fst G G * snd G G := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    have hinv : toUnit (G ⊗ G) ≫ g⁻¹ = (toUnit (G ⊗ G) ≫ g)⁻¹ := by
      rw [Hom.inv_def, Hom.inv_def, Category.assoc]
    rw [comp_conjBy, hμ, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, comp_conjBy,
      comp_conjBy, hinv]
    group

/-- The translate `gZ ⊆ G` of a closed subgroup scheme `j : Z ⟶ G` by a rational point `g`,
recorded as the closed immersion `L_g ∘ j : Z ⟶ G` whose image it is.
(blueprint: `def-sc-group-scheme-translate`) -/
noncomputable def GrpObj.translate {Z : Over (Spec (.of k))} (j : Z ⟶ G)
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : Z ⟶ G :=
  j ≫ GrpObj.mulLeft G g

/-- The translate of a closed subscheme by a rational point is again a closed subscheme. -/
theorem GrpObj.isClosedImmersion_translate {Z : Over (Spec (.of k))} (j : Z ⟶ G)
    [IsClosedImmersion j.left] (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    IsClosedImmersion (GrpObj.translate G j g).left := by
  have := GrpObj.isIso_mulLeft_left G g
  rw [GrpObj.translate, Over.comp_left]
  infer_instance

/-- Left translation of a generalized point `x` by `g` is `g * x`. -/
lemma GrpObj.comp_mulLeft_eq_mul {X : Over (Spec (.of k))} (x : X ⟶ G)
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : x ≫ GrpObj.mulLeft G g = (toUnit X ≫ g) * x := by
  rw [mulLeft_eq_mul, MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit G),
    Category.comp_id]

/-- Right translation of a generalized point `x` by `g` is `x * g`. -/
lemma GrpObj.comp_mulRight_eq_mul {X : Over (Spec (.of k))} (x : X ⟶ G)
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : x ≫ GrpObj.mulRight G g = x * (toUnit X ≫ g) := by
  rw [mulRight_eq_mul, MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit G),
    Category.comp_id]

/-- A homomorphism of group schemes intertwines the left translations by `g` and by its image. -/
lemma GrpObj.mulLeft_comp_of_isMonHom {H : Over (Spec (.of k))} [GrpObj H] (f : G ⟶ H)
    [IsMonHom f] (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    GrpObj.mulLeft G g ≫ f = f ≫ GrpObj.mulLeft H (g ≫ f) := by
  rw [comp_mulLeft_eq_mul, mulLeft_eq_mul, MonObj.mul_comp, Category.id_comp, Category.assoc]

/-- A homomorphism of group schemes intertwines the right translations by `g` and by its image. -/
lemma GrpObj.mulRight_comp_of_isMonHom {H : Over (Spec (.of k))} [GrpObj H] (f : G ⟶ H)
    [IsMonHom f] (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    GrpObj.mulRight G g ≫ f = f ≫ GrpObj.mulRight H (g ≫ f) := by
  rw [comp_mulRight_eq_mul, mulRight_eq_mul, MonObj.mul_comp, Category.id_comp, Category.assoc]

end Translation

/-- A group scheme of finite type over a field has finitely many connected components.
(blueprint: `lemma-connected-components-images-homomorphisms`) -/
theorem finite_connectedComponents (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    Finite (_root_.ConnectedComponents G.left) :=
  have := isNoetherian_left G
  inferInstance

/-- The connected component of the identity of a group scheme of finite type over a field is open.
(blueprint: `lemma-connected-components-images-homomorphisms`) -/
theorem isOpen_connectedComponent_onePoint (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    IsOpen (connectedComponent (GrpObj.onePoint G)) :=
  have := isNoetherian_left G
  TopologicalSpace.NoetherianSpace.isOpen_connectedComponent _

/-- The identity component `G°` of a group scheme `G` of finite type over a field, as an open
subset of `G`: the connected component of the identity point. (blueprint:
`lemma-connected-components-images-homomorphisms`) -/
noncomputable def GrpObj.identityComponentOpens (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] : G.left.Opens :=
  ⟨connectedComponent (GrpObj.onePoint G), isOpen_connectedComponent_onePoint G⟩

section AlgClosed

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field `K`, the `K`-rational point of a group scheme `G` locally of
finite type through a closed point `x`, as a section `𝟙_ ⟶ G`. -/
noncomputable def GrpObj.sectionOfIsClosed (G : Over (Spec (.of K))) [LocallyOfFiniteType G.hom]
    (x : G.left) (hx : IsClosed {x}) : 𝟙_ (Over (Spec (.of K))) ⟶ G :=
  Over.homMk (pointOfClosedPoint G.hom x hx) (pointOfClosedPoint_comp G.hom x hx)

theorem GrpObj.sectionOfIsClosed_left_apply (G : Over (Spec (.of K))) [LocallyOfFiniteType G.hom]
    (x : G.left) (hx : IsClosed {x}) (a : Spec (.of K)) :
    (GrpObj.sectionOfIsClosed G x hx).left a = x :=
  pointOfClosedPoint_apply G.hom x hx a

/-- Over an algebraically closed field, the left translations of a group scheme locally of finite
type act transitively on its closed points. -/
theorem GrpObj.exists_homeomorph_apply_eq (G : Over (Spec (.of K))) [GrpObj G]
    [LocallyOfFiniteType G.hom] {x y : G.left} (hx : IsClosed {x}) (hy : IsClosed {y}) :
    ∃ φ : G.left ≃ₜ G.left, φ x = y := by
  set sx := GrpObj.sectionOfIsClosed G x hx
  set sy := GrpObj.sectionOfIsClosed G y hy
  have := GrpObj.isIso_mulLeft_left G (sy * sx⁻¹)
  refine ⟨(GrpObj.mulLeft G (sy * sx⁻¹)).left.homeomorph, ?_⟩
  have hcomp : sx ≫ GrpObj.mulLeft G (sy * sx⁻¹) = sy := by
    change sx ≫ ((toUnit G ≫ (sy * sx⁻¹)) * 𝟙 G) = sy
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (sx ≫ toUnit G) (𝟙 _),
      Category.id_comp, Category.comp_id, inv_mul_cancel_right]
  obtain ⟨a⟩ : Nonempty (Spec (.of K)) := inferInstance
  rw [Scheme.Hom.homeomorph_apply, ← GrpObj.sectionOfIsClosed_left_apply G x hx a,
    ← Scheme.Hom.comp_apply, ← Over.comp_left, hcomp, GrpObj.sectionOfIsClosed_left_apply]

/-- **A connected group scheme over an algebraically closed field is irreducible.** Some closed
point lies in a single irreducible component; the translations act transitively on the closed
points, so every closed point, hence every point, lies in a single irreducible component. Each
point then has an irreducible open neighbourhood, and a connected space with this property is
irreducible. -/
theorem irreducibleSpace_of_connectedSpace_of_isAlgClosed (G : Over (Spec (.of K))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [ConnectedSpace G.left] : IrreducibleSpace G.left := by
  have := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  let P (x : G.left) : Prop := ∀ Z₁ ∈ irreducibleComponents G.left,
    ∀ Z₂ ∈ irreducibleComponents G.left, x ∈ Z₁ → x ∈ Z₂ → Z₁ = Z₂
  -- some closed point lies in a single irreducible component
  have hA : ∃ p ∈ closedPoints G.left, P p := by
    obtain ⟨x₀⟩ := ‹ConnectedSpace G.left›.toNonempty
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
    have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : TopologicalSpace.NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
    have : Nonempty V := ⟨⟨x₀, hxV⟩⟩
    obtain ⟨U, hU, hUne, hUuniq⟩ :=
      TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_forall_eq (α := V)
    have hU' : IsOpen (((↑) : V → G.left) '' U) := V.2.isOpenMap_subtype_val U hU
    obtain ⟨p, ⟨⟨p, hpV⟩, hpU, rfl⟩, hp⟩ :=
      nonempty_inter_closedPoints (hUne.image _) hU'.isLocallyClosed
    refine ⟨_, hp, fun Z₁ hZ₁ Z₂ hZ₂ h₁ h₂ ↦ ?_⟩
    have hV' := V.2.isOpenEmbedding_subtypeVal
    have key := hUuniq ⟨p, hpV⟩ hpU _ (preimage_mem_irreducibleComponents hZ₁ hV'
      ⟨p, h₁, ⟨p, hpV⟩, rfl⟩) _ (preimage_mem_irreducibleComponents hZ₂ hV'
      ⟨p, h₂, ⟨p, hpV⟩, rfl⟩) h₁ h₂
    have hcl (Z : Set G.left) (hZ : Z ∈ irreducibleComponents G.left) (hp : p ∈ Z) :
        Z = closure (Z ∩ V) := by
      refine (subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2 V.2 ⟨p, hp, hpV⟩).antisymm
        (closure_minimal Set.inter_subset_left (isClosed_of_mem_irreducibleComponents Z hZ))
    have hZV : Z₁ ∩ V = Z₂ ∩ V := Set.ext fun y ↦
      ⟨fun ⟨hy, hyV⟩ ↦ ⟨(Set.ext_iff.1 key ⟨y, hyV⟩).1 hy, hyV⟩,
        fun ⟨hy, hyV⟩ ↦ ⟨(Set.ext_iff.1 key ⟨y, hyV⟩).2 hy, hyV⟩⟩
    calc Z₁ = closure (Z₁ ∩ V) := hcl Z₁ hZ₁ h₁
      _ = closure (Z₂ ∩ V) := by rw [hZV]
      _ = Z₂ := (hcl Z₂ hZ₂ h₂).symm
  -- every closed point lies in a single irreducible component
  have hB (q : G.left) (hq : q ∈ closedPoints G.left) : P q := by
    obtain ⟨p, hp, hP⟩ := hA
    obtain ⟨φ, hφ⟩ := GrpObj.exists_homeomorph_apply_eq G hq hp
    intro Z₁ hZ₁ Z₂ hZ₂ h₁ h₂
    exact φ.injective.image_injective (hP _ (φ.image_mem_irreducibleComponents hZ₁) _
      (φ.image_mem_irreducibleComponents hZ₂) ⟨q, h₁, hφ⟩ ⟨q, h₂, hφ⟩)
  -- every point lies in a single irreducible component
  have hC (x : G.left) : P x := by
    obtain ⟨q, hqx, hq⟩ := nonempty_inter_closedPoints (Z := closure {x})
      ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    intro Z₁ hZ₁ Z₂ hZ₂ h₁ h₂
    exact hB q hq Z₁ hZ₁ Z₂ hZ₂
      (closure_minimal (Set.singleton_subset_iff.2 h₁) (isClosed_of_mem_irreducibleComponents _ hZ₁)
        hqx)
      (closure_minimal (Set.singleton_subset_iff.2 h₂) (isClosed_of_mem_irreducibleComponents _ hZ₂)
        hqx)
  refine irreducibleSpace_of_forall_exists_isPreirreducible fun x ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hVN : TopologicalSpace.NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
  have hV' := V.2.isOpenEmbedding_subtypeVal
  obtain ⟨U, hU, hxU, hUirr⟩ :=
    @TopologicalSpace.NoetherianSpace.exists_isOpen_isPreirreducible V _ hVN (⟨x, hxV⟩ : V)
      fun W₁ hW₁ W₂ hW₂ hx₁ hx₂ ↦ by
        have hW (W : Set V) (hW : W ∈ irreducibleComponents V) (hxW : ⟨x, hxV⟩ ∈ W) :
            ∃ Z ∈ irreducibleComponents G.left, x ∈ Z ∧ W = ((↑) : V → G.left) ⁻¹' Z := by
          obtain ⟨Z, hZ, hWZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
            (hW.1.image _ continuous_subtype_val.continuousOn).closure
          have hsub : W ⊆ ((↑) : V → G.left) ⁻¹' Z := fun w hw ↦ hWZ (subset_closure ⟨w, hw, rfl⟩)
          have hxZ : x ∈ Z := hsub hxW
          have hpre := preimage_mem_irreducibleComponents hZ hV' ⟨x, hxZ, ⟨x, hxV⟩, rfl⟩
          exact ⟨Z, hZ, hxZ, hsub.antisymm (hW.2 hpre.1 hsub)⟩
        obtain ⟨Z₁, hZ₁, hxZ₁, rfl⟩ := hW W₁ hW₁ hx₁
        obtain ⟨Z₂, hZ₂, hxZ₂, rfl⟩ := hW W₂ hW₂ hx₂
        rw [hC x Z₁ hZ₁ Z₂ hZ₂ hxZ₁ hxZ₂]
  exact ⟨((↑) : V → G.left) '' U, V.2.isOpenMap_subtype_val U hU, ⟨_, hxU, rfl⟩,
    hUirr.image _ continuous_subtype_val.continuousOn⟩

end AlgClosed

/-- A connected group scheme locally of finite type over a field is irreducible (SGA 3, VI_A,
Proposition 2.4).

Having the rational point `e`, the connected scheme `G` is geometrically connected
(`GeometricallyConnected.of_connectedSpace_of_section`), so its base change to an algebraic
closure is connected, hence irreducible (`irreducibleSpace_of_connectedSpace_of_isAlgClosed`);
`G` is the image of this base change. (blueprint:
`lemma-connected-components-images-homomorphisms`) -/
theorem irreducibleSpace_of_connectedSpace (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [ConnectedSpace G.left] : IrreducibleSpace G.left := by
  let g : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  let : GrpObj (Over.mk (Limits.pullback.snd G.hom g)) := Over.grpObjMkPullbackSnd
  have hG : GeometricallyConnected G.hom :=
    GeometricallyConnected.of_connectedSpace_of_section G.hom η[G].left (by simp)
  have : ConnectedSpace (Over.mk (Limits.pullback.snd G.hom g)).left :=
    hG.geometrically_connectedSpace g _ _ (IsPullback.of_hasPullback G.hom g)
  have : LocallyOfFiniteType (Over.mk (Limits.pullback.snd G.hom g)).hom :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd G.hom g))
  have : IrreducibleSpace ↥(Limits.pullback G.hom g) :=
    irreducibleSpace_of_connectedSpace_of_isAlgClosed (Over.mk (Limits.pullback.snd G.hom g))
  have : Surjective g := ⟨fun x ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  have hsurj : Function.Surjective (Limits.pullback.fst G.hom g) :=
    (MorphismProperty.pullback_fst (P := @Surjective) G.hom g this).surj
  have := (IrreducibleSpace.isIrreducible_univ ↥(Limits.pullback G.hom g)).image _
    (Limits.pullback.fst G.hom g).continuous.continuousOn
  rw [Set.image_univ, hsurj.range_eq] at this
  exact (irreducibleSpace_def _).2 this

/-- Let `X` and `Y` be schemes over a field `k` with `Y` geometrically connected, and let `y` be a
rational point of `Y`. A morphism `f : X ⊗ Y ⟶ Z` which maps the slice `X × {y}` into a clopen
subset `C` of `Z` maps all of `X ⊗ Y` into `C`: the fibres of the projection `X ⊗ Y ⟶ X` are
connected and each of them meets the slice. -/
theorem range_subset_of_isClopen_of_range_lift_subset {X Y Z : Over (Spec (.of k))}
    [GeometricallyConnected Y.hom] (f : X ⊗ Y ⟶ Z) (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    {C : Set Z.left} (hC : IsClopen C)
    (h : Set.range (lift (𝟙 X) (toUnit X ≫ y) ≫ f).left.base ⊆ C) :
    Set.range f.left.base ⊆ C := by
  rintro _ ⟨z, rfl⟩
  have : GeometricallyConnected (fst X Y).left :=
    inferInstanceAs (GeometricallyConnected (Limits.pullback.fst X.hom Y.hom))
  have hs : (fst X Y).left ((lift (𝟙 X) (toUnit X ≫ y)).left ((fst X Y).left z)) =
      (fst X Y).left z := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst, Over.id_left]
    rfl
  have hsub : (fst X Y).left ⁻¹' {(fst X Y).left z} ⊆ f.left ⁻¹' C :=
    ((fst X Y).left.isConnected_preimage_singleton _).isPreconnected.subset_isClopen
      (hC.preimage f.left.continuous) ⟨_, hs, h ⟨(fst X Y).left z, by
        rw [Over.comp_left, Scheme.Hom.comp_apply]⟩⟩
  exact hsub rfl

section IdentityComponent

variable (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]

/-- The identity component `G°` of a group scheme `G` of finite type over a field, as a scheme
over `k`: the open subscheme of `G` on the connected component of the identity point. The set
`π₀(G)` of connected components is `ConnectedComponents G.left`.
(blueprint: `lemma-connected-components-images-homomorphisms`, `def-wf-algebraic-components`) -/
noncomputable abbrev GrpObj.identityComponent : Over (Spec (.of k)) :=
  Over.mk ((GrpObj.identityComponentOpens G).ι ≫ G.hom)

/-- The open immersion `G° ⟶ G` of the identity component into `G`, as a morphism over `k`.
(blueprint: `lemma-connected-components-images-homomorphisms`) -/
noncomputable def GrpObj.identityComponentι : GrpObj.identityComponent G ⟶ G :=
  Over.homMk (GrpObj.identityComponentOpens G).ι

instance : IsOpenImmersion (GrpObj.identityComponentι G).left :=
  inferInstanceAs (IsOpenImmersion (GrpObj.identityComponentOpens G).ι)

instance : Mono (GrpObj.identityComponentι G) :=
  Over.mono_of_mono_left _

/-- The image of `G° ⟶ G` is the connected component of the identity point. -/
theorem GrpObj.range_identityComponentι :
    Set.range (GrpObj.identityComponentι G).left.base =
      connectedComponent (GrpObj.onePoint G) :=
  Scheme.Opens.range_ι _

/-- A morphism `X ⟶ G` over `k` whose image lies in the connected component of the identity
factors (uniquely, as `G° ⟶ G` is a monomorphism) through the open subscheme `G°`. -/
noncomputable def GrpObj.identityComponentLift {X : Over (Spec (.of k))} (f : X ⟶ G)
    (hf : Set.range f.left.base ⊆ connectedComponent (GrpObj.onePoint G)) :
    X ⟶ GrpObj.identityComponent G :=
  Over.homMk (IsOpenImmersion.lift (GrpObj.identityComponentOpens G).ι f.left
      (hf.trans (Scheme.Opens.range_ι (GrpObj.identityComponentOpens G)).symm.subset))
    ((IsOpenImmersion.lift_fac_assoc (GrpObj.identityComponentOpens G).ι f.left _ _).trans
      (Over.w f))

@[reassoc (attr := simp)]
theorem GrpObj.identityComponentLift_comp_identityComponentι {X : Over (Spec (.of k))}
    (f : X ⟶ G) (hf : Set.range f.left.base ⊆ connectedComponent (GrpObj.onePoint G)) :
    GrpObj.identityComponentLift G f hf ≫ GrpObj.identityComponentι G = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (GrpObj.identityComponentOpens G).ι f.left _

omit [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] in
/-- The unit section of `G` lands in the identity component. -/
theorem GrpObj.range_one_subset_connectedComponent :
    Set.range η[G].left.base ⊆ connectedComponent (GrpObj.onePoint G) := by
  rintro _ ⟨x, rfl⟩
  obtain rfl : x = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) :=
    Subsingleton.elim (α := PrimeSpectrum k) _ _
  exact mem_connectedComponent

/-- The unit section of `G`, as a rational point of the identity component `G°`. -/
noncomputable def GrpObj.identityComponentOne :
    𝟙_ (Over (Spec (.of k))) ⟶ GrpObj.identityComponent G :=
  GrpObj.identityComponentLift G η[G] (GrpObj.range_one_subset_connectedComponent G)

@[reassoc (attr := simp)]
theorem GrpObj.identityComponentOne_comp_identityComponentι :
    GrpObj.identityComponentOne G ≫ GrpObj.identityComponentι G = η[G] :=
  GrpObj.identityComponentLift_comp_identityComponentι G _ _

instance : ConnectedSpace (GrpObj.identityComponent G).left :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

/-- The identity component is geometrically connected: it is connected and has a rational point. -/
instance : GeometricallyConnected (GrpObj.identityComponent G).hom :=
  GeometricallyConnected.of_connectedSpace_of_section _ (GrpObj.identityComponentOne G).left
    (Over.w (GrpObj.identityComponentOne G))

theorem GrpObj.isClopen_connectedComponent_onePoint :
    IsClopen (connectedComponent (GrpObj.onePoint G)) :=
  ⟨isClosed_connectedComponent, isOpen_connectedComponent_onePoint G⟩

/-- Multiplication `G° × G° ⟶ G` lands in the identity component: the product of two connected
schemes with rational points is connected, and its image contains the identity.
(blueprint: `lemma-connected-components-images-homomorphisms`) -/
theorem GrpObj.range_mul_subset_connectedComponent :
    Set.range ((GrpObj.identityComponentι G ⊗ₘ GrpObj.identityComponentι G) ≫ μ[G]).left.base ⊆
      connectedComponent (GrpObj.onePoint G) := by
  refine range_subset_of_isClopen_of_range_lift_subset _ (GrpObj.identityComponentOne G)
    (GrpObj.isClopen_connectedComponent_onePoint G) ?_
  have : lift (𝟙 _) (toUnit _ ≫ GrpObj.identityComponentOne G) ≫
      (GrpObj.identityComponentι G ⊗ₘ GrpObj.identityComponentι G) ≫ μ[G] =
        GrpObj.identityComponentι G := by
    rw [lift_map_assoc, Category.assoc, GrpObj.identityComponentOne_comp_identityComponentι,
      Category.id_comp, ← Hom.mul_def, ← Hom.one_def, mul_one]
  rw [this, GrpObj.range_identityComponentι]

/-- Inversion maps the identity component into itself. (blueprint:
`lemma-connected-components-images-homomorphisms`) -/
theorem GrpObj.range_inv_subset_connectedComponent :
    Set.range (GrpObj.identityComponentι G ≫ ι[G]).left.base ⊆
      connectedComponent (GrpObj.onePoint G) := by
  refine (isConnected_range (GrpObj.identityComponentι G ≫ ι[G]).left.continuous).isPreconnected
    |>.subset_connectedComponent ⟨(GrpObj.identityComponentOne G).left
      (show Spec (.of k) from ⟨⊥, Ideal.isPrime_bot⟩), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left,
    GrpObj.identityComponentOne_comp_identityComponentι_assoc, GrpObj.one_inv]
  rfl

/-- Conjugation `G × G° ⟶ G`, `(g, h) ↦ g * h * g⁻¹`, lands in the identity component: each
fibre `g G° g⁻¹` is connected and contains the identity. (blueprint:
`lemma-connected-components-images-homomorphisms`) -/
theorem GrpObj.range_conj_subset_connectedComponent :
    Set.range ((G ◁ GrpObj.identityComponentι G) ≫ GrpObj.conj G).left.base ⊆
      connectedComponent (GrpObj.onePoint G) := by
  refine range_subset_of_isClopen_of_range_lift_subset _ (GrpObj.identityComponentOne G)
    (GrpObj.isClopen_connectedComponent_onePoint G) ?_
  have : lift (𝟙 _) (toUnit _ ≫ GrpObj.identityComponentOne G) ≫
      (G ◁ GrpObj.identityComponentι G) ≫ GrpObj.conj G = toUnit G ≫ η[G] := by
    rw [lift_whiskerLeft_assoc, Category.assoc,
      GrpObj.identityComponentOne_comp_identityComponentι, GrpObj.lift_conj_eq_mul_mul_inv,
      ← Hom.one_def, mul_one, mul_inv_cancel, Hom.one_def]
  rw [this]
  rintro _ ⟨x, rfl⟩
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  exact GrpObj.range_one_subset_connectedComponent G ⟨_, rfl⟩

/-- The identity component `G°` is an open subgroup scheme of `G`: the unit, multiplication and
inversion of `G` restrict to `G°`, and the group axioms follow from those of `G` since `G° ⟶ G`
is a monomorphism. (blueprint: `lemma-connected-components-images-homomorphisms`) -/
noncomputable instance : GrpObj (GrpObj.identityComponent G) where
  one := GrpObj.identityComponentLift G η[G] (GrpObj.range_one_subset_connectedComponent G)
  mul := GrpObj.identityComponentLift G
    ((GrpObj.identityComponentι G ⊗ₘ GrpObj.identityComponentι G) ≫ μ[G])
    (GrpObj.range_mul_subset_connectedComponent G)
  inv := GrpObj.identityComponentLift G (GrpObj.identityComponentι G ≫ ι[G])
    (GrpObj.range_inv_subset_connectedComponent G)
  one_mul := by
    rw [← cancel_mono (GrpObj.identityComponentι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, leftUnitor_hom,
      toUnit_unique _ (toUnit _), ← Hom.one_def]
  mul_one := by
    rw [← cancel_mono (GrpObj.identityComponentι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, rightUnitor_hom,
      toUnit_unique _ (toUnit _), ← Hom.one_def]
  mul_assoc := by
    rw [← cancel_mono (GrpObj.identityComponentι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, mul_assoc]
  left_inv := by
    rw [← cancel_mono (GrpObj.identityComponentι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, ← Hom.inv_def, ← Hom.one_def]
  right_inv := by
    rw [← cancel_mono (GrpObj.identityComponentι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, ← Hom.inv_def, ← Hom.one_def]

/-- The inclusion `G° ⟶ G` of the identity component is a homomorphism of group schemes. -/
instance : IsMonHom (GrpObj.identityComponentι G) where
  one_hom := GrpObj.identityComponentLift_comp_identityComponentι G _ _
  mul_hom := GrpObj.identityComponentLift_comp_identityComponentι G _ _

/-- The identity component `G°` is a normal subgroup scheme of `G`: the conjugation morphism
`G × G° ⟶ G` factors through `G° ⟶ G`. (blueprint:
`lemma-connected-components-images-homomorphisms`) -/
instance : IsMonHom.Normal (GrpObj.identityComponentι G) where
  exists_comp_eq_conj :=
    ⟨GrpObj.identityComponentLift G _ (GrpObj.range_conj_subset_connectedComponent G),
      GrpObj.identityComponentLift_comp_identityComponentι G _ _⟩

/-- The identity component `G°` of a group scheme of finite type over a field is irreducible.
(blueprint: `lemma-connected-components-images-homomorphisms`) -/
theorem GrpObj.irreducibleSpace_identityComponent :
    IrreducibleSpace (GrpObj.identityComponent G).left :=
  have : LocallyOfFiniteType (GrpObj.identityComponent G).hom :=
    inferInstanceAs (LocallyOfFiniteType ((GrpObj.identityComponentOpens G).ι ≫ G.hom))
  irreducibleSpace_of_connectedSpace (GrpObj.identityComponent G)

/-- The rational points of the identity component `G°` have finite index in the rational points
of `G`. (blueprint: `lemma-connected-components-images-homomorphisms`) -/
theorem GrpObj.finiteIndex_range_identityComponentι :
    (IsMonHom.monoidHom (GrpObj.identityComponentι G)
      (𝟙_ (Over (Spec (.of k))))).range.FiniteIndex := by
  set H := (IsMonHom.monoidHom (GrpObj.identityComponentι G) (𝟙_ (Over (Spec (.of k))))).range
  let pt : Spec (.of k) := ⟨⊥, Ideal.isPrime_bot⟩
  -- two rational points in the same connected component differ by a point of `G°`
  have key (a b : 𝟙_ (Over (Spec (.of k))) ⟶ G)
      (hab : (a.left pt : _root_.ConnectedComponents G.left) = b.left pt) : a⁻¹ * b ∈ H := by
    have hb : b ≫ GrpObj.mulLeft G a⁻¹ = a⁻¹ * b := by
      rw [GrpObj.mulLeft_eq_mul, MonObj.comp_mul, ← Category.assoc,
        toUnit_unique (b ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id]
    have ha : a ≫ GrpObj.mulLeft G a⁻¹ = 1 := by
      rw [GrpObj.mulLeft_eq_mul, MonObj.comp_mul, ← Category.assoc,
        toUnit_unique (a ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id, inv_mul_cancel]
    have hsub : Set.range (a⁻¹ * b).left.base ⊆ connectedComponent (GrpObj.onePoint G) := by
      rintro _ ⟨x, rfl⟩
      obtain rfl : x = pt := Subsingleton.elim (α := PrimeSpectrum k) _ _
      have h1 : (GrpObj.mulLeft G a⁻¹).left (a.left pt) = GrpObj.onePoint G := by
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ha]
        change (toUnit (𝟙_ (Over (Spec (.of k)))) ≫ η[G]).left pt = _
        rw [toUnit_unit, Category.id_comp]
        rfl
      rw [← hb, Over.comp_left, Scheme.Hom.comp_apply, ← h1]
      exact (GrpObj.mulLeft G a⁻¹).left.continuous.image_connectedComponent_subset _
        ⟨_, ConnectedComponents.coe_eq_coe'.mp hab.symm, rfl⟩
    exact ⟨GrpObj.identityComponentLift G _ hsub,
      GrpObj.identityComponentLift_comp_identityComponentι G _ hsub⟩
  have := finite_connectedComponents G
  have : Finite ((𝟙_ (Over (Spec (.of k))) ⟶ G) ⧸ H) := by
    refine Finite.of_injective (fun q ↦ ((Quotient.out q).left pt :
      _root_.ConnectedComponents G.left)) fun q q' hqq' ↦ ?_
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
    exact key _ _ hqq'
  exact Subgroup.finiteIndex_of_finite_quotient

omit [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] in
/-- The connected components of a group scheme `G` of finite type over a field are the translates
of the identity component: left translation by a rational point `g` maps `G°` onto the connected
component of the point `g * 1 = g`. (blueprint:
`lemma-connected-components-images-homomorphisms`) -/
theorem GrpObj.image_mulLeft_connectedComponent_onePoint (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (GrpObj.mulLeft G g).left.base '' connectedComponent (GrpObj.onePoint G) =
      connectedComponent ((GrpObj.mulLeft G g).left.base (GrpObj.onePoint G)) := by
  have := GrpObj.isIso_mulLeft_left G g
  simpa [connectedComponentIn_univ] using
    (GrpObj.mulLeft G g).left.homeomorph.image_connectedComponentIn
      (Set.mem_univ (GrpObj.onePoint G))

end IdentityComponent

/-- Cartier's theorem: a group scheme locally of finite type over a field of characteristic zero
is reduced (indeed smooth). (blueprint: `proposition-cartier-s-theorem`) -/
theorem GrpObj.isReduced_of_charZero [CharZero k] (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] : IsReduced G.left :=
  let : GrpObj (Over.mk G.hom) := ‹GrpObj G›
  isReduced_of_grpObj G.hom

/-- Let `V` be an open subset of a space `X` and `s ⊆ X`. If some open subset of `V` meets the
closure of `s ∩ V` in `V` inside `s`, then some open subset of `X` meets the closure of `s` in a
nonempty subset of `s`. -/
theorem exists_isOpen_inter_closure_subset_of_subtype {X : Type*} [TopologicalSpace X]
    {V s : Set X} (hV : IsOpen V) {u : Set V} (hu : IsOpen u)
    (hne : (u ∩ closure (Subtype.val ⁻¹' s)).Nonempty)
    (hsub : u ∩ closure (Subtype.val ⁻¹' s) ⊆ Subtype.val ⁻¹' s) :
    ∃ u : Set X, IsOpen u ∧ (u ∩ closure s).Nonempty ∧ u ∩ closure s ⊆ s := by
  refine ⟨Subtype.val '' u, hV.isOpenMap_subtype_val u hu, ?_, ?_⟩
  · obtain ⟨p, hpu, hp⟩ := hne
    exact ⟨p, ⟨p, hpu, rfl⟩, continuous_subtype_val.closure_preimage_subset s hp⟩
  · rintro _ ⟨⟨p, hpu, rfl⟩, hp⟩
    refine hsub ⟨hpu, closure_subtype.mpr ?_⟩
    rw [Subtype.image_preimage_coe]
    exact hV.inter_closure ⟨p.2, hp⟩

/-- A consequence of **Chevalley's theorem**: the image of a quasi-compact morphism locally of
finite type from a nonempty scheme to a locally noetherian scheme contains a nonempty open subset
of its closure. -/
theorem Scheme.Hom.exists_isOpen_inter_closure_range_subset {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsLocallyNoetherian Y] [Nonempty X] :
    ∃ u : Set Y, IsOpen u ∧ (u ∩ closure (Set.range f)).Nonempty ∧
      u ∩ closure (Set.range f) ⊆ Set.range f := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  have : IsAffine V := hV
  have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : TopologicalSpace.NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
  have hr : Set.range (f ∣_ V) = Subtype.val ⁻¹' Set.range f := by
    ext y
    refine ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, (morphismRestrict_base_coe f V z).symm⟩
    · rintro ⟨z, hz⟩
      refine ⟨⟨z, show f z ∈ V from hz ▸ y.2⟩, Subtype.ext ?_⟩
      rw [morphismRestrict_base_coe, hz]
  have hc : Topology.IsConstructible (Set.range (f ∣_ V)) := by
    rw [← Set.image_univ]
    exact (f ∣_ V).isConstructible_image .univ
  obtain ⟨u, hu, hne, hsub⟩ := exists_isOpen_inter_closure_subset_of_isConstructible hc
    (Set.range_nonempty_iff_nonempty.mpr ⟨⟨x, hxV⟩⟩)
  rw [hr] at hne hsub
  exact exists_isOpen_inter_closure_subset_of_subtype V.2 hu hne hsub

/-- The image of a homomorphism from a group scheme of finite type to a group scheme locally of
finite type over an algebraically closed field `K` is closed.

Let `S` be the image and `Z` its closure. By Chevalley's theorem `S` contains a nonempty open
subset `U` of `Z`; the translates of `U` by the rational points of `S` cover the closed points of
`S`, so their union `U'` is a dense open subset of `Z` contained in `S`. If `Z ⊄ U'`, pick a closed
point `y ∈ Z \ U'`. Then `y U'` and `U'` are open in `Z` and meet in a closed point `w = y x`,
with `x, w` rational points of `S`, so `y = w x⁻¹ ∈ S ⊆ U'`, a contradiction. -/
theorem isClosed_range_of_isMonHom_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    {G H : Over (Spec (.of K))} [GrpObj G] [GrpObj H] [LocallyOfFiniteType G.hom]
    [QuasiCompact G.hom] [LocallyOfFiniteType H.hom] (f : G ⟶ H) [IsMonHom f] :
    IsClosed (Set.range f.left) := by
  classical
  have := isNoetherian_left G
  have := LocallyOfFiniteType.isLocallyNoetherian H.hom
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  have : JacobsonSpace H.left := LocallyOfFiniteType.jacobsonSpace H.hom
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ H.hom) := by rw [Over.w f]; infer_instance
    exact locallyOfFiniteType_of_comp f.left H.hom
  set S := Set.range f.left with hS
  set Z := closure S with hZ
  let pt : Spec (.of K) := IsLocalRing.closedPoint K
  -- rational points of `H` are its closed points
  have hcl (s : 𝟙_ (Over (Spec (.of K))) ⟶ H) : IsClosed {s.left pt} :=
    (pointEquivClosedPoint H.hom ⟨s.left, Over.w s⟩).2
  have hext {s t : 𝟙_ (Over (Spec (.of K))) ⟶ H} (h : s.left pt = t.left pt) : s = t :=
    Over.OverMorphism.ext (ext_of_apply_closedPoint_eq H.hom (Over.w s) (Over.w t) h)
  have hsec (y : H.left) (hy : IsClosed {y}) : (GrpObj.sectionOfIsClosed H y hy).left pt = y :=
    GrpObj.sectionOfIsClosed_left_apply H y hy pt
  have happ {X Y : Over (Spec (.of K))} (a : 𝟙_ (Over (Spec (.of K))) ⟶ X) (b : X ⟶ Y) :
      (a ≫ b).left pt = b.left (a.left pt) := by
    rw [Over.comp_left, Scheme.Hom.comp_apply]
  -- the rational points of `S` form the subgroup `P`, the image of `G(K)`
  set P := (IsMonHom.monoidHom f (𝟙_ (Over (Spec (.of K))))).range with hP
  have hmemP (s : 𝟙_ (Over (Spec (.of K))) ⟶ H) : s ∈ P ↔ s.left pt ∈ S := by
    refine ⟨?_, fun hs ↦ ?_⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g.left pt, (happ g f).symm⟩
    obtain ⟨x, hx, hxcl⟩ := nonempty_inter_closedPoints (Z := f.left ⁻¹' {s.left pt})
      (by obtain ⟨x, hx⟩ := hs; exact ⟨x, hx⟩) ((hcl s).preimage f.left.continuous).isLocallyClosed
    refine ⟨GrpObj.sectionOfIsClosed G x hxcl, hext ?_⟩
    rw [IsMonHom.monoidHom_apply, happ, GrpObj.sectionOfIsClosed_left_apply]
    exact hx
  have hSpt (y : H.left) (hyS : y ∈ S) (hy : IsClosed {y}) :
      GrpObj.sectionOfIsClosed H y hy ∈ P := by
    rw [hmemP, hsec]
    exact hyS
  -- the closed points of `S` are dense in `S`
  have hdense : S ⊆ closure (S ∩ closedPoints H.left) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ closure (closedPoints G.left) := by rw [closure_closedPoints]; trivial
    refine (image_closure_subset_closure_image f.left.continuous) ⟨x, hx, rfl⟩ |> closure_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rw [← GrpObj.sectionOfIsClosed_left_apply G x hx pt, ← happ]
    exact hcl _
  -- translations by rational points of `S` and the inversion preserve `S` and `Z`
  have hclosure {φ : H.left ⟶ H.left} (h : φ '' S ⊆ S) : φ '' Z ⊆ Z :=
    (image_closure_subset_closure_image φ.continuous).trans (closure_mono h)
  have hLS {s} (hs : s ∈ P) : (GrpObj.mulLeft H s).left '' S ⊆ S := by
    obtain ⟨g, rfl⟩ := hs
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨(GrpObj.mulLeft G g).left x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.mulLeft_comp_of_isMonHom,
      Over.comp_left, Scheme.Hom.comp_apply, IsMonHom.monoidHom_apply]
  have hRS {s} (hs : s ∈ P) : (GrpObj.mulRight H s).left '' S ⊆ S := by
    obtain ⟨g, rfl⟩ := hs
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨(GrpObj.mulRight G g).left x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.mulRight_comp_of_isMonHom,
      Over.comp_left, Scheme.Hom.comp_apply, IsMonHom.monoidHom_apply]
  have hιS : ι[H].left '' S ⊆ S := by
    have : ι[G] ≫ f = f ≫ ι[H] := by
      calc ι[G] ≫ f = (𝟙 G)⁻¹ ≫ f := by rw [Hom.inv_def, Category.id_comp]
        _ = (𝟙 G ≫ f)⁻¹ := GrpObj.inv_comp _ _
        _ = f ≫ ι[H] := by rw [Category.id_comp, Hom.inv_def]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨ι[G].left x, by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, this, Over.comp_left,
      Scheme.Hom.comp_apply]⟩
  -- left translation by a rational point of `Z` preserves `Z`
  have hLZ (a : 𝟙_ (Over (Spec (.of K))) ⟶ H) (ha : a.left pt ∈ Z) :
      (GrpObj.mulLeft H a).left '' Z ⊆ Z := by
    refine (image_closure_subset_closure_image (GrpObj.mulLeft H a).left.continuous).trans
      (closure_minimal ?_ isClosed_closure)
    refine (Set.image_mono hdense).trans
      ((image_closure_subset_closure_image (GrpObj.mulLeft H a).left.continuous).trans
      (closure_minimal ?_ isClosed_closure))
    rintro _ ⟨y, ⟨hyS, hycl⟩, rfl⟩
    have hy := hSpt y hyS hycl
    have e : a * GrpObj.sectionOfIsClosed H y hycl =
        a ≫ GrpObj.mulRight H (GrpObj.sectionOfIsClosed H y hycl) := by
      rw [GrpObj.comp_mulRight_eq_mul, toUnit_unit, Category.id_comp]
    rw [← hsec y hycl, ← happ, GrpObj.comp_mulLeft_eq_mul, toUnit_unit, Category.id_comp, e, happ]
    exact hclosure (hRS hy) ⟨_, ha, rfl⟩
  have hιZ : ι[H].left '' Z ⊆ Z := hclosure hιS
  have hLiso (s : 𝟙_ (Over (Spec (.of K))) ⟶ H) : IsIso (GrpObj.mulLeft H s).left :=
    GrpObj.isIso_mulLeft_left H s
  have hLinv (s : 𝟙_ (Over (Spec (.of K))) ⟶ H) (x : H.left) :
      (GrpObj.mulLeft H s⁻¹).left ((GrpObj.mulLeft H s).left x) = x := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.mulLeft_comp_mulLeft, inv_mul_cancel,
      GrpObj.mulLeft_one]
    rfl
  -- Chevalley: `S` contains a nonempty open subset `u ∩ Z` of `Z`
  have : Nonempty G.left := ⟨η[G].left pt⟩
  obtain ⟨u, hu, hune, huS⟩ := f.left.exists_isOpen_inter_closure_range_subset
  obtain ⟨x₀, hx₀, hx₀cl⟩ := nonempty_inter_closedPoints hune
    (hu.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  have hx₀P := hSpt x₀ (huS hx₀) hx₀cl
  set s₀ := GrpObj.sectionOfIsClosed H x₀ hx₀cl
  -- the union `U'` of the translates of `u` by `P`
  set u' := ⋃ s ∈ P, (GrpObj.mulLeft H s).left '' u with hu'
  have hu'open : IsOpen u' :=
    isOpen_biUnion fun s _ ↦ (GrpObj.mulLeft H s).left.isOpenEmbedding.isOpenMap _ hu
  have hu'S : u' ∩ Z ⊆ S := by
    rintro _ ⟨hy, hyZ⟩
    obtain ⟨s, hs, v, hv, rfl⟩ := Set.mem_iUnion₂.mp hy
    have hvZ : v ∈ Z := by
      rw [← hLinv s v]
      refine hLZ s⁻¹ ?_ ⟨_, hyZ, rfl⟩
      exact subset_closure ((hmemP _).mp (inv_mem hs))
    exact hLS hs ⟨v, huS ⟨hv, hvZ⟩, rfl⟩
  have hu'P (s) (hs : s ∈ P) : s.left pt ∈ u' := by
    refine Set.mem_iUnion₂.mpr ⟨s * s₀⁻¹, mul_mem hs (inv_mem hx₀P), x₀, hx₀.1, ?_⟩
    rw [← hsec x₀ hx₀cl, ← happ, GrpObj.comp_mulLeft_eq_mul, toUnit_unit, Category.id_comp,
      inv_mul_cancel_right]
  have hu'dense : Z ⊆ closure (u' ∩ Z) := by
    refine closure_minimal (hdense.trans (closure_mono ?_)) isClosed_closure
    rintro y ⟨hyS, hycl⟩
    refine ⟨?_, subset_closure hyS⟩
    rw [← hsec y hycl]
    exact hu'P _ (hSpt y hyS hycl)
  -- every closed point of `Z` lies in `U'`
  have hZu' : Z ⊆ u' := by
    by_contra h
    obtain ⟨y, ⟨hyZ, hyu'⟩, hycl⟩ := nonempty_inter_closedPoints (Set.sdiff_nonempty.mpr h)
      (isClosed_closure.isLocallyClosed.inter hu'open.isClosed_compl.isLocallyClosed)
    set t := GrpObj.sectionOfIsClosed H y hycl
    refine hyu' ?_
    rw [← hsec y hycl]
    refine hu'P _ ?_
    -- `t u'` and `u'` meet in a point of `Z`
    set O := (GrpObj.mulLeft H t).left '' u'
    have hOopen : IsOpen O := (GrpObj.mulLeft H t).left.isOpenEmbedding.isOpenMap _ hu'open
    have hO : (O ∩ (u' ∩ Z)).Nonempty := by
      have h1 : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ H).left pt ∈ u' := hu'P 1 (one_mem P)
      have hyO : y ∈ O ∩ closure (u' ∩ Z) := by
        refine ⟨⟨_, h1, ?_⟩, hu'dense hyZ⟩
        rw [← happ, GrpObj.comp_mulLeft_eq_mul, toUnit_unit, Category.id_comp, mul_one, hsec]
      obtain ⟨w, hw⟩ := closure_nonempty_iff.mp ⟨y, hOopen.inter_closure hyO⟩
      exact ⟨w, hw⟩
    rw [← Set.inter_assoc] at hO
    obtain ⟨w, ⟨⟨⟨x, hxu', rfl⟩, hwu'⟩, hwZ⟩, hwcl⟩ := nonempty_inter_closedPoints hO
      ((hOopen.inter hu'open).isLocallyClosed.inter isClosed_closure.isLocallyClosed)
    have hxZ : x ∈ Z := by
      rw [← hLinv t x]
      refine hLZ t⁻¹ ?_ ⟨_, hwZ, rfl⟩
      rw [Hom.inv_def, happ]
      exact hιZ ⟨_, hsec y hycl ▸ hyZ, rfl⟩
    have hxcl : IsClosed {x} := by
      have := (GrpObj.mulLeft H t⁻¹).left.isClosedEmbedding.isClosedMap _ hwcl
      rwa [Set.image_singleton, hLinv] at this
    have hxP := hSpt x (hu'S ⟨hxu', hxZ⟩) hxcl
    have hwP := hSpt _ (hu'S ⟨hwu', hwZ⟩) hwcl
    have htx : t * GrpObj.sectionOfIsClosed H x hxcl = GrpObj.sectionOfIsClosed H _ hwcl := by
      refine hext ?_
      rw [hsec, show t * GrpObj.sectionOfIsClosed H x hxcl =
          GrpObj.sectionOfIsClosed H x hxcl ≫ GrpObj.mulLeft H t by
        rw [GrpObj.comp_mulLeft_eq_mul, toUnit_unit, Category.id_comp], happ, hsec]
    change t ∈ P
    rw [← mul_inv_cancel_right t (GrpObj.sectionOfIsClosed H x hxcl), htx]
    exact mul_mem hwP (inv_mem hxP)
  exact closure_subset_iff_isClosed.mp fun y hy ↦ hu'S ⟨hZu' hy, hy⟩

/-- The image of a homomorphism from a group scheme of finite type to a group scheme locally of
finite type over a field is closed (SGA 3, VI_B, Proposition 1.2).

The source must be quasi-compact: the homomorphism `ℤ ⟶ 𝔾ₐ` from the constant group scheme,
`n ↦ n`, over `ℚ` has image the infinite non-closed set of closed points `n ∈ 𝔸¹_ℚ`.

After base change to an algebraic closure the image is closed by
`isClosed_range_of_isMonHom_of_isAlgClosed`, and closedness descends along the closed surjection
from the base change. The matrix-group case over an algebraically closed
field is `AlgebraicGeometry.GeneralLinearGroup.RationalHom.mem_range_points_iff` (blueprint
`lemma-connected-components-images-homomorphisms--2`). (blueprint:
`lemma-connected-components-images-homomorphisms`) -/
theorem isClosed_range_of_isMonHom {G K : Over (Spec (.of k))} [GrpObj G] [GrpObj K]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [LocallyOfFiniteType K.hom] (f : G ⟶ K)
    [IsMonHom f] :
    IsClosed (Set.range f.left.base) := by
  let g : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
  let : GrpObj ((Over.pullback g).obj K) := Functor.grpObjObj
  have : LocallyOfFiniteType ((Over.pullback g).obj G).hom :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd G.hom g))
  have : QuasiCompact ((Over.pullback g).obj G).hom :=
    inferInstanceAs (QuasiCompact (Limits.pullback.snd G.hom g))
  have : LocallyOfFiniteType ((Over.pullback g).obj K).hom :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd K.hom g))
  have h := isClosed_range_of_isMonHom_of_isAlgClosed ((Over.pullback g).map f)
  have : IsIntegralHom g := by
    rw [IsIntegralHom.SpecMap_iff]
    exact Algebra.IsIntegral.isIntegral
  have : Surjective g := ⟨fun x ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  let pG : ((Over.pullback g).obj G).left ⟶ G.left := Limits.pullback.fst G.hom g
  let pK : ((Over.pullback g).obj K).left ⟶ K.left := Limits.pullback.fst K.hom g
  have hsurj : Function.Surjective pG :=
    (MorphismProperty.pullback_fst (P := @Surjective) G.hom g this).surj
  have hw : ((Over.pullback g).map f).left ≫ pK = pG ≫ f.left := by
    simp [pG, pK]
  have hr {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
      Set.range (a ≫ b) = b '' Set.range a := by
    rw [← Set.range_comp]
    rfl
  have : Set.range f.left.base = pK '' Set.range ((Over.pullback g).map f).left := by
    calc Set.range f.left.base = f.left '' Set.range pG := by
          rw [hsurj.range_eq, Set.image_univ]
      _ = Set.range (pG ≫ f.left) := (hr _ _).symm
      _ = Set.range (((Over.pullback g).map f).left ≫ pK) := by rw [hw]
      _ = _ := hr _ _
  rw [this]
  exact pK.isClosedMap _ h

/-- A closed subgroup `J` of a connected reduced group scheme `G` locally of finite type over a
field, with `J` reduced of the same dimension as `G`, is all of `G`.
(blueprint: `lemma-connected-components-images-homomorphisms`) -/
theorem isIso_left_of_topologicalKrullDim_eq {J G : Over (Spec (.of k))} [GrpObj J] [GrpObj G]
    [LocallyOfFiniteType G.hom] [IsReduced J.left] [IsReduced G.left] [ConnectedSpace G.left]
    (f : J ⟶ G) [IsMonHom f] [IsClosedImmersion f.left]
    (h : topologicalKrullDim J.left = topologicalKrullDim G.left) : IsIso f.left := by
  have := irreducibleSpace_of_connectedSpace G
  have : IsIntegral G.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : Surjective f.left :=
    ⟨f.left.isClosedEmbedding.isInducing.surjective_of_topologicalKrullDim_eq
      f.left.isClosedEmbedding.isClosed_range (topologicalKrullDim_ne_top G.hom) h⟩
  exact isIso_of_isClosedImmersion_of_surjective f.left

/-! ### Subgroup schemes containing the commutators -/

section ContainsCommutators

variable {S : Scheme.{u}} {G H : Over S} [GrpObj G] [GrpObj H]

/-- A homomorphism of group schemes `f : H ⟶ G` over `S` *contains the commutators* of `G` when
every commutator `a b a⁻¹ b⁻¹` of two points `a b : X ⟶ G` of `G`, with values in an arbitrary
`S`-scheme `X`, factors through `f`. For a subgroup scheme `H ⊆ G` this is the scheme-theoretic
form of `⁅G, G⁆ ⊆ H`, that is, of the commutativity of the quotient `G ⧸ H`.
(blueprint: `lemma-restriction-normal-subgroup`) -/
class IsMonHom.ContainsCommutators (f : H ⟶ G) [IsMonHom f] : Prop where
  exists_comp_eq_commutator (f) : ∀ {X : Over S} (a b : X ⟶ G),
    ∃ c : X ⟶ H, c ≫ f = a * b * a⁻¹ * b⁻¹

instance : IsMonHom.ContainsCommutators (𝟙 G) where
  exists_comp_eq_commutator a b := ⟨a * b * a⁻¹ * b⁻¹, Category.comp_id _⟩

theorem IsMonHom.ContainsCommutators.of_eq {f g : H ⟶ G} [IsMonHom f] [IsMonHom g]
    [IsMonHom.ContainsCommutators f] (e : f = g) : IsMonHom.ContainsCommutators g := by
  subst e; assumption

/-- A subgroup scheme containing the commutators is normal: `g h g⁻¹ = (g h g⁻¹ h⁻¹) h`. -/
instance (priority := low) IsMonHom.Normal.of_containsCommutators (f : H ⟶ G) [IsMonHom f]
    [Mono f] [IsMonHom.ContainsCommutators f] : IsMonHom.Normal f where
  exists_comp_eq_conj := by
    obtain ⟨c, hc⟩ :=
      IsMonHom.ContainsCommutators.exists_comp_eq_commutator f (fst G H) (snd G H ≫ f)
    refine ⟨c * snd G H, ?_⟩
    have h := (IsMonHom.monoidHom f (G ⊗ H)).map_mul c (snd G H)
    simp only [IsMonHom.monoidHom_apply] at h
    rw [h, hc, GrpObj.conj, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, whiskerLeft_fst,
      whiskerLeft_snd, inv_mul_cancel_right]

end ContainsCommutators

/-- A fibre product over `Spec k` of two schemes locally of finite type over `k` is locally of
finite type over `k`. -/
instance {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

end AlgebraicGeometry
