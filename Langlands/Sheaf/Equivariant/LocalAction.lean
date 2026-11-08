import Langlands.Representation.Smooth.Definitions
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Discrete sections for specified local actions on a site

A local action system on a category specifies, for objects `U` and open
subgroups `H` of a topological group, which actions of `H` on `U` by
endomorphisms are the admissible ones. A presheaf with values in a concrete
category is discrete when every admissible local action acts on its sections
with open stabilizers. It is locally discrete for a Grothendieck topology when
every section is, on a covering sieve, the restriction of discrete sections over
objects carrying admissible local actions.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory Opposite

universe v u uG uA vA wA uR wR

variable (T : Type u) [Category.{v} T] (G : Type uG) [Group G] [TopologicalSpace G]

/-- For each object `U` and open subgroup `H`, the actions of `H` on `U` by
endomorphisms that are declared admissible. -/
structure LocalActionSystem where
  /-- The predicate selecting the admissible local actions. -/
  IsAdmissible : ∀ (U : T) (H : OpenSubgroup G), ((H : Subgroup G) →* (End U)ᵐᵒᵖ) → Prop

variable {T G}
variable {A : Type uA} [Category.{vA} A] {FA : A → A → Type*} {CA : A → Type wA}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{wA} A FA]

/-- A section is discrete for a local action when an open subgroup contained in
the acting subgroup fixes it. -/
def IsDiscreteSection (F : Tᵒᵖ ⥤ A) {U : T} {H : OpenSubgroup G}
    (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ) (s : ToType (F.obj (op U))) : Prop :=
  ∃ K : OpenSubgroup G, K ≤ H ∧
    ∀ h : (H : Subgroup G), (h : G) ∈ K → F.map (a h).unop.op s = s

theorem IsDiscreteSection.map {F F' : Tᵒᵖ ⥤ A} (φ : F ⟶ F') {U : T} {H : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} {s : ToType (F.obj (op U))}
    (hs : IsDiscreteSection F a s) : IsDiscreteSection F' a (φ.app (op U) s) := by
  obtain ⟨K, hKH, hK⟩ := hs
  refine ⟨K, hKH, fun h hh => ?_⟩
  rw [← NatTrans.naturality_apply, hK h hh]

theorem IsDiscreteSection.of_injective {F F' : Tᵒᵖ ⥤ A} (φ : F ⟶ F') {U : T}
    {H : OpenSubgroup G} {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} {s : ToType (F.obj (op U))}
    (hφ : Function.Injective (φ.app (op U)))
    (hs : IsDiscreteSection F' a (φ.app (op U) s)) : IsDiscreteSection F a s := by
  obtain ⟨K, hKH, hK⟩ := hs
  refine ⟨K, hKH, fun h hh => hφ ?_⟩
  rw [NatTrans.naturality_apply, hK h hh]

/-- Discreteness only depends on the action of a smaller open subgroup: two
local actions agreeing on an open subgroup have the same discrete sections. -/
theorem IsDiscreteSection.of_agree {F : Tᵒᵖ ⥤ A} {U : T} {H H' N : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} {a' : (H' : Subgroup G) →* (End U)ᵐᵒᵖ}
    (hNH : N ≤ H) (hNH' : N ≤ H')
    (haa' : ∀ (g : G) (hg : g ∈ N), a ⟨g, hNH hg⟩ = a' ⟨g, hNH' hg⟩)
    {s : ToType (F.obj (op U))} (hs : IsDiscreteSection F a s) :
    IsDiscreteSection F a' s := by
  obtain ⟨K, -, hK⟩ := hs
  refine ⟨K ⊓ N, inf_le_right.trans hNH', fun h hh => ?_⟩
  obtain ⟨hhK, hhN⟩ := OpenSubgroup.mem_inf.1 hh
  have hfix := hK ⟨h, hNH hhN⟩ hhK
  rw [haa' h hhN] at hfix
  exact hfix

theorem isDiscreteSection_of_discreteTopology [DiscreteTopology G] (F : Tᵒᵖ ⥤ A) {U : T}
    {H : OpenSubgroup G} (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ) (s : ToType (F.obj (op U))) :
    IsDiscreteSection F a s := by
  refine ⟨⟨⊥, isOpen_discrete _⟩, fun g hg => ?_, fun h hh => ?_⟩
  · have hg' : g = 1 := Subgroup.mem_bot.1 hg
    rw [hg']
    exact one_mem H
  · have hh' : (h : G) = 1 := Subgroup.mem_bot.1 hh
    have h1 : h = 1 := Subtype.ext hh'
    rw [h1, map_one]
    change F.map (𝟙 (op U)) s = s
    rw [F.map_id, CategoryTheory.id_apply]

namespace LocalActionSystem

variable (L : LocalActionSystem T G)

/-- Berkovich's Definition 1.4.1 shape: every admissible local action acts on
sections with open stabilizers. -/
def IsDiscrete (F : Tᵒᵖ ⥤ A) : Prop :=
  ∀ (U : T) (H : OpenSubgroup G) (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ),
    L.IsAdmissible U H a → ∀ s : ToType (F.obj (op U)), IsDiscreteSection F a s

/-- The sieve of arrows factoring through an object that carries an admissible
local action. -/
def admissibleSieve (U : T) : Sieve U where
  arrows W g := ∃ (V : T) (k : W ⟶ V) (f : V ⟶ U) (H : OpenSubgroup G)
    (a : (H : Subgroup G) →* (End V)ᵐᵒᵖ), L.IsAdmissible V H a ∧ k ≫ f = g
  downward_closed := by
    rintro W W' g ⟨V, k, f, H, a, ha, rfl⟩ k'
    exact ⟨V, k' ≫ k, f, H, a, ha, Category.assoc _ _ _⟩

/-- Every object is covered by objects carrying admissible local actions. -/
def Covers (J : GrothendieckTopology T) : Prop :=
  ∀ U : T, L.admissibleSieve U ∈ J U

/-- The sieve of arrows factoring through an object with an admissible local
action for which the restricted section is discrete. -/
def discreteSieve (F : Tᵒᵖ ⥤ A) {U : T} (s : ToType (F.obj (op U))) : Sieve U where
  arrows W g := ∃ (V : T) (k : W ⟶ V) (f : V ⟶ U) (H : OpenSubgroup G)
    (a : (H : Subgroup G) →* (End V)ᵐᵒᵖ),
      L.IsAdmissible V H a ∧ IsDiscreteSection F a (F.map f.op s) ∧ k ≫ f = g
  downward_closed := by
    rintro W W' g ⟨V, k, f, H, a, ha, hs, rfl⟩ k'
    exact ⟨V, k' ≫ k, f, H, a, ha, hs, Category.assoc _ _ _⟩

/-- The remark after Berkovich's Definition 1.4.1: every section is locally the
restriction of discrete sections over objects with admissible local actions. -/
def IsLocallyDiscrete (J : GrothendieckTopology T) (F : Tᵒᵖ ⥤ A) : Prop :=
  ∀ (U : T) (s : ToType (F.obj (op U))), L.discreteSieve F s ∈ J U

theorem discreteSieve_le_admissibleSieve (F : Tᵒᵖ ⥤ A) {U : T}
    (s : ToType (F.obj (op U))) : L.discreteSieve F s ≤ L.admissibleSieve U := by
  rintro W g ⟨V, k, f, H, a, ha, -, rfl⟩
  exact ⟨V, k, f, H, a, ha, rfl⟩

theorem IsDiscrete.discreteSieve_eq {F : Tᵒᵖ ⥤ A} (hF : L.IsDiscrete F) {U : T}
    (s : ToType (F.obj (op U))) : L.discreteSieve F s = L.admissibleSieve U := by
  apply le_antisymm (L.discreteSieve_le_admissibleSieve F s)
  rintro W g ⟨V, k, f, H, a, ha, rfl⟩
  exact ⟨V, k, f, H, a, ha, hF V H a ha _, rfl⟩

/-- Discreteness implies local discreteness when admissible objects cover. -/
theorem IsDiscrete.isLocallyDiscrete {J : GrothendieckTopology T} (hL : L.Covers J)
    {F : Tᵒᵖ ⥤ A} (hF : L.IsDiscrete F) : L.IsLocallyDiscrete J F := by
  intro U s
  rw [hF.discreteSieve_eq L s]
  exact hL U

/-- Restricting a section along an arrow keeps the arrows of its discrete sieve
after composition. -/
theorem discreteSieve_le_pullback (F : Tᵒᵖ ⥤ A) {U V : T} (g : V ⟶ U)
    (s : ToType (F.obj (op U))) :
    L.discreteSieve F (F.map g.op s) ≤ (L.discreteSieve F s).pullback g := by
  rintro W h ⟨V', k, f, H, a, ha, hs, rfl⟩
  refine ⟨V', k, f ≫ g, H, a, ha, ?_, (Category.assoc _ _ _).symm⟩
  rw [op_comp, F.map_comp, CategoryTheory.comp_apply]
  exact hs

/-- Local discreteness of a section descends along a covering sieve. -/
theorem discreteSieve_mem_of_covering {J : GrothendieckTopology T} (F : Tᵒᵖ ⥤ A) {U : T}
    (s : ToType (F.obj (op U))) {S : Sieve U} (hS : S ∈ J U)
    (h : ∀ ⦃V : T⦄ ⦃g : V ⟶ U⦄, S g → L.discreteSieve F (F.map g.op s) ∈ J V) :
    L.discreteSieve F s ∈ J U :=
  J.transitive hS _ fun _ g hg =>
    J.superset_covering (L.discreteSieve_le_pullback F g s) (h hg)

theorem discreteSieve_le_map {F F' : Tᵒᵖ ⥤ A} (φ : F ⟶ F') {U : T}
    (s : ToType (F.obj (op U))) : L.discreteSieve F s ≤ L.discreteSieve F' (φ.app (op U) s) := by
  rintro W g ⟨V, k, f, H, a, ha, hs, rfl⟩
  refine ⟨V, k, f, H, a, ha, ?_, rfl⟩
  rw [← NatTrans.naturality_apply]
  exact hs.map φ

theorem discreteSieve_map_of_injective {F F' : Tᵒᵖ ⥤ A} (φ : F ⟶ F')
    (hφ : ∀ U : Tᵒᵖ, Function.Injective (φ.app U)) {U : T} (s : ToType (F.obj (op U))) :
    L.discreteSieve F' (φ.app (op U) s) = L.discreteSieve F s := by
  apply le_antisymm _ (L.discreteSieve_le_map φ s)
  rintro W g ⟨V, k, f, H, a, ha, hs, rfl⟩
  refine ⟨V, k, f, H, a, ha, ?_, rfl⟩
  rw [← NatTrans.naturality_apply] at hs
  exact hs.of_injective φ (hφ _)

/-- The source of a morphism with injective components into a discrete
presheaf is discrete. -/
theorem IsDiscrete.of_injective {F F' : Tᵒᵖ ⥤ A} (φ : F ⟶ F')
    (hφ : ∀ U : Tᵒᵖ, Function.Injective (φ.app U)) (hF' : L.IsDiscrete F') :
    L.IsDiscrete F := fun U H a ha s =>
  (hF' U H a ha (φ.app (op U) s)).of_injective φ (hφ _)

/-- The source of a morphism with injective components into a locally discrete
presheaf is locally discrete. -/
theorem IsLocallyDiscrete.of_injective {J : GrothendieckTopology T} {F F' : Tᵒᵖ ⥤ A}
    (φ : F ⟶ F') (hφ : ∀ U : Tᵒᵖ, Function.Injective (φ.app U))
    (hF' : L.IsLocallyDiscrete J F') : L.IsLocallyDiscrete J F := fun U s => by
  rw [← L.discreteSieve_map_of_injective φ hφ s]
  exact hF' U _

theorem isDiscrete_of_discreteTopology [DiscreteTopology G] (F : Tᵒᵖ ⥤ A) :
    L.IsDiscrete F := fun _ _ a _ s => isDiscreteSection_of_discreteTopology F a s

theorem isLocallyDiscrete_of_discreteTopology [DiscreteTopology G]
    {J : GrothendieckTopology T} (hL : L.Covers J) (F : Tᵒᵖ ⥤ A) :
    L.IsLocallyDiscrete J F :=
  (L.isDiscrete_of_discreteTopology F).isLocallyDiscrete L hL

variable (A) (J : GrothendieckTopology T)

/-- Sheaves whose admissible local actions are discrete on sections. -/
def discreteSheafProperty : ObjectProperty (Sheaf J A) :=
  fun F => L.IsDiscrete F.obj

/-- Sheaves whose sections are locally discrete. -/
def smoothSheafProperty : ObjectProperty (Sheaf J A) :=
  fun F => L.IsLocallyDiscrete J F.obj

/-- The full subcategory of locally discrete sheaves. -/
abbrev SmoothSheaf := (L.smoothSheafProperty A J).FullSubcategory

/-- The inclusion of locally discrete sheaves into all sheaves. -/
def smoothSheafInclusion : L.SmoothSheaf A J ⥤ Sheaf J A :=
  (L.smoothSheafProperty A J).ι

variable {A J}

theorem discreteSheafProperty_le_smoothSheafProperty (hL : L.Covers J) :
    L.discreteSheafProperty A J ≤ L.smoothSheafProperty A J :=
  fun _ hF => IsDiscrete.isLocallyDiscrete L hL hF

end LocalActionSystem

section Representation

variable {R : Type uR} [CommRing R]

/-- The representation of the acting open subgroup on the sections over an
object with a local action. -/
def localRepresentation (F : Tᵒᵖ ⥤ ModuleCat.{wR} R) {U : T} {H : OpenSubgroup G}
    (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ) :
    Representation R (H : Subgroup G) (F.obj (op U)) where
  toFun h := (F.map (a h).unop.op).hom
  map_one' := by
    rw [map_one]
    change (F.map (𝟙 (op U))).hom = 1
    rw [F.map_id]
    rfl
  map_mul' g h := by
    rw [map_mul, MulOpposite.unop_mul, End.mul_def, op_comp, F.map_comp]
    rfl

theorem localRepresentation_apply (F : Tᵒᵖ ⥤ ModuleCat.{wR} R) {U : T} {H : OpenSubgroup G}
    (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ) (h : (H : Subgroup G)) (s : F.obj (op U)) :
    localRepresentation F a h s = (F.map (a h).unop.op).hom s := rfl

/-- A section is discrete exactly when it is a smooth vector of the local
representation, for the subspace topology on the acting open subgroup. -/
theorem isDiscreteSection_iff_isSmoothVector (F : Tᵒᵖ ⥤ ModuleCat.{wR} R) {U : T}
    {H : OpenSubgroup G} (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ) (s : F.obj (op U)) :
    IsDiscreteSection F a s ↔ IsSmoothVector (localRepresentation F a) s := by
  constructor
  · rintro ⟨K, -, hK⟩
    refine ⟨K.comap (H : Subgroup G).subtype continuous_subtype_val, ?_⟩
    rintro ⟨h, hh⟩
    exact hK h hh
  · rintro ⟨K, hK⟩
    let K' : OpenSubgroup G :=
      ⟨(K : Subgroup (H : Subgroup G)).map (H : Subgroup G).subtype,
        H.isOpen.isOpenMap_subtype_val _ K.isOpen⟩
    refine ⟨K', ?_, ?_⟩
    · rintro g ⟨h, -, rfl⟩
      exact h.2
    · rintro h ⟨k, hk, hkh⟩
      have hkh' : k = h := Subtype.ext hkh
      subst hkh'
      exact hK ⟨k, hk⟩

/-- For module-valued presheaves, discreteness means that every admissible
local representation is smooth. -/
theorem LocalActionSystem.isDiscrete_iff_isSmooth (L : LocalActionSystem T G)
    (F : Tᵒᵖ ⥤ ModuleCat.{wR} R) :
    L.IsDiscrete F ↔ ∀ (U : T) (H : OpenSubgroup G) (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ),
      L.IsAdmissible U H a → IsSmooth (localRepresentation F a) := by
  refine forall_congr' fun U => forall_congr' fun H => forall_congr' fun a =>
    forall_congr' fun _ => forall_congr' fun s => ?_
  exact isDiscreteSection_iff_isSmoothVector F a s

end Representation

end Langlands.Sheaf.Equivariant
