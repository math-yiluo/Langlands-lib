import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Compact.CharZeroAverage
import Langlands.Representation.Jacquet.CoefficientScalarRestriction
import Mathlib.CategoryTheory.Center.Basic

/-! # Reducing `B ⊗_ℂ ℨ(G)`-admissibility to a complex subrepresentation

Helpers for Renard VI.10.7, Variant: a `(G, B)`-module of finite type over `B[G]` contains a
complex subrepresentation of finite type over `ℂ[G]` whose carrier spans it over `B`, and
`ℨ(G)`-generators of the `K`-fixed vectors of such a subrepresentation give
`B ⊗_ℂ ℨ(G)`-generators of the `K`-fixed vectors of the whole module. No reductive structure
on the group is used.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped MonoidAlgebra

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Jacquet.CoefficientRestriction

universe uG uV uB

variable {G : Type uG} [Group G]
variable {B : Type uB} [CommRing B] [Algebra ℂ B]
variable {V : Type uV} [AddCommGroup V] [Module B V] [Module ℂ V] [IsScalarTower ℂ B V]

/-- Multiplication by a coefficient `b : B` is a complex intertwiner of the underlying complex
representation `complexRepresentation ρ`: it is complex-linear because the complex structure
is the restriction of the `B`-structure, and it commutes with every `ρ g` because `ρ g` is
`B`-linear. -/
def coefficientSMulIntertwiningMap (ρ : Representation B G V) (b : B) :
    (complexRepresentation ρ).IntertwiningMap (complexRepresentation ρ) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    { toFun := fun v => b • v
      map_add' := smul_add b
      map_smul' := fun c v => smul_comm b c v }
    (fun g v => ((ρ g).map_smul b v).symm)

@[simp]
theorem coefficientSMulIntertwiningMap_apply (ρ : Representation B G V) (b : B) (v : V) :
    coefficientSMulIntertwiningMap ρ b v = b • v := rfl

omit [Algebra ℂ B] [Module ℂ V] [IsScalarTower ℂ B V] in
/-- The `B`-span of a `ρ`-stable set of vectors is `ρ`-stable. -/
theorem span_mem_of_stable (ρ : Representation B G V) (S : Set V)
    (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : G) {v : V} (hv : v ∈ Submodule.span B S) :
    ρ g v ∈ Submodule.span B S := by
  have hle : (Submodule.span B S).map (ρ g) ≤ Submodule.span B S := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨w, hw, rfl⟩
    exact hS g w hw
  exact hle ⟨v, hv, rfl⟩

section Topological

variable [TopologicalSpace G]

/-- Intertwiners of smooth representations commute with the action of the group algebra. -/
theorem hom_asAlgebraHom {A A' : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ A') (r : ℂ[G]) (x : A) :
    SmoothRep.hom f (A.representation.asAlgebraHom r x) =
      A'.representation.asAlgebraHom r (SmoothRep.hom f x) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r₁ r₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | single g a =>
    simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
    rw [(SmoothRep.hom f).isIntertwining]

/-- The inclusion of a smooth subrepresentation, as a linear map of group-algebra modules. -/
def subrepresentationAsModuleSubtype (A : SmoothRep.{0, uG, uV} ℂ G)
    (S : Subrepresentation A.representation) :
    (SmoothRep.subrepresentation A S).representation.asModule →ₗ[ℂ[G]]
      A.representation.asModule where
  toFun w := A.representation.asModuleEquiv.symm
    (SmoothRep.hom (SmoothRep.subtype A S)
      ((SmoothRep.subrepresentation A S).representation.asModuleEquiv w))
  map_add' _ _ := rfl
  map_smul' r w := by
    rw [RingHom.id_apply]
    apply A.representation.asModuleEquiv.injective
    rw [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply,
      Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply]
    exact hom_asAlgebraHom _ r _

theorem subrepresentationAsModuleSubtype_injective (A : SmoothRep.{0, uG, uV} ℂ G)
    (S : Subrepresentation A.representation) :
    Function.Injective (subrepresentationAsModuleSubtype A S) :=
  fun _ _ h => SmoothRep.subtype_injective A S h

/-- If a smooth subrepresentation is carried by a finitely generated group-algebra submodule,
it is of finite type. -/
theorem finite_subrepresentation_ofSubmodule (A : SmoothRep.{0, uG, uV} ℂ G)
    (N : Submodule ℂ[G] A.representation.asModule) (hN : N.FG) :
    Module.Finite ℂ[G]
      (SmoothRep.subrepresentation A
        (Subrepresentation.ofSubmodule' N)).representation.asModule := by
  let f := subrepresentationAsModuleSubtype A (Subrepresentation.ofSubmodule' N)
  have hf := subrepresentationAsModuleSubtype_injective A (Subrepresentation.ofSubmodule' N)
  have hrange : LinearMap.range f = N := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact w.2
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩
  have : Module.Finite ℂ[G] (LinearMap.range f) := by
    rw [hrange]
    exact Module.Finite.iff_fg.mpr hN
  exact Module.Finite.equiv (LinearEquiv.ofInjective f hf).symm

/-- Step 1 of the reduction. If a `(G, B)`-module is finitely generated over `B[G]`, there is
a complex subrepresentation of `complexRepresentation ρ`, of finite type over `ℂ[G]`, whose
carrier spans `V` over `B`: the complex subrepresentation generated by finitely many
`B[G]`-generators. -/
theorem exists_finite_complexSubrepresentation (ρ : Representation B G V)
    (hτ : IsSmooth (complexRepresentation ρ))
    (hfin : Module.Finite (MonoidAlgebra B G) ρ.asModule) :
    ∃ S : Subrepresentation (complexRepresentation ρ),
      Submodule.span B (S : Set V) = ⊤ ∧
        Module.Finite ℂ[G]
          (SmoothRep.subrepresentation (SmoothRep.of (complexRepresentation ρ) hτ)
            S).representation.asModule := by
  obtain ⟨T, hT⟩ := hfin.fg_top
  let τ : SmoothRep.{0, uG, uV} ℂ G := SmoothRep.of (complexRepresentation ρ) hτ
  let T₀ : Set V := (T : Set ρ.asModule)
  let N : Submodule ℂ[G] τ.representation.asModule :=
    Submodule.span ℂ[G] (T₀ : Set τ.representation.asModule)
  let S : Subrepresentation (complexRepresentation ρ) := Subrepresentation.ofSubmodule' N
  refine ⟨S, ?_, finite_subrepresentation_ofSubmodule τ N (Submodule.fg_span T.finite_toSet)⟩
  -- The `B`-span of the carrier of `S` is a `B[G]`-submodule containing the generators.
  let P : Subrepresentation ρ :=
    { toSubmodule := Submodule.span B (S : Set V)
      apply_mem_toSubmodule := fun g _ hv =>
        span_mem_of_stable ρ (S : Set V)
          (fun g w hw => S.apply_mem_toSubmodule g hw) g hv }
  have hTP : (T : Set ρ.asModule) ⊆ Subrepresentation.asSubmodule P := by
    intro t ht
    have htN : t ∈ N := Submodule.subset_span ht
    change (t : V) ∈ Submodule.span B (S : Set V)
    exact Submodule.subset_span htN
  have htop : (⊤ : Submodule (MonoidAlgebra B G) ρ.asModule) ≤
      Subrepresentation.asSubmodule P := by
    rw [← hT]
    exact Submodule.span_le.mpr hTP
  rw [eq_top_iff]
  intro v _
  have hv : (show ρ.asModule from v) ∈ Subrepresentation.asSubmodule P :=
    htop Submodule.mem_top
  exact hv

variable [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- The generating vectors coming from a subrepresentation are `K`-fixed for `ρ`. -/
theorem mem_fixedVectors_of_subrepresentation (ρ : Representation B G V)
    (hτ : IsSmooth (complexRepresentation ρ))
    (S : Subrepresentation (complexRepresentation ρ)) (K : Subgroup G)
    (w : SmoothRep.subrepresentation (SmoothRep.of (complexRepresentation ρ) hτ) S)
    (hw : ∀ g ∈ K,
      (SmoothRep.subrepresentation (SmoothRep.of (complexRepresentation ρ) hτ) S).representation
        g w = w) :
    SmoothRep.hom (SmoothRep.subtype (SmoothRep.of (complexRepresentation ρ) hτ) S) w ∈
      fixedVectors ρ K := by
  rw [fixedVectors, Representation.mem_invariants]
  intro g
  exact congrArg Subtype.val (hw g.1 g.2)

/-- Steps 3 and 4 of the reduction. Let `S` be a complex subrepresentation of the underlying
complex representation of a `(G, B)`-module whose carrier spans `V` over `B`, let `K` be a
compact open subgroup, and let `s₁, …, s_n` be vectors of `W = S` such that every `K`-fixed
vector of `W` is `∑ zᵢ · sᵢ` with `zᵢ ∈ ℨ(G)`. Then every `K`-fixed vector of `V` lies in the
`B`-span of the vectors `z · sⱼ`, where `z ∈ ℨ(G)` acts on `V` through its component at
`τ = complexRepresentation ρ`. -/
theorem fixedVectors_le_span_center_of_subrepresentation (ρ : Representation B G V)
    (hτ : IsSmooth (complexRepresentation ρ))
    (S : Subrepresentation (complexRepresentation ρ))
    (hspan : Submodule.span B (S : Set V) = ⊤)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {n : ℕ}
    (s : Fin n → SmoothRep.subrepresentation (SmoothRep.of (complexRepresentation ρ) hτ) S)
    (hgen : ∀ x : SmoothRep.subrepresentation (SmoothRep.of (complexRepresentation ρ) hτ) S,
      (∀ g ∈ K, (SmoothRep.subrepresentation (SmoothRep.of (complexRepresentation ρ) hτ)
        S).representation g x = x) →
      ∃ z : Fin n → CatCenter (SmoothRep.{0, uG, uV} ℂ G),
        x = ∑ i, SmoothRep.hom ((z i).app _) (s i)) :
    fixedVectors ρ K.toSubgroup ≤
      Submodule.span B {y : V | ∃ (j : Fin n) (z : CatCenter (SmoothRep.{0, uG, uV} ℂ G)),
        y = SmoothRep.hom (z.app (SmoothRep.of (complexRepresentation ρ) hτ))
          (SmoothRep.hom (SmoothRep.subtype (SmoothRep.of (complexRepresentation ρ) hτ) S)
            (s j))} := by
  intro x hx
  let τ : SmoothRep.{0, uG, uV} ℂ G := SmoothRep.of (complexRepresentation ρ) hτ
  let W : SmoothRep.{0, uG, uV} ℂ G := SmoothRep.subrepresentation τ S
  let ι : W ⟶ τ := SmoothRep.subtype τ S
  let e : V →ₗ[ℂ] V := Langlands.Compact.CharZero.averageMap (complexRepresentation ρ) hτ K hK
  let eW : W →ₗ[ℂ] W := Langlands.Compact.CharZero.averageMap W.representation W.isSmooth K hK
  -- Averaging is the identity on `K`-fixed vectors.
  have hex : e x = x := by
    apply Langlands.Compact.CharZero.averageMap_id
    rw [fixedVectors, Representation.mem_invariants] at hx ⊢
    exact hx
  -- Averaging commutes with the inclusion of `W`.
  have hι : ∀ w : W, e (SmoothRep.hom ι w) = SmoothRep.hom ι (eW w) := fun w =>
    (LinearMap.congr_fun (Langlands.Compact.CharZero.averageMap_commute W.representation
      τ.representation W.isSmooth hτ K hK (SmoothRep.hom ι)) w).symm
  -- Averaging commutes with the coefficient action.
  have hb : ∀ (b : B) (v : V), e (b • v) = b • e v := fun b v =>
    (LinearMap.congr_fun (Langlands.Compact.CharZero.averageMap_commute
      (complexRepresentation ρ) (complexRepresentation ρ) hτ hτ K hK
      (coefficientSMulIntertwiningMap ρ b)) v).symm
  have key : ∀ v ∈ Submodule.span B (S : Set V),
      e v ∈ Submodule.span B {y : V | ∃ (j : Fin n)
        (z : CatCenter (SmoothRep.{0, uG, uV} ℂ G)),
          y = SmoothRep.hom (z.app τ) (SmoothRep.hom ι (s j))} := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      let w : W := ⟨v, hv⟩
      have hwfix : ∀ g ∈ K, W.representation g (eW w) = eW w := by
        intro g hg
        have h := Langlands.Compact.CharZero.averageMap_mem_fixedVectors W.representation
          W.isSmooth K hK w
        rw [fixedVectors, Representation.mem_invariants] at h
        exact h ⟨g, hg⟩
      obtain ⟨z, hz⟩ := hgen (eW w) hwfix
      have hv' : e v = SmoothRep.hom ι (eW w) := hι w
      rw [hv', hz, map_sum]
      refine Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨i, z i, ?_⟩)
      have hnat := congrArg (fun f : W ⟶ τ => SmoothRep.hom f (s i)) ((z i).naturality ι)
      exact hnat.symm
    | zero => simp
    | add a c _ _ ha hc =>
      rw [map_add]
      exact add_mem ha hc
    | smul b v _ hv =>
      rw [hb]
      exact Submodule.smul_mem _ b hv
  rw [← hex]
  exact key x (hspan ▸ Submodule.mem_top)

/-- The reduction of Renard VI.10.7, Variant, to the complex Theorem, in an arbitrary
topological group. Assume the conclusion of the complex Theorem (`ℨ(G)`-admissibility of
every smooth complex representation of finite type over `ℂ[G]`). Then every `(G, B)`-module
whose underlying complex representation is smooth and which is finitely generated over `B[G]`
is `B ⊗_ℂ ℨ(G)`-admissible: for every compact open subgroup `K` there are finitely many
`K`-fixed vectors `s₁, …, s_n` such that every `K`-fixed vector lies in the `B`-span of the
vectors `z · sⱼ` with `z ∈ ℨ(G)`. -/
theorem centerAdmissible_of_complexCenterAdmissible
    (hC : ∀ τ : SmoothRep.{0, uG, uV} ℂ G,
      Module.Finite (MonoidAlgebra ℂ G) τ.representation.asModule →
      ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
        ∃ (n : ℕ) (s : Fin n → τ),
          (∀ i, ∀ g ∈ K, τ.representation g (s i) = s i) ∧
          ∀ x : τ, (∀ g ∈ K, τ.representation g x = x) →
            ∃ z : Fin n → CatCenter (SmoothRep.{0, uG, uV} ℂ G),
              x = ∑ i, SmoothRep.hom ((z i).app τ) (s i))
    (ρ : Representation B G V) (hτ : IsSmooth (complexRepresentation ρ))
    (hfin : Module.Finite (MonoidAlgebra B G) ρ.asModule)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    ∃ (n : ℕ) (s : Fin n → V),
      (∀ j, s j ∈ fixedVectors ρ K.toSubgroup) ∧
      fixedVectors ρ K.toSubgroup ≤
        Submodule.span B {y : V | ∃ (j : Fin n) (z : CatCenter (SmoothRep.{0, uG, uV} ℂ G)),
          y = SmoothRep.hom (z.app (SmoothRep.of (complexRepresentation ρ) hτ)) (s j)} := by
  obtain ⟨S, hspan, hWfin⟩ := exists_finite_complexSubrepresentation ρ hτ hfin
  obtain ⟨n, s, hsK, hgen⟩ :=
    hC (SmoothRep.subrepresentation (SmoothRep.of (complexRepresentation ρ) hτ) S) hWfin K hK
  exact ⟨n, fun j =>
      SmoothRep.hom (SmoothRep.subtype (SmoothRep.of (complexRepresentation ρ) hτ) S) (s j),
    fun j => mem_fixedVectors_of_subrepresentation ρ hτ S K.toSubgroup (s j) (hsK j),
    fixedVectors_le_span_center_of_subrepresentation ρ hτ S hspan K hK s hgen⟩

end Topological

end Langlands.Renard.AlgebraicFamily
