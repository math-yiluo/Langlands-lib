/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.AlgebraicGeometry.ProEtale.SequentialLimit
public import WeilConjectures.AlgebraicGeometry.ProEtale.SigmaCover
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Repleteness of the pro-étale topos

The pro-étale topos of a scheme `S` is replete (Bhatt–Scholze, Proposition 4.2.8): for a tower
of epimorphisms of sheaves `⋯ ⟶ F₁ ⟶ F₀`, the projection `lim Fₙ ⟶ F₀` is an epimorphism.
Consequently countable products of sheaves of modules are exact.

The proof follows Mathlib's argument for light condensed sets
(`Mathlib/CategoryTheory/Sites/Coherent/SequentialLimit.lean`). We work on the affine pro-étale
site `S.AffineProEt`, where a morphism of sheaves is locally surjective if and only if sections
lift after pullback along a single surjection (finite covers can be replaced by their disjoint
union, see `AlgebraicGeometry.Scheme.AffineProEt.sigmaCover`). Lifting step by step along a
tower produces a sequence of surjections, whose limit is again a surjection
(`AlgebraicGeometry.Scheme.AffineProEt.exists_compatible_surjective`). The result is transported
to the pro-étale site along the equivalence of sheaf categories
`AlgebraicGeometry.Scheme.AffineProEt.isEquivalence_sheafPushforwardContinuous_toProEt`.

## Main statements

* `AlgebraicGeometry.Scheme.AffineProEt.isLocallySurjective_iff`: local surjectivity on the
  affine pro-étale site in terms of single surjections.
* `AffineProEt.isLocallySurjective_π_app_zero_of_isLocallySurjective_map`:
  sequential limits of locally surjective morphisms are locally surjective.
* `AlgebraicGeometry.Scheme.ProEt.epi_π_app_zero_of_epi`: the projection `lim Fₙ ⟶ F₀` of a
  tower of epimorphisms of sheaves of modules on the pro-étale site is an epimorphism.
* `AlgebraicGeometry.Scheme.ProEt.epi_pi_map`: countable products of epimorphisms of sheaves of
  modules on the pro-étale site are epimorphisms.
* `AlgebraicGeometry.Scheme.ProEt.countableAB4Star`: sheaves of modules on the pro-étale site
  satisfy countable AB4\*.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite TypeCat

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {S : Scheme.{u}}

/-- A single surjection in the affine pro-étale site generates a covering sieve. -/
lemma generate_singleton_mem_topology {W X : S.AffineProEt} (q : W ⟶ X)
    (hq : Surjective q.left) : Sieve.generate (Presieve.singleton q) ∈ topology S X :=
  (generates_minimalPrecoverage S).generate_mem
    (.inr ⟨⟨W, q, rfl⟩, MorphismProperty.singleton_mem_precoverage_iff.mpr hq⟩)

/-- A morphism of sheaves of types on the affine pro-étale site is locally surjective if and only
if every section of the target lifts after pullback along a single surjection. -/
lemma isLocallySurjective_iff_of_isSheaf {F G : S.AffineProEtᵒᵖ ⥤ Type w} (φ : F ⟶ G)
    (hF : Presheaf.IsSheaf (topology S) F) (hG : Presheaf.IsSheaf (topology S) G) :
    Presheaf.IsLocallySurjective (topology S) φ ↔
      ∀ (X : S.AffineProEt) (y : G.obj (op X)), ∃ (W : S.AffineProEt) (q : W ⟶ X)
        (_ : Surjective q.left) (x : F.obj (op W)), φ.app (op W) x = G.map q.op y := by
  refine ⟨fun h X y ↦ ?_, fun h ↦ ⟨fun {X} y ↦ ?_⟩⟩
  · obtain ⟨ι, _, V, f, hf, hsurj⟩ :=
      exists_finite_jointly_surjective_of_mem_topology
        (Presheaf.imageSieve_mem (topology S) φ (U := op X) y)
    choose x hx using hf
    obtain ⟨z, hz⟩ := exists_sigmaCover_glue V f hF x
    refine ⟨sigmaCover V f, sigmaCoverπ V f, surjective_sigmaCoverπ V f hsurj, z,
      sigmaCover_ext V f hG fun i ↦ ?_⟩
    rw [← NatTrans.naturality_apply, hz, hx, ← Functor.map_comp_apply, ← op_comp,
      sigmaCoverι_π]
  · obtain ⟨W, q, hq, x, hx⟩ := h X y
    refine (topology S).superset_covering ?_ (generate_singleton_mem_topology q hq)
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    exact ⟨x, hx⟩

section

variable {A : Type*} [Category* A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [(topology S).HasSheafCompose (CategoryTheory.forget A)]

/-- A morphism of sheaves on the affine pro-étale site with values in a concrete category is
locally surjective if and only if every section of the target lifts after pullback along a
single surjection. -/
lemma isLocallySurjective_iff {F G : Sheaf (topology S) A} (φ : F ⟶ G) :
    Sheaf.IsLocallySurjective φ ↔
      ∀ (X : S.AffineProEt) (y : ToType (G.obj.obj (op X))), ∃ (W : S.AffineProEt) (q : W ⟶ X)
        (_ : Surjective q.left) (x : ToType (F.obj.obj (op W))),
          φ.hom.app (op W) x = G.obj.map q.op y := by
  rw [Sheaf.IsLocallySurjective, Presheaf.isLocallySurjective_iff_whisker_forget,
    isLocallySurjective_iff_of_isSheaf _
      ((sheafCompose _ (CategoryTheory.forget A)).obj F).property
      ((sheafCompose _ (CategoryTheory.forget A)).obj G).property]
  rfl

variable [HasLimitsOfShape ℕᵒᵖ A] [PreservesLimitsOfShape ℕᵒᵖ (CategoryTheory.forget A)]

/-- On the affine pro-étale site, a sequential limit of locally surjective morphisms of sheaves
is locally surjective onto the first term: since sequential limits of covers are covers
(`exists_compatible_surjective`), compatible lifts can be chosen over a single cover. -/
lemma isLocallySurjective_π_app_zero_of_isLocallySurjective_map
    {F : ℕᵒᵖ ⥤ Sheaf (topology S) A} {c : Cone F} (hc : IsLimit c)
    (hF : ∀ n, Sheaf.IsLocallySurjective (F.map (homOfLE (Nat.le_succ n)).op)) :
    Sheaf.IsLocallySurjective (c.π.app ⟨0⟩) := by
  rw [isLocallySurjective_iff]
  intro X y
  choose W q hq x hx using fun n ↦ (isLocallySurjective_iff _).mp (hF n)
  let seq (n : ℕ) : Σ Y : S.AffineProEt, ToType ((F.obj (op n)).obj.obj (op Y)) :=
    Nat.rec ⟨X, y⟩ (fun n p ↦ ⟨W n p.1 p.2, x n p.1 p.2⟩) n
  let π (n : ℕ) : (seq (n + 1)).1 ⟶ (seq n).1 := q n (seq n).1 (seq n).2
  obtain ⟨V, p, hp, hp0⟩ :=
    exists_compatible_surjective (W := fun n ↦ (seq n).1) (π := π) fun n ↦ hq _ _ _
  let E := sheafToPresheaf (topology S) A ⋙ (CategoryTheory.evaluation _ A).obj (op V) ⋙
    CategoryTheory.forget A
  have hc' : IsLimit (E.mapCone c) := isLimitOfPreserves E hc
  have key (n : ℕ) : (F.map (homOfLE (n.le_add_right 1)).op).hom.app (op V)
      ((F.obj (op (n + 1))).obj.map (p (n + 1)).op (seq (n + 1)).2) =
        (F.obj (op n)).obj.map (p n).op (seq n).2 :=
    calc _ = (F.obj (op n)).obj.map (p (n + 1)).op
          ((F.map (homOfLE (n.le_add_right 1)).op).hom.app _ (x n (seq n).1 (seq n).2)) :=
          NatTrans.naturality_apply _ _ _
      _ = (F.obj (op n)).obj.map (p (n + 1)).op ((F.obj (op n)).obj.map (π n).op (seq n).2) := by
          rw [hx]
      _ = _ := by rw [← Functor.map_comp_apply, ← op_comp, hp n]
  let s : Cone (F ⋙ E) :=
    { pt := PUnit
      π := NatTrans.ofOpSequence (fun n ↦ ↾fun _ ↦ (F.obj (op n)).obj.map (p n).op (seq n).2)
        fun n ↦ by
          ext ⟨⟩
          exact (key n).symm }
  let t : ToType (c.pt.obj.obj (op V)) := hc'.lift s PUnit.unit
  refine ⟨V, p 0, hp0, t, ?_⟩
  exact ConcreteCategory.congr_hom (hc'.fac s (op 0)) PUnit.unit

end

section ModuleCat

variable {Λ : Type (u + 1)} [Ring Λ]

/-- On the affine pro-étale site, the projection `lim Fₙ ⟶ F₀` of a tower of epimorphisms of
sheaves of modules is an epimorphism. -/
lemma epi_π_app_zero_of_epi : EpiπAppZeroOfEpi (Sheaf (topology S) (ModuleCat.{u + 1} Λ)) := by
  intro F c hc hF
  have h {M N : Sheaf (topology S) (ModuleCat.{u + 1} Λ)} (φ : M ⟶ N) :
      Sheaf.IsLocallySurjective φ ↔ Epi φ :=
    Sheaf.isLocallySurjective_iff_epi' _ φ
  simp_rw [← h] at hF ⊢
  exact isLocallySurjective_π_app_zero_of_isLocallySurjective_map hc hF

/-- Countable products of epimorphisms of sheaves of modules on the affine pro-étale site are
epimorphisms. -/
instance epi_pi_map {M N : ℕ → Sheaf (topology S) (ModuleCat.{u + 1} Λ)} (f : ∀ n, M n ⟶ N n)
    [∀ n, Epi (f n)] : Epi (Limits.Pi.map f) :=
  have := Abelian.hasFiniteBiproducts (C := Sheaf (topology S) (ModuleCat.{u + 1} Λ))
  epi_pi_map_of_epi_π_app_zero epi_π_app_zero_of_epi f

/-- **Repleteness of the affine pro-étale topos**: sheaves of modules on the affine pro-étale
site satisfy countable AB4\*, i.e. countable products are exact. -/
instance countableAB4Star : CountableAB4Star (Sheaf (topology S) (ModuleCat.{u + 1} Λ)) :=
  .of_epi_π_app_zero epi_π_app_zero_of_epi

end ModuleCat

end AlgebraicGeometry.Scheme.AffineProEt

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]

/-- On the pro-étale site, the projection `lim Fₙ ⟶ F₀` of a tower of epimorphisms of sheaves of
modules is an epimorphism. This is transported from the affine pro-étale site along the
equivalence `AffineProEt.isEquivalence_sheafPushforwardContinuous_toProEt`. -/
lemma epi_π_app_zero_of_epi : EpiπAppZeroOfEpi (Sheaf (topology S) (ModuleCat.{u + 1} Λ)) := by
  intro F c hc hF
  let e := (AffineProEt.toProEt S).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
    (AffineProEt.topology S) (topology S)
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} Λ) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  apply e.epi_of_epi_map
  exact AffineProEt.epi_π_app_zero_of_epi (F := F ⋙ e) (isLimitOfPreserves e hc)
    fun n ↦ e.map_epi _

/-- Countable products of epimorphisms of sheaves of modules on the pro-étale site are
epimorphisms. -/
instance epi_pi_map {M N : ℕ → Sheaf (topology S) (ModuleCat.{u + 1} Λ)} (f : ∀ n, M n ⟶ N n)
    [∀ n, Epi (f n)] : Epi (Limits.Pi.map f) :=
  have := Abelian.hasFiniteBiproducts (C := Sheaf (topology S) (ModuleCat.{u + 1} Λ))
  epi_pi_map_of_epi_π_app_zero epi_π_app_zero_of_epi f

/-- **Repleteness of the pro-étale topos** (Bhatt–Scholze, Proposition 4.2.8): sheaves of
modules on the pro-étale site satisfy countable AB4\*, i.e. countable products are exact. -/
instance countableAB4Star : CountableAB4Star (Sheaf (topology S) (ModuleCat.{u + 1} Λ)) :=
  .of_epi_π_app_zero epi_π_app_zero_of_epi

end AlgebraicGeometry.Scheme.ProEt
