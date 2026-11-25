/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction

/-! # Closed symmetric monoidal dualizability criterion

Source: Stacks Project, Cohomology, Tag 0FPC
(blueprint: lem-pc-dualizable-evaluation-criterion).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem evaluation_slide {C : Type*} [Category C] [MonoidalCategory C]
    (K D : C) (e : D ⊗ K ⟶ 𝟙_ C) (η : 𝟙_ C ⟶ K ⊗ D) :
    ((ρ_ D).inv ≫ (𝟙 D ⊗ₘ η) ≫ (α_ D K D).inv ≫
      (e ⊗ₘ 𝟙 D) ≫ (λ_ D).hom) ▷ K ≫ e =
    D ◁ ((λ_ K).inv ≫ (η ⊗ₘ 𝟙 K) ≫ (α_ K D K).hom ≫
      (𝟙 K ⊗ₘ e) ≫ (ρ_ K).hom) ≫ e := by
  calc
    _ = 𝟙 (D ⊗ K) ⊗≫ (D ◁ η) ▷ K ⊗≫
        (e ▷ (D ⊗ K) ≫ (𝟙_ C) ◁ e) ≫ (λ_ (𝟙_ C)).hom := by monoidal
    _ = 𝟙 (D ⊗ K) ⊗≫ (D ◁ η) ▷ K ⊗≫
        ((D ⊗ K) ◁ e ≫ e ▷ (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom := by
      rw [whisker_exchange]
    _ = _ := by monoidal

/- The evaluation isomorphism criterion for a dualizable object in `D(O_X)`.
The bijection `adj` is a tensor--internal-Hom bijection of
`lem-sc-derived-internal-hom-adjunction`, with the naturality equation of
`scheme_derivedInternalHom_adjunction` as hypothesis `hadj`.
Source: Stacks Project, Cohomology, Tag 0FPC
(blueprint: lem-pc-dualizable-evaluation-criterion).

Proof:
1. Naturality of the adjunction in its first variable: for `f : A → B` and
   `g : B ⊗ K → M` with adjunct `g♭ : B → RHom(K,M)`, the adjunct of `(f ⊗ 1_K) ≫ g`
   is `f ≫ g♭`. Take `A = O_X`, `B = K ⊗ D`, `f = η`, `g = 1_K ⊗ e`, whose adjunct is
   `φ_K`. The adjunct of `(η ⊗ 1_K) ≫ (1_K ⊗ e)` is `η ≫ φ_K`, the adjunct of `id_K` by
   the definition of `η`; bijectivity gives the first triangle identity.
2. Put `g := (1_D ⊗ η) ≫ (e ⊗ 1_D) : D → D`. The map `φ_{O_X} : D = O_X ⊗ D → RHom(K,O_X)`
   is the adjunct of `e` and an isomorphism. By naturality, `g ≫ φ_{O_X}` is the adjunct of
   `(g ⊗ 1_K) ≫ e`. Bifunctoriality (`e ⊗ e` computed two ways) and Step 1 give
   `(g ⊗ 1_K) ≫ e = e`, so `g ≫ φ_{O_X} = φ_{O_X}` and `g = id_D` since `φ_{O_X}` is an
   isomorphism. Associators and unitors are inserted throughout. -/
/-- The second triangle identity isolated from the evaluation criterion.
The formal tensor--Hom naturality and bifunctoriality calculation is the
second zig-zag identity in Stacks Project, Cohomology, Tag 0FPC.
(blueprint: lem-pc-dualizable-evaluation-second-triangle) -/
theorem dualizable_evaluation_second_triangle (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K D : schemeDerivedCategory X)
    (adj : ∀ A B C : schemeDerivedCategory X,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)) ≃ (A ⊗ B ⟶ C))
    (hadj : ∀ (A A' B B' C C' : schemeDerivedCategory X)
      (a : A' ⟶ A) (b : B' ⟶ B) (c : C ⟶ C')
      (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)),
      adj A' B' C' (a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.op, c)) =
        (a ⊗ₘ b) ≫ adj A B C f ≫ c)
    (e : D ⊗ K ⟶ 𝟙_ (schemeDerivedCategory X))
    (φ : ∀ M : schemeDerivedCategory X,
      M ⊗ D ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op K, M))
    (hφ : ∀ M : schemeDerivedCategory X, IsIso (φ M))
    (hφ_def : ∀ M : schemeDerivedCategory X,
      φ M = (adj (M ⊗ D) K M).symm
        ((α_ M D K).hom ≫ (𝟙 M ⊗ₘ e) ≫ (ρ_ M).hom))
    (η : 𝟙_ (schemeDerivedCategory X) ⟶ K ⊗ D)
    (hη : η ≫ φ K =
      (adj (𝟙_ (schemeDerivedCategory X)) K K).symm ((λ_ K).hom)) :
 𝟙 D = (ρ_ D).inv ≫ (𝟙 D ⊗ₘ η) ≫ (α_ D K D).inv ≫
        (e ⊗ₘ 𝟙 D) ≫ (λ_ D).hom := by
  have hnat := hadj (K ⊗ D) (𝟙_ _) K K K K η (𝟙 K) (𝟙 K) (φ K)
  have hphi := hφ_def K
  have hfirst : (λ_ K).hom =
      (η ⊗ₘ 𝟙 K) ≫ (α_ K D K).hom ≫ (𝟙 K ⊗ₘ e) ≫ (ρ_ K).hom := by
    have hh := congrArg (adj (𝟙_ _) K K) hη
    simp only [Equiv.apply_symm_apply] at hh
    have hmap := CategoryTheory.Functor.map_id
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf) (op K, K)
    have hnat' :
        (adj (𝟙_ _) K K) (η ≫ φ K) =
          (η ⊗ₘ 𝟙 K) ≫ (adj (K ⊗ D) K K) (φ K) := by
      change (adj (𝟙_ _) K K)
        (η ≫ φ K ≫
          (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
            X.toRingedSpace.sheaf).map (𝟙 (op K, K))) = _ at hnat
      rw [hmap] at hnat
      simpa only [Category.comp_id] using hnat
    rw [hnat'] at hh
    rw [hphi] at hh
    simpa using hh.symm
  have hK : (λ_ K).inv ≫ (η ⊗ₘ 𝟙 K) ≫ (α_ K D K).hom ≫
      (𝟙 K ⊗ₘ e) ≫ (ρ_ K).hom = 𝟙 K := by
    rw [← hfirst, Iso.inv_hom_id]
  let I := 𝟙_ (schemeDerivedCategory X)
  let g := (ρ_ D).inv ≫ (𝟙 D ⊗ₘ η) ≫ (α_ D K D).inv ≫
    (e ⊗ₘ 𝟙 D) ≫ (λ_ D).hom
  have hg : (g ⊗ₘ 𝟙 K) ≫ e = e := by
    rw [tensorHom_id]
    dsimp only [g]
    rw [evaluation_slide, hK]
    simp
  have hnatural (A A' : schemeDerivedCategory X) (a : A' ⟶ A)
      (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op K, I)) :
      adj A' K I (a ≫ f) = (a ⊗ₘ 𝟙 K) ≫ adj A K I f := by
    have hn := hadj A A' K K I I a (𝟙 K) (𝟙 I) f
    have hmap := CategoryTheory.Functor.map_id
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf) (op K, I)
    change adj A' K I (a ≫ f ≫
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).map (𝟙 (op K, I))) = _ at hn
    rw [hmap] at hn
    simpa only [Category.comp_id] using hn
  let t := (λ_ D).inv ≫ φ I
  have ht : adj D K I t = e := by
    dsimp only [t]
    rw [hnatural, hφ_def, Equiv.apply_symm_apply]
    monoidal
  have hgt : g ≫ t = t := by
    apply (adj D K I).injective
    calc
      adj D K I (g ≫ t) = (g ⊗ₘ 𝟙 K) ≫ adj D K I t := hnatural D D g t
      _ = (g ⊗ₘ 𝟙 K) ≫ e := congrArg (fun f ↦ (g ⊗ₘ 𝟙 K) ≫ f) ht
      _ = e := hg
      _ = adj D K I t := ht.symm
  let : IsIso (φ I) := hφ I
  let : IsIso t := by
    dsimp only [t]
    infer_instance
  have hgid : g = 𝟙 D := by
    apply (cancel_mono t).1
    simpa only [Category.id_comp] using hgt
  exact hgid.symm

/-- (blueprint: lem-pc-dualizable-evaluation-criterion) -/
theorem dualizable_evaluation_criterion (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K D : schemeDerivedCategory X)
    (adj : ∀ A B C : schemeDerivedCategory X,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)) ≃ (A ⊗ B ⟶ C))
    (hadj : ∀ (A A' B B' C C' : schemeDerivedCategory X)
      (a : A' ⟶ A) (b : B' ⟶ B) (c : C ⟶ C')
      (f : A ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op B, C)),
      adj A' B' C' (a ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.op, c)) =
        (a ⊗ₘ b) ≫ adj A B C f ≫ c)
    (e : D ⊗ K ⟶ 𝟙_ (schemeDerivedCategory X))
    (φ : ∀ M : schemeDerivedCategory X,
      M ⊗ D ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op K, M))
    (hφ : ∀ M : schemeDerivedCategory X, IsIso (φ M))
    (hφ_def : ∀ M : schemeDerivedCategory X,
      φ M = (adj (M ⊗ D) K M).symm
        ((α_ M D K).hom ≫ (𝟙 M ⊗ₘ e) ≫ (ρ_ M).hom))
    (η : 𝟙_ (schemeDerivedCategory X) ⟶ K ⊗ D)
    (hη : η ≫ φ K =
      (adj (𝟙_ (schemeDerivedCategory X)) K K).symm ((λ_ K).hom)) :
    𝟙 K = (λ_ K).inv ≫ (η ⊗ₘ 𝟙 K) ≫ (α_ K D K).hom ≫
    (𝟙 K ⊗ₘ e) ≫ (ρ_ K).hom ∧
      𝟙 D = (ρ_ D).inv ≫ (𝟙 D ⊗ₘ η) ≫ (α_ D K D).inv ≫
        (e ⊗ₘ 𝟙 D) ≫ (λ_ D).hom := by
  have hnat := hadj (K ⊗ D) (𝟙_ _) K K K K η (𝟙 K) (𝟙 K) (φ K)
  have hphi := hφ_def K
  have hfirst : (λ_ K).hom =
      (η ⊗ₘ 𝟙 K) ≫ (α_ K D K).hom ≫ (𝟙 K ⊗ₘ e) ≫ (ρ_ K).hom := by
    have hh := congrArg (adj (𝟙_ _) K K) hη
    simp only [Equiv.apply_symm_apply] at hh
    have hmap := CategoryTheory.Functor.map_id
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf) (op K, K)
    have hnat' :
        (adj (𝟙_ _) K K) (η ≫ φ K) =
          (η ⊗ₘ 𝟙 K) ≫ (adj (K ⊗ D) K K) (φ K) := by
      change (adj (𝟙_ _) K K)
        (η ≫ φ K ≫
          (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
            X.toRingedSpace.sheaf).map (𝟙 (op K, K))) = _ at hnat
      rw [hmap] at hnat
      simpa only [Category.comp_id] using hnat
    rw [hnat'] at hh
    rw [hphi] at hh
    simpa using hh.symm
  constructor
  · rw [← cancel_epi (λ_ K).hom]
    simp only [Iso.hom_inv_id_assoc, Category.comp_id]
    exact hfirst
  · exact dualizable_evaluation_second_triangle X K D adj hadj e φ hφ hφ_def η hη


end AlgebraicGeometry
