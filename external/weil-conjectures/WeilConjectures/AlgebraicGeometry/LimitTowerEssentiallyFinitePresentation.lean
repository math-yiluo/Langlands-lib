/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
import WeilConjectures.RingTheory.EssentiallyFinitePresentationOverIntermediate
import WeilConjectures.AlgebraicGeometry.LimitTowerOverLocalSystem
import WeilConjectures.RingTheory.LocalRingColimitEssentiallyFiniteType

/-! # Limit presentation of an essentially finitely presented local tower
Source: literature/stacks-project/algebra.tex, proof of Lemma Tag 00R7
(blueprint: lem-weil-pbc-limit-tower-essentially-finite-presentation).
-/

@[expose] public section

universe u v p q

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingHom

/-- Limit presentation of a tower `R → S → S'` of local rings, `S` and `S'` essentially of
finite presentation over `R`, with a finitely presented `S'`-module `M`. The colimits are
colimit cocones over the directed set `Λ` (in `CommRingCat` and `AddCommGrpCat`);
scalar-extension maps are specified on pure tensors, and the module tensors put the new
scalar ring first (tensor symmetry matches the source).

Source: Stacks Project, Algebra, proof of Tag 00R7, with the constructions of Tags 00QU,
00QV and 00QX
(blueprint: lem-weil-pbc-limit-tower-essentially-finite-presentation).

Proof:
1. (Base system.) Write `R` as a directed colimit of local rings `R_λ` essentially of
   finite type over `ℤ` with local transition maps and local maps `π_λ : R_λ → R`
   [lemma-quasi-finite-coordinates--1].
2. (Middle ring.) Apply [lem-weil-pbc-limit-module-essentially-finite-presentation-over-system]
   to this system, `T = S`, `τ = α` and the zero module: on a tail `Λ₁` get local `S_λ`,
   local `ρ_λ`, `s_{μλ}`, `κ_λ` with `S = colim S_λ`, `S_λ` essentially of finite type over
   `R_λ`, and the base changes `S_λ ⊗ R_μ → S_μ`, `S_λ ⊗ R → S` localizations.
3. `S'` is essentially of finite presentation over `S` via `β`
   [lemma-quasi-finite-coordinates--1].
4. (Top ring and module.) Apply the same node to `(S_λ)_{Λ₁}`, `T = S'`, `τ = β` and `M`:
   on a tail `Λ₂` get `S'_λ`, `σ_λ`, `s'_{μλ}`, `κ'_λ`, modules `M_λ` with semilinear maps,
   `S' = colim S'_λ`, `M = colim M_λ`, the `M_λ` cokernels of `t × s` matrices, and the
   localization and module base-change clauses.
5. (Restriction.) `Λ₂` is cofinal in `Λ` and in `Λ₁`, so `R` and `S` remain the colimits
   over `Λ₂` [lem-weil-pbc-colimit-initial-full-subcategory].
6. (Conclusion.) Index everything by `Λ₂`; clauses (1)–(5) are steps 2, 4 and 5.
-/
theorem limit_tower_essentially_finite_presentation
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    (α : R →+* S) (β : S →+* S') [IsLocalHom α] [IsLocalHom β]
    -- `S` is essentially of finite presentation over `R` via `α`
    (B : Type p) [CommRing B] [Algebra R B] [Algebra.FinitePresentation R B]
    (W : Submonoid B) (f : B →+* S) (hf : f.comp (algebraMap R B) = α)
    (hS : letI := f.toAlgebra; IsLocalization W S)
    -- `S'` is essentially of finite presentation over `R` via `β ∘ α`
    (B' : Type q) [CommRing B'] [Algebra R B'] [Algebra.FinitePresentation R B']
    (W' : Submonoid B') (f' : B' →+* S') (hf' : f'.comp (algebraMap R B') = β.comp α)
    (hS' : letI := f'.toAlgebra; IsLocalization W' S')
    -- `M` is a finitely presented `S'`-module
    (M : Type v) [AddCommGroup M] [Module S' M]
    (s t : ℕ) (H : (Fin s → S') →ₗ[S'] (Fin t → S'))
    (hM : Nonempty (((Fin t → S') ⧸ LinearMap.range H) ≃ₗ[S'] M)) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (A Bs C : Λ ⥤ CommRingCat.{u}) (ρ : A ⟶ Bs) (σ : Bs ⟶ C)
      (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R))
      (κ : Bs ⟶ (Functor.const Λ).obj (CommRingCat.of S))
      (κ' : C ⟶ (Functor.const Λ).obj (CommRingCat.of S'))
      (D : Λ ⥤ AddCommGrpCat.{v})
      (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
      (_ : ∀ i : Λ, Module (C.obj i) (D.obj i)),
      -- local rings and local homomorphisms
      (∀ i, IsLocalRing (A.obj i)) ∧ (∀ i, IsLocalRing (Bs.obj i)) ∧
      (∀ i, IsLocalRing (C.obj i)) ∧
      (∀ i, IsLocalHom (ρ.app i).hom) ∧ (∀ i, IsLocalHom (σ.app i).hom) ∧
      (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (A.map (homOfLE h)).hom) ∧
      (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (Bs.map (homOfLE h)).hom) ∧
      (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (C.map (homOfLE h)).hom) ∧
      (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i))) ∧
      (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i))) ∧
      (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ'.app i))) ∧
      -- the maps to `R, S, S'` commute with `α, β`
      (∀ i, ρ.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom α) ∧
      (∀ i, σ.app i ≫ κ'.app i = κ.app i ≫ CommRingCat.ofHom β) ∧
      -- semilinearity of the module maps
      (∀ (i j : Λ) (h : i ≤ j) (y : C.obj i) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (C.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ i (y : C.obj i) (x : D.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ'.app i)) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) ∧
      -- (1) the colimits
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S') κ')) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)) ∧
      -- (2) essential finite type
      (∀ i, (algebraMap ℤ (A.obj i)).EssFiniteType) ∧
      (∀ i, (ρ.app i).hom.EssFiniteType) ∧
      (∀ i, (σ.app i).hom.EssFiniteType) ∧
      -- (3) finite generation, indeed cokernels of `t × s` matrices
      (∀ i, Module.Finite (C.obj i) (D.obj i)) ∧
      (∀ i, ∃ H₀ : (Fin s → C.obj i) →ₗ[C.obj i] (Fin t → C.obj i),
        Nonempty (((Fin t → C.obj i) ⧸ LinearMap.range H₀) ≃ₗ[C.obj i] D.obj i)) ∧
      -- (4) transition base changes
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (ρ.app i).hom.toAlgebra
        letI := (A.map (homOfLE h)).hom.toAlgebra
        ∃ φ : Bs.obj i ⊗[A.obj i] A.obj j →+* Bs.obj j,
          (∀ (x : Bs.obj i) (y : A.obj j),
            φ (x ⊗ₜ[A.obj i] y) = (Bs.map (homOfLE h)).hom x * (ρ.app j).hom y) ∧
          (letI := φ.toAlgebra
           ∃ U : Submonoid (Bs.obj i ⊗[A.obj i] A.obj j), IsLocalization U (Bs.obj j))) ∧
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (σ.app i).hom.toAlgebra
        letI := (Bs.map (homOfLE h)).hom.toAlgebra
        ∃ φ : C.obj i ⊗[Bs.obj i] Bs.obj j →+* C.obj j,
          (∀ (x : C.obj i) (y : Bs.obj j),
            φ (x ⊗ₜ[Bs.obj i] y) = (C.map (homOfLE h)).hom x * (σ.app j).hom y) ∧
          (letI := φ.toAlgebra
           ∃ U : Submonoid (C.obj i ⊗[Bs.obj i] Bs.obj j), IsLocalization U (C.obj j))) ∧
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (C.map (homOfLE h)).hom.toAlgebra
        ∃ e : C.obj j ⊗[C.obj i] D.obj i ≃ₗ[C.obj j] D.obj j,
          ∀ (y : C.obj j) (x : D.obj i),
            e (y ⊗ₜ[C.obj i] x) = y • (D.map (homOfLE h)).hom x) ∧
      -- (5) base changes to the limit
      (∀ i,
        letI := (ρ.app i).hom.toAlgebra
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)).toAlgebra
        ∃ φ : Bs.obj i ⊗[A.obj i] R →+* S,
          (∀ (x : Bs.obj i) (y : R),
            φ (x ⊗ₜ[A.obj i] y) =
              (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) x * α y) ∧
          (letI := φ.toAlgebra
           ∃ U : Submonoid (Bs.obj i ⊗[A.obj i] R), IsLocalization U S)) ∧
      (∀ i,
        letI := (σ.app i).hom.toAlgebra
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)).toAlgebra
        ∃ φ : C.obj i ⊗[Bs.obj i] S →+* S',
          (∀ (x : C.obj i) (y : S),
            φ (x ⊗ₜ[Bs.obj i] y) =
              (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ'.app i)) x * β y) ∧
          (letI := φ.toAlgebra
           ∃ U : Submonoid (C.obj i ⊗[Bs.obj i] S), IsLocalization U S')) ∧
      (∀ i,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ'.app i)).toAlgebra
        ∃ e : S' ⊗[C.obj i] D.obj i ≃ₗ[S'] M,
          ∀ (y : S') (x : D.obj i),
            e (y ⊗ₜ[C.obj i] x) =
              y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) := by
  have hα : α.EssFiniteType := by
    let : Algebra R S := α.toAlgebra
    let : Algebra B S := f.toAlgebra
    let : IsScalarTower R B S := IsScalarTower.of_algebraMap_eq' hf.symm
    let : IsLocalization W S := hS
    let : Algebra.EssFiniteType B S := Algebra.EssFiniteType.of_isLocalization S W
    exact Algebra.EssFiniteType.comp R B S
  obtain ⟨Q, _, _, hQ, V, g, hg, htop⟩ :=
    RingHom.essentially_finite_presentation_over_intermediate α β hα B' W' f' hf' hS'
  let : Algebra.FinitePresentation S Q := hQ
  obtain ⟨I, _, _, _, F, π₀, hFlocal, hFmap, hπlocal, hcolim, hFfinite⟩ :=
    CommRingCat.exists_local_essFiniteType_colimit R
  obtain ⟨Λ, _, _, _, J, _, Bs, C, ρ, σ, κ, κ', D, ν, inst, h⟩ :=
    limit_tower_over_local_system F π₀ hFlocal (fun i j h ↦ hFmap i j (homOfLE h))
      hπlocal hcolim hFfinite α β B W f hf hS Q V g hg htop M s t H hM
  let A := J ⋙ F
  let π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R) :=
    { app := fun i ↦ π₀.app (J.obj i)
      naturality := fun _ _ h ↦ π₀.naturality (J.map h) }
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  refine ⟨Λ, inferInstance, inferInstance, inferInstance, A, Bs, C, ρ, σ, π, κ, κ', D, ν,
    inst, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, ?_, h23, h24, h25, h26, h27, h28, h29⟩
  intro i
  obtain ⟨H₀, ⟨e⟩⟩ := h23 i
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

end RingHom
