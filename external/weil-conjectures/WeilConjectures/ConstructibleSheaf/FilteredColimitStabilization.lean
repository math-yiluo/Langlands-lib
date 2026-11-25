/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FilteredColimit
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Noetherian

/-!
# Constructible sheaves are not unions of strictly increasing families of subsheaves

Let `X` be a Noetherian scheme and `Λ` a finite ring. A constructible étale sheaf `F` of
`Λ`-modules on `X` which is the colimit of a filtered diagram of subsheaves is equal to one of
them (`AlgebraicGeometry.Etale.exists_epi_ι_app_of_isConstructibleSheaf`): its stalks are finite,
hence each is attained at some stage, the locus where a stage is attained is a constructible
neighbourhood of the point (`AlgebraicGeometry.Etale.exists_isConstructible_sheafFiber_map_eq_zero`
applied to the cokernels), and a Noetherian induction makes one stage work at all points.

This is the finiteness input of Deligne's approximation of a sheaf by a constructible subsheaf
on the geometric generic fibres of coordinates (SGA 4½, [Th. finitude], proof of 3.2).
-/

@[expose] public section

universe w w' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- **A constructible sheaf which is a filtered union of subsheaves equals one of them.** On a
Noetherian scheme, let `c` be a colimit cocone of a filtered diagram of étale sheaves of modules
over a finite ring, with monomorphic legs and constructible apex. Then some leg is an
epimorphism. -/
theorem exists_epi_ι_app_of_isConstructibleSheaf {X : Scheme.{u}} [IsNoetherian X]
    {J : Type w} [Category.{w'} J] [IsFiltered J]
    {D : J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {c : Cocone D} (hc : IsColimit c)
    (hmono : ∀ j, Mono (c.ι.app j)) (hF : IsConstructibleSheaf c.pt) :
    ∃ j, Epi (c.ι.app j) := by
  classical
  have : Nonempty J := IsFiltered.nonempty
  let P (x : X) := (pointSmallEtale (X.algClosurePoint x)).sheafFiber (A := ModuleCat.{u + 1} Λ)
  let φ (x : X) (j : J) : (P x).obj (D.obj j) ⟶ (P x).obj c.pt := (P x).map (c.ι.app j)
  -- the images of the stalk maps increase along the diagram
  have hle {j j' : J} (f : j ⟶ j') (x : X) :
      LinearMap.range (φ x j).hom ≤ LinearMap.range (φ x j').hom := by
    rintro _ ⟨a, rfl⟩
    refine ⟨(P x).map (D.map f) a, ?_⟩
    have h := ConcreteCategory.congr_hom
      (((P x).map_comp _ _).symm.trans (congrArg (P x).map (c.w f))) a
    rwa [ConcreteCategory.comp_apply] at h
  have hmon {j j' : J} (f : j ⟶ j') (x : X) (h : Function.Surjective (φ x j)) :
      Function.Surjective (φ x j') :=
    fun m ↦ hle f x (h m)
  -- every stalk is attained at some stage, the stalks of `c.pt` being finite
  have hpt (x : X) : ∃ j, Function.Surjective (φ x j) := by
    have : PreservesColimitsOfSize.{w', w} (P x) :=
      ((pointSmallEtale (X.algClosurePoint x)).skyscraperSheafAdjunction
        (A := ModuleCat.{u + 1} Λ)).leftAdjoint_preservesColimits
    have hc' : IsColimit ((P x).mapCocone c) := isColimitOfPreserves (P x) hc
    let N : Submodule Λ ((P x).obj c.pt) := ⨆ j, LinearMap.range (φ x j).hom
    let q : (P x).obj c.pt ⟶ ModuleCat.of Λ ((P x).obj c.pt ⧸ N) := ModuleCat.ofHom N.mkQ
    have hq : q = 0 := by
      refine hc'.hom_ext fun j ↦ ?_
      rw [comp_zero]
      refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
      change N.mkQ (φ x j m) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_iSup_of_mem j ⟨m, rfl⟩
    have hN : N = ⊤ := by
      rw [eq_top_iff]
      intro m _
      have : N.mkQ m = 0 := by
        change q m = (0 : (P x).obj c.pt ⟶ ModuleCat.of Λ ((P x).obj c.pt ⧸ N)) m
        rw [hq]
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    have hdir : Directed (· ≤ ·) fun j ↦ LinearMap.range (φ x j).hom := fun j₁ j₂ ↦
      ⟨IsFiltered.max j₁ j₂, hle (IsFiltered.leftToMax j₁ j₂) x,
        hle (IsFiltered.rightToMax j₁ j₂) x⟩
    have : Module.Finite Λ ((P x).obj c.pt) := (ModuleCat.isFinitelyGenerated_iff _).1
      (hF.isFiniteSheaf.isFinitelyGenerated_sheafFiber _ (X.algClosurePoint x))
    have : Fintype ((P x).obj c.pt) := @Fintype.ofFinite _ (Module.finite_of_finite Λ)
    have hm (m : (P x).obj c.pt) : ∃ j, m ∈ LinearMap.range (φ x j).hom :=
      (Submodule.mem_iSup_of_directed _ hdir).1 (by
        change m ∈ N
        rw [hN]
        exact Submodule.mem_top)
    choose jm hjm using hm
    let O := Finset.univ.image jm
    exact ⟨IsFiltered.sup O ∅, fun m ↦
      hle (IsFiltered.toSup O ∅ (Finset.mem_image_of_mem jm (Finset.mem_univ m))) x (hjm m)⟩
  -- near every point some stage is surjective on stalks
  have hC (j : J) : IsConstructibleSheaf (Limits.cokernel (c.ι.app j)) :=
    have : IsConstructibleSheaf (D.obj j) :=
      Scheme.IsConstructibleSheaf.of_mono (F := c.pt) (c.ι.app j)
    IsConstructibleSheaf.cokernel (G := c.pt) _
  have hnbhd (x : X) : ∃ j, ∃ E : Set X, Topology.IsConstructible E ∧ x ∈ E ∧
      ∀ y ∈ E, Function.Surjective (φ y j) := by
    obtain ⟨j, hj⟩ := hpt x
    have := hC j
    obtain ⟨E, hE, hxE, hEz⟩ := exists_isConstructible_sheafFiber_map_eq_zero
      (𝟙 (Limits.cokernel (c.ι.app j))) x (by
        rw [CategoryTheory.Functor.map_id, ← IsZero.iff_id_eq_zero]
        exact (isZero_sheafFiber_cokernel_iff _ _).2 hj)
    refine ⟨j, E, hE, hxE, fun y hy ↦ (isZero_sheafFiber_cokernel_iff _ _).1 ?_⟩
    rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id]
    exact hEz y hy
  choose jx E hE hxE hES using hnbhd
  -- finitely many of these neighbourhoods cover `X`
  have hcov : (Set.univ : Set X) ⊆ ⋃ x, E x := fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxE x⟩
  obtain ⟨T₀, hT₀⟩ :=
    (isCompact_univ (X := WithConstructibleTopology X)).elim_finite_subcover
    (fun x ↦ WithTopology.ofTopology ⁻¹' E x)
    (fun x ↦ by
      rw [WithConstructibleTopology.isOpen_iff]
      exact (hE x).isClopen_constructibleTopology.2)
    (fun w _ ↦ by simpa using hcov (Set.mem_univ (WithTopology.ofTopology w)))
  have hT (y : X) : y ∈ ⋃ x ∈ T₀, E x := by
    simpa using hT₀ (Set.mem_univ (WithTopology.toTopology _ y))
  -- a stage above the corresponding stages is surjective on all stalks
  let O := T₀.image jx
  let j₀ := IsFiltered.sup O ∅
  have hall (y : X) : IsZero ((P y).obj (Limits.cokernel (c.ι.app j₀))) := by
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (hT y)
    exact (isZero_sheafFiber_cokernel_iff _ _).2
      (hmon (IsFiltered.toSup O ∅ (Finset.mem_image_of_mem jx hx)) y (hES x y hy))
  have : IsIso (0 : Limits.cokernel (c.ι.app j₀) ⟶ _) :=
    isIso_of_isIso_sheafFiber_map _ fun x ↦ by
      have hx : IsZero ((X.uliftPointSmallEtale x).sheafFiber.obj
          (Limits.cokernel (c.ι.app j₀))) :=
        (hall x).of_iso (((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso _).app _)
      exact ⟨0, hx.eq_of_src _ _, hx.eq_of_src _ _⟩
  exact ⟨j₀, Preadditive.epi_of_isZero_cokernel _ (by
    rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : Limits.cokernel (c.ι.app j₀) ⟶
      Limits.cokernel (c.ι.app j₀)), zero_comp])⟩

end Etale

end AlgebraicGeometry
