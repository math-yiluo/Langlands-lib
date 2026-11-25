/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.AffineCoverModuleTensorFlatCriterion
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Affine module comparisons for eventual flatness

Source: Stacks Project, Limits, Tag 05LY, affine-local reduction with the target
scheme equal to the base; Properties, Tag 01PC; Morphisms, Tag 01U4.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Finite affine charts identify limit flatness with flatness of tensor modules and
allow stage flatness to be glued. This comparison asserts no eventual flatness.
Source: Stacks Project, Limits, Tag 05LY, affine-local reduction with Y_i = S_i;
Properties, Tag 01PC; Morphisms, Tag 01U4.
(blueprint: lem-pc-flat-module-descent-affine-charts).

Proof: Since the base Spec(R_i) is affine and f is quasi-compact, X_i is
quasi-compact. Choose a finite affine open cover U_b of X_i, and put B_b = O(U_b)
and N_b = M(U_b), with a_b the map on sections induced by f. Local finite
presentation of f makes B_b a finitely presented R_i-algebra. Quasi-coherence and
finite presentation of M make N_b a finitely presented B_b-module (01PC).
The spectrum of colim R is the limit of the spectra of R_k. Uniqueness of limits
identifies it with c.pt, compatibly with every projection. The pullbacks of U_b
are spectra of R_k tensor_{R_i} B_b at stage k and of (colim R) tensor_{R_i} B_b
at the limit. Sections of the tensor pullback are the corresponding scalar
extensions of N_b. The displayed iterated tensor with R_i is canonically the
same scalar extension, since T tensor_{R_i} R_i is T. Limit flatness therefore
gives each displayed limit module flat over (colim R) tensor_{R_i} R_i.
At any stage k, flatness of all the displayed modules gives relative flatness
on these pulled-back affine charts by 01U4. They cover the base-changed source,
so 01U4 glues their flatness to IsFlatOver on the entire source. There is no
uniform stage or descent assertion here. The empty source uses n = 0 and the
last conclusion is vacuous; zero chart modules and the zero ring cause no
exception. No module or algebra is chosen from an unproved theorem in a
definition: B_b and N_b are the actual rings and sections of the chosen opens. -/
theorem exists_flat_module_descent_affine_charts
    {I : Type u} [PartialOrder I] [IsDirectedOrder I]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : Xi.Modules) [M.IsFinitePresentation] [M.IsQuasicoherent]
    (hflat : Scheme.Modules.IsFlatOver
      ((Scheme.Modules.tensorPullback (pullback.fst f (c.π.app (op i)))).obj M)
      (pullback.snd f (c.π.app (op i)))) :
    ∃ n : ℕ, ∃ B : Fin n → CommRingCat.{u},
      ∃ N : (b : Fin n) → ModuleCat.{u} (B b),
        ∃ a : (b : Fin n) → (R.obj i : Type u) →+* (B b : Type u),
          (∀ b, letI := (a b).toAlgebra
            Algebra.FinitePresentation (R.obj i : Type u) (B b : Type u)) ∧
          (∀ b, Module.FinitePresentation (B b : Type u) (N b)) ∧
          (∀ b, letI : Module (R.obj i : Type u) (N b) := Module.compHom _ (a b)
            letI : Algebra (R.obj i : Type u) ((colimit.cocone R).pt : Type u) :=
              ((colimit.cocone R).ι.app i).hom.toAlgebra
            letI : Algebra (R.obj i : Type u)
                (((colimit.cocone R).pt : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u)) :=
              Algebra.TensorProduct.rightAlgebra
            letI : Module (R.obj i : Type u)
                (((colimit.cocone R).pt : Type u) ⊗[(R.obj i : Type u)]
                  (R.obj i : Type u)) := Algebra.toModule
            Module.Flat
              (((colimit.cocone R).pt : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u))
              ((((colimit.cocone R).pt : Type u)
                ⊗[(R.obj i : Type u)] (R.obj i : Type u))
                ⊗[(R.obj i : Type u)] (N b))) ∧
          (∀ (k : I) (hik : i ≤ k),
            (∀ b, letI : Module (R.obj i : Type u) (N b) := Module.compHom _ (a b)
              letI : Algebra (R.obj i : Type u) (R.obj k : Type u) :=
                (R.map (homOfLE hik)).hom.toAlgebra
              letI : Algebra (R.obj i : Type u)
                  ((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u)) :=
                Algebra.TensorProduct.rightAlgebra
              letI : Module (R.obj i : Type u)
                  ((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u)) :=
                Algebra.toModule
              Module.Flat ((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u))
                (((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u))
                  ⊗[(R.obj i : Type u)] (N b))) →
            Scheme.Modules.IsFlatOver
              ((Scheme.Modules.tensorPullback
                (pullback.fst f (Spec.map (R.map (homOfLE hik))))).obj M)
              (pullback.snd f (Spec.map (R.map (homOfLE hik))))) := by
  classical
  let : CompactSpace Xi := QuasiCompact.compactSpace_of_compactSpace f
  have h (x : Xi) : ∃ U : Xi.affineOpens, x ∈ U.1 := by
    obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : Xi.Opens) from trivial)
    exact ⟨⟨U, hU⟩, hx⟩
  choose V hx using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : Xi ↦ ((V x).1 : Set Xi)) (fun x ↦ (V x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let ef := Fintype.equivFin t
  let U : Fin (Fintype.card t) → Xi.affineOpens := fun b ↦ V (ef.symm b)
  have hcover : ∀ x : Xi, ∃ b, x ∈ (U b).1 := by
    intro x
    obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨ef ⟨y, hyt⟩, by simpa [U] using hxy⟩
  let B : Fin (Fintype.card t) → CommRingCat.{u} := fun b ↦ Γ(Xi, (U b).1)
  let N : (b : Fin (Fintype.card t)) → ModuleCat.{u} (B b) :=
    fun b ↦ ModuleCat.of (B b) Γ(M, (U b).1)
  let a := fun b ↦ ((Scheme.ΓSpecIso (R.obj i)).inv ≫
    f.appLE ⊤ (U b).1 (by simp)).hom
  refine ⟨Fintype.card t, B, N, a, ?_, ?_, ?_, ?_⟩
  · intro b
    change (a b).FinitePresentation
    exact (f.finitePresentation_appLE (isAffineOpen_top _) (U b).2 (by simp)).comp
      (RingHom.FinitePresentation.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (R.obj i)).inv))
  · intro b
    exact Scheme.Modules.finitePresentation_sections_of_isFinitePresentation M (U b).2
  · let cs := Scheme.Spec.mapCone (colimit.cocone R).op
    have hs : IsLimit cs := isLimitOfPreserves Scheme.Spec (colimit.isColimit R).op
    let e := hc.conePointUniqueUpToIso hs
    have he : e.hom ≫ Spec.map ((colimit.cocone R).ι.app i) = c.π.app (op i) :=
      hc.conePointUniqueUpToIso_hom_comp hs (op i)
    exact (affine_cover_module_tensor_flat_criterion (R.obj i) _ f M U hcover
      ((colimit.cocone R).ι.app i) (c.π.app (op i)) e he).mp hflat
  · intro k hik hstage
    exact (affine_cover_module_tensor_flat_criterion (R.obj i) (R.obj k) f M U hcover
      (R.map (homOfLE hik)) (Spec.map (R.map (homOfLE hik))) (Iso.refl _) (by simp)).mpr
      hstage

end AlgebraicGeometry
