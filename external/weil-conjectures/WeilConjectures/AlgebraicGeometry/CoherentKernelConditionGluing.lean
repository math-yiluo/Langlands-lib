/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Sites.CoversTop.Over
import WeilConjectures.AlgebraicGeometry.CoherentKernelIntersectionFiniteType

/-! # Finite local kernel generators from an open cover

Source: Stacks Project, Modules, Definitions 01BV and 01B5 and Section 01AF.
(blueprint: lem-weil-pbc-coherent-kernel-condition-descent-local-generators).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Flatten finite local generating families on a covering of a site.
The iterated-slice equivalence transports each generating epimorphism, while
`CoversTop.over` proves that the resulting family covers. This is the generators
analogue of Mathlib's `QuasicoherentData.bind`. -/
private theorem finite_generators_of_cover
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
    [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) (I : Type u) (V : I → C)
    (hV : J.CoversTop V) (hM : ∀ i, (M.over (V i)).IsFiniteType) :
    ∃ σ : LocalGeneratorsData.{u} M, σ.IsFiniteType := by
  classical
  let D (i : I) := (hM i).exists_localGeneratorsData.choose
  have hD (i : I) : (D i).IsFiniteType :=
    (hM i).exists_localGeneratorsData.choose_spec
  let σ : M.LocalGeneratorsData :=
    { I := (i : I) × (D i).I
      X := fun ij ↦ ((D ij.1).X ij.2).left
      coversTop := hV.over (fun i ↦ (D i).coversTop)
      generators := fun ij ↦ by
        let e := pushforwardPushforwardEquivalence
          (Over.iteratedSliceEquiv ((D ij.1).X ij.2))
          (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
          (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
        exact (((D ij.1).generators ij.2).map e.inverse (.refl _)).ofEpi
          (e.fullyFaithfulFunctor.preimageIso
            (by
              exact e.counitIso.app ((M.over (V ij.1)).over ((D ij.1).X ij.2)))).hom }
  refine ⟨σ, ⟨fun ij ↦ ?_⟩⟩
  have := (hD ij.1).isFiniteType ij.2
  dsimp only [σ]
  infer_instance

end SheafOfModules

namespace AlgebraicGeometry

/-- Construct finite local-generators data for a kernel from the corresponding kernel
condition on an open cover.  The construction restricts the global map to each
intersection with a member of the cover, uses sectionwise computation of kernels,
and transports finite generators across the resulting restriction isomorphisms.
The cover equality supplies, for every point, a member and a neighbourhood on which
these generators apply; assembling those neighbourhoods is the required local
generators datum.  This is the gluing step in the proof of finite-type descent.
Source: Stacks Project, Modules, Definitions 01BV and 01B5 and Section 01AF.
(blueprint: lem-weil-pbc-coherent-kernel-condition-descent-local-generators). -/
theorem coherent_kernel_condition_local_generators
    (X : Scheme.{u}) (F : X.Modules)
    (I : Type u) (U : I → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hK : ∀ (i : I) (V : (U i).toScheme.Opens) (n : ℕ)
      (f : SheafOfModules.free (R := (U i).toScheme.ringCatSheaf.over V)
        (ULift.{u} (Fin n)) ⟶ ((Scheme.Modules.restrictFunctor (U i).ι).obj F).over V),
      (kernel f).IsFiniteType)
    (W : X.Opens) (n : ℕ)
    (f : SheafOfModules.free (R := X.ringCatSheaf.over W) (ULift.{u} (Fin n)) ⟶
      F.over W) :
    ∃ σ : SheafOfModules.LocalGeneratorsData.{u} (kernel f), σ.IsFiniteType := by
  let V (i : I) : Over W := Over.mk (homOfLE (inf_le_left : W ⊓ U i ≤ W))
  have hV : ((_root_.Opens.grothendieckTopology X).over W).CoversTop V := by
    intro T
    rw [GrothendieckTopology.mem_over_iff, _root_.Opens.mem_grothendieckTopology]
    intro x hx
    have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
    let Z : X.Opens := T.left ⊓ U i
    refine ⟨Z, homOfLE inf_le_left, ?_, ⟨hx, hi⟩⟩
    apply (Sieve.overEquiv_iff _ _).mpr
    refine ⟨i, ⟨Over.homMk (homOfLE ?_)⟩⟩
    exact le_inf ((inf_le_left : Z ≤ T.left).trans (leOfHom T.hom)) inf_le_right
  have hlocal : ∀ i, ((kernel f).over (V i)).IsFiniteType := by
    intro i
    exact coherent_kernel_intersection_finiteType X F (U i) n (fun V g ↦ hK i V n g) W f
  exact SheafOfModules.finite_generators_of_cover (kernel f) I V hV hlocal

end AlgebraicGeometry
