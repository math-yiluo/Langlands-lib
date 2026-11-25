/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Adjunction.Lifting.Left

/-! # Scalar extension for left modules over arbitrary rings

Source: Stacks Project, Modules on Sites, Section 6.3, scalar extension construction;
its balanced-tensor universal property
(blueprint: def-pod-ring-scalar-extension).
-/

@[expose] public section

universe uR vC

open CategoryTheory

namespace ModuleCat

variable {R S : Type uR} [Ring R] [Ring S]

-- The Mathlib free-module adjunction uses one universe for the ring and generators.
-- Here the generators may live in the larger universe required by module sheaves.
private noncomputable def largeFree (A : Type uR) [Ring A] :
    Type (max uR vC) ⥤ ModuleCat.{max uR vC} A where
  obj X := ModuleCat.of A (X →₀ A)
  map f := ofHom (Finsupp.lmapDomain A A f)

private noncomputable def largeFreeHomEquiv (A : Type uR) [Ring A]
    (X : Type (max uR vC)) (M : ModuleCat.{max uR vC} A) :
    ((largeFree A).obj X ⟶ M) ≃ (X ⟶ (forget (ModuleCat A)).obj M) where
  toFun φ := ↾fun x ↦ φ (Finsupp.single x 1)
  invFun ψ := ofHom (Finsupp.lift M A X ψ)
  left_inv φ := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simp
    rfl
  right_inv ψ := by
    ext x
    dsimp
    erw [Finsupp.lift_apply, Finsupp.sum_single_index]
    all_goals simp

private noncomputable def largeFreeAdj (A : Type uR) [Ring A] :
    largeFree.{uR, vC} A ⊣ forget (ModuleCat.{max uR vC} A) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := largeFreeHomEquiv A
      homEquiv_naturality_left_symm := by
        intro X Y M f g
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext'
        intro x
        apply LinearMap.ext_ring
        simp [largeFreeHomEquiv, largeFree] }

/-- Restriction of scalars has a left adjoint for arbitrary rings.
Source: the balanced-tensor construction, Stacks Project, Modules on Sites, Section 6.3
(blueprint: def-pod-ring-scalar-extension).
Proof: the free-module/forgetful adjunction has surjective counit, since the
basis vector at m maps to m. In the abelian category of modules this counit is a
regular epimorphism. Restriction followed by forgetting is the forgetful functor
for S-modules, which also has a free-module left adjoint. The adjoint triangle
theorem therefore supplies a left adjoint to restriction, using reflexive
coequalizers in S-modules. This constructs the same balanced scalar extension
by its universal property. The free modules allow generators in max uR vC. -/
theorem isRightAdjoint_restrictScalars (f : R →+* S) :
    (restrictScalars.{max uR vC} f).IsRightAdjoint := by
  have : (restrictScalars.{max uR vC} f ⋙
      forget (ModuleCat.{max uR vC} R)).IsRightAdjoint := by
    change (forget (ModuleCat.{max uR vC} S)).IsRightAdjoint
    exact (largeFreeAdj S).isRightAdjoint
  apply isRightAdjoint_triangle_lift (restrictScalars f) (largeFreeAdj R)
  intro M
  have : Epi ((largeFreeAdj R).counit.app M) := by
    apply (ModuleCat.epi_iff_surjective _).2
    intro m
    refine ⟨Finsupp.single m 1, ?_⟩
    dsimp [largeFreeAdj, Adjunction.mkOfHomEquiv, largeFreeHomEquiv]
    erw [Finsupp.lift_apply, Finsupp.sum_single_index]
    all_goals simp
  exact regularEpiOfEpi _

/-- The balanced tensor S tensor_R M, characterized as the left adjoint to restriction.
The chosen data satisfy the full adjunction.
Source: Stacks Project, Modules on Sites, Section 6.3
(blueprint: def-pod-ring-scalar-extension). -/
noncomputable def ringExtendScalars (f : R →+* S) :
    ModuleCat.{max uR vC} R ⥤ ModuleCat.{max uR vC} S :=
  @Functor.leftAdjoint _ _ _ _ (restrictScalars f) (isRightAdjoint_restrictScalars f)

/-- The universal property of the balanced tensor.
Source: Stacks Project, Modules on Sites, Section 6.3
(blueprint: def-pod-ring-scalar-extension). -/
noncomputable def ringExtendScalarsAdj (f : R →+* S) :
    ringExtendScalars.{uR, vC} f ⊣ restrictScalars f :=
  @Adjunction.ofIsRightAdjoint _ _ _ _ (restrictScalars f)
    (isRightAdjoint_restrictScalars f)

/-- The pure tensor s tensor m is s times the universal image of m.
Source: Stacks Project, Modules on Sites, Section 6.3
(blueprint: def-pod-ring-scalar-extension). -/
noncomputable def ringExtensionTmul (f : R →+* S) (M : ModuleCat.{max uR vC} R)
    (s : S) (m : M) : (ringExtendScalars.{uR, vC} f).obj M :=
  s • (show (ringExtendScalars.{uR, vC} f).obj M from
    (ringExtendScalarsAdj.{uR, vC} f).unit.app M m)

/-- The canonical comparison for composite scalar extensions, by adjoint uniqueness.
Source: Stacks Project, Modules on Sites, Section 6.3
(blueprint: def-pod-ring-scalar-extension). -/
noncomputable def ringExtensionComp {T : Type uR} [Ring T]
    (f : R →+* S) (g : S →+* T) :
    ringExtendScalars.{uR, vC} f ⋙ ringExtendScalars g ≅ ringExtendScalars (g.comp f) :=
  ((ringExtendScalarsAdj f).comp (ringExtendScalarsAdj g)).leftAdjointUniq
    ((ringExtendScalarsAdj (g.comp f)).ofNatIsoRight
      (restrictScalarsComp' f g (g.comp f) rfl))

end ModuleCat

namespace CategoryTheory

variable {C : Type vC} [Category C] (J : GrothendieckTopology C)
  {R S : Type uR} [Ring R] [Ring S]
  [HasWeakSheafify J (ModuleCat.{max uR vC} S)]

/-- Scalar extension of module sheaves is the sheafification of sectionwise extension.
Source: Stacks Project, Modules on Sites, Section 6.3
(blueprint: def-pod-ring-scalar-extension). -/
noncomputable def Sheaf.ringExtendScalars (f : R →+* S) :
    Sheaf J (ModuleCat.{max uR vC} R) ⥤ Sheaf J (ModuleCat.{max uR vC} S) :=
  sheafToPresheaf J _ ⋙
    (Functor.whiskeringRight _ _ _).obj (ModuleCat.ringExtendScalars f) ⋙
      presheafToSheaf J _

end CategoryTheory
