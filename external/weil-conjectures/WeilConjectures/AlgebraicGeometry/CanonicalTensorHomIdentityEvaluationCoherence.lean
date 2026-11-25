/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomEvaluationNaturality

/-! # Equality transport for normalized identity evaluation

Source: Stacks Project, cohomology.tex, Tag 08DJ; sites-cohomology.tex, Tags 0A90, 0A96.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

private theorem evaluation_equality_transport {C : Type*} [Category C]
    [MonoidalCategory C] (H : Cᵒᵖ × C ⥤ C)
    {L M L' M' : C} (hL : L = L') (hM : M = M')
    (E : H.obj (op L, M) ⊗ L ⟶ M)
    (E' : H.obj (op L', M') ⊗ L' ⟶ M')
    (h : (H.map ((eqToIso hL).hom.op, (eqToIso hM).inv) ⊗ₘ 𝟙 L) ≫ E =
      (𝟙 _ ⊗ₘ (eqToIso hL).hom) ≫ E' ≫ (eqToIso hM).inv) :
    HEq E E' := by
  subst L'
  subst M'
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, op_id] at h
  have hid : (𝟙 (op L), 𝟙 M) = 𝟙 (op L, M) := rfl
  rw [hid, H.map_id] at h
  simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id] at h
  exact heq_of_eq h

/-- Normalized evaluation at the identity depends only on the literal derived objects.
Source: Stacks Project, cohomology.tex, Tag 08DJ; sites-cohomology.tex, Tags 0A90, 0A96.
(blueprint: lem-pc-tensor-hom-identity-evaluation-coherence).

Proof: Resolve L and L' by K-flat complexes and use the fixed K-injective resolutions
of M and M'. On these models, evaluation is the counit of the componentwise sheaf
Hom-tensor adjunction, extended over the coproduct defining the total tensor. Hom
from a K-flat complex into a K-injective complex is K-injective, so comparison roofs
compute the internal-Hom comparison uniquely modulo chain homotopy. Evaluation
commutes with the comparison maps on each tensor summand by the sheaf adjunction
and the Hom projections. The Hom differential formula makes homotopic comparison
maps give homotopic evaluation maps, with the total tensor Koszul signs. Localize
these identities and cancel the resolution quasi-isomorphisms. Naturality of the
internal-Hom resolution isomorphism and of the inverse augmentation identifies the
result with the displayed normalized identity evaluations. For literal equalities
of the derived objects the comparison arrows are equality isomorphisms; equality
induction reduces their transport to identities, giving HEq. No source P or map
into Hom occurs in this assertion. Zero and unbounded complexes cause no change:
all identities are checked on the same total tensor summands. -/
theorem tensorHomIdentityEvaluation_coherence (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L M L' M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hL : DerivedCategory.Q.obj L = DerivedCategory.Q.obj L')
    (hM : DerivedCategory.Q.obj M = DerivedCategory.Q.obj M') :
    letI := schemeDerivedTensorMonoidal X
    HEq (((schemeDerivedInternalHomResolutionIso X L M).hom ⊗ₘ
          𝟙 (DerivedCategory.Q.obj L)) ≫
        pullbackTensorModelMap X _ L ≫
          DerivedCategory.Q.map (schemeTensorHomUncurry X _ L M (𝟙 _)) ≫
            schemeHomResolutionInverse X M)
      (((schemeDerivedInternalHomResolutionIso X L' M').hom ⊗ₘ
          𝟙 (DerivedCategory.Q.obj L')) ≫
        pullbackTensorModelMap X _ L' ≫
          DerivedCategory.Q.map (schemeTensorHomUncurry X _ L' M' (𝟙 _)) ≫
            schemeHomResolutionInverse X M') := by
  let := schemeDerivedTensorMonoidal X
  exact evaluation_equality_transport
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf) hL hM _ _
    (tensorHomEvaluation_natural X L M L' M' (eqToIso hL) (eqToIso hM))

end AlgebraicGeometry
