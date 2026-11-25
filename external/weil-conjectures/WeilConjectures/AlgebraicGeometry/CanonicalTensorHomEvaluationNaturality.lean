/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomEvaluationPrecomposition
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomEvaluationPostcomposition

/-! # Naturality of localized tensor-Hom evaluation

Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96. (blueprint: lem-pc-tensor-hom-evaluation-naturality).
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

private theorem evaluation_naturality_of_components
    {C : Type*} [Category* C] [MonoidalCategory C]
    (H : Cᵒᵖ × C ⥤ C) (L M L' M' : C) (b : L ⟶ L') (c : M' ⟶ M)
    (e : H.obj (op L, M) ⊗ L ⟶ M)
    (ep : H.obj (op L', M) ⊗ L' ⟶ M)
    (e' : H.obj (op L', M') ⊗ L' ⟶ M')
    (hp : (H.map (b.op, 𝟙 M) ⊗ₘ 𝟙 L) ≫ e = (𝟙 _ ⊗ₘ b) ≫ ep)
    (hq : (H.map (𝟙 (op L'), c) ⊗ₘ 𝟙 L') ≫ ep = e' ≫ c) :
    (H.map (b.op, c) ⊗ₘ 𝟙 L) ≫ e = (𝟙 _ ⊗ₘ b) ≫ e' ≫ c := by
  have hm : H.map (X := (op L', M')) (Y := (op L, M)) (b.op, c) =
      H.map (X := (op L', M')) (Y := (op L', M)) (𝟙 (op L'), c) ≫
      H.map (X := (op L', M)) (Y := (op L, M)) (b.op, 𝟙 M) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hm, comp_tensor_id, Category.assoc, hp]
  rw [← Category.assoc, tensor_id_comp_id_tensor,
    ← id_tensor_comp_tensor_id, Category.assoc, hq]


/-- Evaluation at the identity of the fixed Hom complex is natural in both derived
variables. This concerns the evaluation morphism itself, with no choice of a map into
internal Hom.
Source: Stacks Project, cohomology.tex, Tag 08DJ; sites-cohomology.tex, Tags 0A90
and 0A96. (blueprint: lem-pc-tensor-hom-evaluation-naturality).

Proof: First resolve L and L' by K-flat complexes. Compute b on a common K-flat
roof and c by maps between the fixed K-injective resolutions. Evaluation of the
Hom complex commutes with precomposition in L and postcomposition in I(M): on
each tensor summand this is naturality of the sheaf tensor-Hom adjunction and of
the Hom projections. The coproduct universal property gives these equalities of
chain maps. The same componentwise uncurrying of degree-minus-one cochains takes
homotopies to homotopies, by the signed Hom differential formula, so these identities
hold for homotopy classes. Hom from a K-flat complex into a K-injective complex is
K-injective, allowing derived morphisms into these Hom complexes to be computed by
homotopy classes. Localize the evaluation identities and use naturality of the lax
tensor comparison, the internal-Hom resolution comparison and the augmentation into
I(M). Cancel the localized quasi-isomorphisms in the common roofs. For arbitrary L
and L', the Hom functor into I(M) inverts their K-flat resolutions; the derived tensor
also inverts these resolutions. Thus the localized identities give the displayed
square on the original objects. The identity evaluations are genuine chain maps;
no data is chosen from an existence assertion. This argument includes zero objects,
zero maps and identity comparisons, and imposes no boundedness condition. -/
theorem tensorHomEvaluation_natural (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (L M L' M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (b : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj L')
    (c : DerivedCategory.Q.obj M ≅ DerivedCategory.Q.obj M') :
    letI := schemeDerivedTensorMonoidal X
    let E := fun L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ↦
      ((schemeDerivedInternalHomResolutionIso X L M).hom ⊗ₘ
          𝟙 (DerivedCategory.Q.obj L)) ≫
        pullbackTensorModelMap X (homComplex (R := X.sheaf) L
          ((schemeHomKInjectiveResolution X).obj M)) L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X _ L M (𝟙 _)) ≫
        schemeHomResolutionInverse X M
    ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
        (b.hom.op, c.inv) ⊗ₘ 𝟙 (DerivedCategory.Q.obj L)) ≫ E L M =
      (𝟙 _ ⊗ₘ b.hom) ≫ E L' M' ≫ c.inv := by
  let := schemeDerivedTensorMonoidal X
  exact evaluation_naturality_of_components
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf)
    _ _ _ _ b.hom c.inv _ _ _
    (tensorHomEvaluation_precomposition X L L' M b)
    (tensorHomEvaluation_postcomposition X L' M M' c)

end AlgebraicGeometry
