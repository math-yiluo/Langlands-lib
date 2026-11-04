import Langlands.GroupScheme.Chevalley.RepresentationExtension

/-! # Ambient representation subquotients for actual affine group schemes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G H J : GroupScheme (Spec (CommRingCat.of k))}

/-- Actual affine-test intertwiners commute with restriction. -/
theorem Intertwines.restrict
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
    {C : Matrix m n k} (hC : Intertwines ρ σ C) (f : H ⟶ G) :
    Intertwines (ρ.restrict f) (σ.restrict f) C := by
  intro A x
  exact hC A (x ≫ f.hom.hom)

/-- Restriction preserves actual representation subquotient witnesses. -/
theorem IsSubquotientOf.restrict {n m : ℕ}
    {σ : MatrixRepresentation G (Fin n)} {ρ : MatrixRepresentation G (Fin m)}
    (h : IsSubquotientOf σ ρ) (f : H ⟶ G) :
    IsSubquotientOf (σ.restrict f) (ρ.restrict f) := by
  obtain ⟨r, τ, C, D, hC, hi, hD, hs⟩ := h
  exact ⟨r, τ.restrict f, C, D, hC.restrict f, hi, hD.restrict f, hs⟩

/-- Every finite coordinate representation of the source is an actual
subquotient of a restricted finite coordinate representation of the target. -/
def HasAmbientSubquotients (f : H ⟶ G) : Prop :=
  ∀ (n : ℕ) (σ : MatrixRepresentation H (Fin n)),
    ∃ (m : ℕ) (ρ : MatrixRepresentation G (Fin m)),
      IsSubquotientOf σ (ρ.restrict f)

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding MatrixRepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Every actual representation of a closed subgroup of an affine group over
a field is a subquotient of a restricted actual ambient representation. -/
theorem hasAmbientSubquotients_of_isClosedSubgroup
    [IsAffineHom G.X.hom] (i : H ⟶ G) (hc : IsClosedSubgroup i) :
    HasAmbientSubquotients i := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion i.hom.hom.left := hc
  have : IsAffine H.X.left := isAffine_of_isAffineHom i.hom.hom.left
  obtain ⟨⟨B⟩, ⟨jG⟩⟩ := (essImage_algSpec (G := G.X)).mpr inferInstance
  obtain ⟨⟨C⟩, ⟨jH⟩⟩ := (essImage_algSpec (G := H.X)).mpr inferInstance
  intro n σ
  obtain ⟨m, ρ, hρ⟩ := exists_corepresented_ambient_subquotient
    (corepresentableBy G jG) (corepresentableBy H jH) (affineMapNat i)
    (modelMap_isClosedSubgroup jG jH i hc) (σ.restrict (modelIso H jH).hom)
  have hmap : (modelIso H jH).inv ≫ modelMap jG jH i =
      i ≫ (modelIso G jG).inv := by
    apply Grp.hom_ext
    change (modelIso H jH).inv.hom.hom ≫ (modelMap jG jH i).hom.hom =
      i.hom.hom ≫ (modelIso G jG).inv.hom.hom
    rw [modelIso_inv_hom_hom jH, modelIso_inv_hom_hom jG,
      modelMap_hom_hom jG jH i]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨m, ρ.restrict (modelIso G jG).inv, ?_⟩
  have h := hρ.restrict (modelIso H jH).inv
  change IsSubquotientOf
    ((σ.restrict (modelIso H jH).hom).restrict (modelIso H jH).inv)
    ((ρ.restrict (modelMap jG jH i)).restrict (modelIso H jH).inv) at h
  simpa only [restrict_comp, Iso.inv_hom_id, restrict_id, hmap] using h

end Langlands.GroupScheme.Chevalley

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Representation-tested geometric semisimplicity reflects along a closed
subgroup inclusion into an actual affine group scheme. -/
theorem isSemisimpleElement_of_closed_subgroup [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hc : IsClosedSubgroup i) {X : lieKernel H k}
    (hX : IsSemisimpleElement G (targetMap i k X)) :
    IsSemisimpleElement H X :=
  MatrixRepresentation.isSemisimpleElement_of_subquotients i
    (Chevalley.hasAmbientSubquotients_of_isClosedSubgroup i hc) hX

/-- Closed subgroup inclusions into affine groups detect exactly the same
representation-tested geometric semisimple tangent elements. -/
theorem isSemisimpleElement_closed_subgroup_iff [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hc : IsClosedSubgroup i) (X : lieKernel H k) :
    IsSemisimpleElement H X ↔ IsSemisimpleElement G (targetMap i k X) :=
  ⟨fun hX => hX.map i, fun hX => isSemisimpleElement_of_closed_subgroup i hc hX⟩

end Langlands.GroupScheme.Lie
