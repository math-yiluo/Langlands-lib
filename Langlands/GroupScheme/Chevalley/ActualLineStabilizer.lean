import Langlands.GroupScheme.Chevalley.LineStabilizer
import Langlands.GroupScheme.AffineLinearEmbeddingProof

/-! # Line stabilizers for arbitrary actual affine group schemes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix Classical CategoryTheory.MonObj

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  {B C : CommAlgCat.{u} R}
  (jG : (algSpec R).obj (op B) ≅ G.X)
  (jH : (algSpec R).obj (op C) ≅ H.X) (i : H ⟶ G)

/-- Restrict a group-scheme homomorphism to affine tests. -/
def affineMapNat : H.affinePointFunctor ⟶ G.affinePointFunctor :=
  Functor.whiskerLeft (algSpec R).rightOp (pointsMap i)

/-- The homomorphism between the corepresented affine models. -/
def modelMap : model H jH ⟶ model G jG :=
  Corepresented.groupSchemeMap (corepresentableBy H jH) (corepresentableBy G jG)
    (affineMapNat i)

/-- The model homomorphism transports the original homomorphism on every test. -/
theorem modelMap_points_comp (T : Over (Spec R)) (x : T ⟶ (model H jH).X) :
    (x ≫ (modelMap jG jH i).hom.hom) ≫ jG.hom = (x ≫ jH.hom) ≫ i.hom.hom := by
  rw [comp_hom]
  erw [Corepresented.groupSchemeMap_points]
  change (algΓAlgSpecAdjunction R).unit.app T ≫
    (Corepresented.pointsEquiv H.affinePointFunctor (corepresentableBy H jH) T x ≫
      i.hom.hom) = _
  rw [← Category.assoc, ← comp_hom]

/-- The chosen group-scheme model comparison has the chosen underlying scheme map. -/
theorem modelIso_hom_hom : (modelIso G jG).hom.hom.hom = jG.hom := by
  have h := congrArg (fun a => (a.app (op (model G jG).X)).hom (𝟙 (model G jG).X))
    (yonedaGrpFullyFaithful.map_preimage
      (NatIso.ofComponents (fun T => (pointsMulEquiv G jG T.unop).toGrpIso)
        (fun f => by
          ext x
          change (f.unop ≫ x) ≫ jG.hom = f.unop ≫ x ≫ jG.hom
          exact Category.assoc _ _ _)).hom)
  change (𝟙 (model G jG).X) ≫ (modelIso G jG).hom.hom.hom =
    (𝟙 (model G jG).X) ≫ jG.hom at h
  simpa only [Category.id_comp] using h

/-- The inverse model comparison has the inverse underlying scheme map. -/
theorem modelIso_inv_hom_hom : (modelIso G jG).inv.hom.hom = jG.inv := by
  apply (cancel_mono jG.hom).mp
  rw [jG.inv_hom_id, ← modelIso_hom_hom jG]
  change ((modelIso G jG).inv ≫ (modelIso G jG).hom).hom.hom = (𝟙 G : G ⟶ G).hom.hom
  rw [Iso.inv_hom_id]

/-- The model homomorphism is the scheme conjugate of the original map. -/
theorem modelMap_hom_hom :
    (modelMap jG jH i).hom.hom = jH.hom ≫ i.hom.hom ≫ jG.inv := by
  apply (cancel_mono jG.hom).mp
  simpa only [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    modelMap_points_comp jG jH i (model H jH).X (𝟙 _)

/-- Closedness is preserved under the affine-model comparison. -/
theorem modelMap_isClosedSubgroup (hc : IsClosedSubgroup i) :
    IsClosedSubgroup (modelMap jG jH i) := by
  have : IsClosedImmersion i.hom.hom.left := hc
  have : IsIso jH.hom.left := inferInstanceAs (IsIso ((Over.forget _).map jH.hom))
  have : IsIso jG.inv.left := inferInstanceAs (IsIso ((Over.forget _).map jG.inv))
  change IsClosedImmersion (modelMap jG jH i).hom.hom.left
  rw [modelMap_hom_hom]
  change IsClosedImmersion (jH.hom.left ≫ i.hom.hom.left ≫ jG.inv.left)
  infer_instance

/-- Range membership is invariant under the chosen affine-model identifications. -/
theorem modelMap_mem_range_iff (T : Over (Spec R)) (x : T ⟶ (model G jG).X) :
    x ∈ (SubgroupFunctor.range (modelMap jG jH i)).carrier T ↔
      x ≫ jG.hom ∈ (SubgroupFunctor.range i).carrier T := by
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ≫ jH.hom, ?_⟩
    rw [← modelMap_points_comp, hy]
  · rintro ⟨y, hy⟩
    refine ⟨y ≫ jH.inv, ?_⟩
    apply (cancel_mono jG.hom).mp
    rw [modelMap_points_comp]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hy

/-- Every finite-type affine group over a field and every closed subgroup admit
an actual finite matrix representation with the subgroup as its coordinate-line
unit-scalar stabilizer on all relative scheme tests. -/
theorem exists_line_stabilizer
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G)
    (hc : IsClosedSubgroup i) :
    ∃ (n : ℕ) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1))),
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        x ∈ (SubgroupFunctor.range i).carrier T ↔
          ∃ u : Γ(T.left, ⊤)ˣ,
            (ρ.pointMatrix T x : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T.left, ⊤)) *ᵥ
                Pi.single j 1 =
              (u : Γ(T.left, ⊤)) • (Pi.single j (1 : Γ(T.left, ⊤)) :
                Fin (n + 1) → Γ(T.left, ⊤)) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion i.hom.hom.left := hc
  have : IsAffine H.X.left := isAffine_of_isAffineHom i.hom.hom.left
  obtain ⟨⟨B⟩, ⟨jG⟩⟩ := (essImage_algSpec (G := G.X)).mpr inferInstance
  obtain ⟨⟨C⟩, ⟨jH⟩⟩ := (essImage_algSpec (G := H.X)).mpr inferInstance
  have : Algebra.FiniteType (CommRingCat.of k) B := by
    have h : LocallyOfFiniteType ((algSpec (CommRingCat.of k)).obj (op B)).hom := by
      have : IsIso jG.hom.left := inferInstanceAs (IsIso ((Over.forget _).map jG.hom))
      rw [← Over.w jG.hom]
      exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
    exact RingHom.finiteType_algebraMap.mp
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType).mp h)
  obtain ⟨n, j, ρ, hρ⟩ := exists_corepresented_line_stabilizer_fin
    (corepresentableBy G jG) (corepresentableBy H jH) (affineMapNat i)
    (Field.toIsField (CommRingCat.of k)) (modelMap_isClosedSubgroup jG jH i hc)
  refine ⟨n, j, ρ.restrict (modelIso G jG).inv, ?_⟩
  intro T x
  rw [MatrixRepresentation.pointMatrix_restrict, ← hρ T]
  change x ∈ (SubgroupFunctor.range i).carrier T ↔
    x ≫ (modelIso G jG).inv.hom.hom ∈ (SubgroupFunctor.range (modelMap jG jH i)).carrier T
  rw [modelMap_mem_range_iff jG jH i, modelIso_inv_hom_hom jG]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Langlands.GroupScheme.Chevalley
