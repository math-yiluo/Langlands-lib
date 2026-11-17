import Langlands.GroupScheme.Torus.MultiplicativeTypeAtlas
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.Descent.FppfEffectivity
import Langlands.GroupScheme.Descent.FppfHomDescent
import Langlands.GroupScheme.Descent.FppfReflection

/-! # The descended torus of a diagonalizable atlas and the embedding into it -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeMultiplicativeType

open Descent FreeCharacterCover

/-- `diagonalizableBaseChangeIso` is compatible with iterated base change. -/
theorem baseChange_map_diagonalizableBaseChangeIso {X S V : Scheme.{u}} (P : X ⟶ S)
    (a : V ⟶ X) (l : V ⟶ S) (h : a ≫ P = l) (Λ : Type u) [AddCommGroup Λ] :
    (GroupScheme.baseChange a).map (diagonalizableBaseChangeIso P Λ).hom ≫
        (diagonalizableBaseChangeIso a Λ).hom =
      (pullbackComparison P a l h (diagonalizable S Λ)).hom ≫
        (diagonalizableBaseChangeIso l Λ).hom :=
  pullbackComparison_tower' (Gm.toSpecZ S) P (Gm.toSpecZ X) (toSpecZ_comp P) a l
    (Gm.toSpecZ V) h (toSpecZ_comp l) (toSpecZ_comp a)

/-- The canonical overlap of a pulled-back group, evaluated along any test map. -/
theorem pullHom_canonicalOverlap {B X V : Scheme.{u}} (p : X ⟶ B) (C : GroupScheme B)
    (q : V ⟶ Overlap p) {a b : V ⟶ X} (ha : q ≫ fst p = a) (hb : q ≫ snd p = b)
    (l : V ⟶ B) (hal : a ≫ p = l) (hbl : b ≫ p = l) :
    pullHom q ha hb (canonicalOverlap p C).hom =
      (pullbackComparison p a l hal C).hom ≫ (pullbackComparison p b l hbl C).inv := by
  have hl : q ≫ (fst p ≫ p) = l := by rw [← Category.assoc, ha, hal]
  have h := pullHom_conj_pullbackComparison p (rfl : fst p ≫ p = fst p ≫ p)
    (pullback.condition.symm : snd p ≫ p = fst p ≫ p) q ha hb hl hl
    (canonicalOverlap p C).hom
  have e : (pullbackComparison p (fst p) (fst p ≫ p) rfl C).inv ≫
      (canonicalOverlap p C).hom ≫
        (pullbackComparison p (snd p) (fst p ≫ p) pullback.condition.symm C).hom = 𝟙 _ := by
    simp [canonicalOverlap]
  rw [e, pullHom_id] at h
  calc pullHom q ha hb (canonicalOverlap p C).hom
      = (pullbackComparison p a l hal C).hom ≫ ((pullbackComparison p a l hal C).inv ≫
          pullHom q ha hb (canonicalOverlap p C).hom ≫
            (pullbackComparison p b l hbl C).hom) ≫ (pullbackComparison p b l hbl C).inv := by
        simp
    _ = _ := by rw [← h]; simp

namespace DiagonalizableAtlas

variable {S V W : Scheme.{u}} {H : GroupScheme S} (A : DiagonalizableAtlas H)

/-! ### The embedding over the atlas scheme -/

/-- The original group pulled back to the atlas scheme. -/
abbrev pulled : GroupScheme A.space := (GroupScheme.baseChange A.projection).obj H

/-- The trivialization of the pulled-back group on a chart, written over the atlas scheme. -/
def pulledChart (i : A.I) :
    (GroupScheme.baseChange (A.inclusion i)).obj A.pulled ≅
      (GroupScheme.baseChange (A.inclusion i)).obj
        ((GroupScheme.baseChange A.projection).obj (diagonalizable S (A.Λ i))) :=
  pullbackComparison A.projection (A.inclusion i) (A.f i) (A.inclusion_projection i) H ≪≫
    A.triv i ≪≫ (pullbackComparison A.projection (A.inclusion i) (A.f i)
      (A.inclusion_projection i) (diagonalizable S (A.Λ i))).symm

/-- The map `D_space(Λ i) ⟶ D_space(F(Λ i))` induced by the projection of the free cover,
precomposed with the comparison `P^* D_S(Λ i) ≅ D_space(Λ i)`. -/
def coverMap (i : A.I) :
    (GroupScheme.baseChange A.projection).obj (diagonalizable S (A.Λ i)) ⟶
      diagonalizable A.space (Cover (A.Λ i)) :=
  (diagonalizableBaseChangeIso A.projection (A.Λ i)).hom ≫
    diagonalizableMap A.space (proj (A.Λ i))

/-- The embedding on one chart. -/
def embeddingComponent (i : A.I) :
    (GroupScheme.baseChange (A.inclusion i)).obj A.pulled ⟶
      (GroupScheme.baseChange (A.inclusion i)).obj A.group :=
  (A.pulledChart i).hom ≫ (GroupScheme.baseChange (A.inclusion i)).map (A.coverMap i) ≫
    (A.groupChart i).inv

/-- The embedding of the pulled-back group into the glued free-cover group. -/
def embedding : A.pulled ⟶ A.group :=
  DisjointComponents.groupHom A.inclusion A.embeddingComponent

theorem baseChange_map_embedding (i : A.I) :
    (GroupScheme.baseChange (A.inclusion i)).map A.embedding = A.embeddingComponent i :=
  DisjointComponents.map_groupHom A.inclusion A.embeddingComponent i

/-- On every chart coordinate, the embedding is `D(proj)` in the chart trivializations. -/
theorem embedding_on_chart (i : A.I) (x : V ⟶ A.Z i) (a : V ⟶ A.space)
    (hx : x ≫ A.inclusion i = a) (l : V ⟶ S) (hxl : x ≫ A.f i = l) :
    (GroupScheme.baseChange a).map A.embedding =
      (pullbackComparison A.projection a l
          (by rw [← hx, Category.assoc, inclusion_projection, hxl]) H).hom ≫
        (A.chartTriv i x l hxl).hom ≫ diagonalizableMap V (proj (A.Λ i)) ≫
          (diagonalizableBaseChangeIso a (Cover (A.Λ i))).inv ≫ (A.coord i x a hx).inv := by
  have hal : a ≫ A.projection = l := by rw [← hx, Category.assoc, inclusion_projection, hxl]
  have h1 : (GroupScheme.baseChange a).map A.embedding =
      pullHom x hx hx (A.embeddingComponent i) := by
    rw [← pullHom_map x (A.inclusion i) a hx A.embedding, baseChange_map_embedding]
  have e1 : (pullbackComparison A.projection (A.inclusion i) (A.f i)
        (A.inclusion_projection i) H).inv ≫ (A.pulledChart i).hom ≫
      (pullbackComparison A.projection (A.inclusion i) (A.f i)
        (A.inclusion_projection i) (diagonalizable S (A.Λ i))).hom = (A.triv i).hom := by
    simp [pulledChart]
  have h2 : pullHom x hx hx (A.pulledChart i).hom =
      (pullbackComparison A.projection a l hal H).hom ≫ (pullIso x hxl hxl (A.triv i)).hom ≫
        (pullbackComparison A.projection a l hal (diagonalizable S (A.Λ i))).inv := by
    have h := pullHom_conj_pullbackComparison A.projection (A.inclusion_projection i)
      (A.inclusion_projection i) x hx hx hxl hxl (A.pulledChart i).hom
    rw [e1] at h
    rw [pullIso_hom, h]
    simp
  have h3 : (pullbackComparison A.projection a l hal (diagonalizable S (A.Λ i))).inv ≫
      (GroupScheme.baseChange a).map (diagonalizableBaseChangeIso A.projection (A.Λ i)).hom =
        (diagonalizableBaseChangeIso l (A.Λ i)).hom ≫
          (diagonalizableBaseChangeIso a (A.Λ i)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc,
      ← baseChange_map_diagonalizableBaseChangeIso A.projection a l hal]
    simp
  rw [h1, embeddingComponent, pullHom_comp x hx hx hx, pullHom_comp x hx hx hx, h2,
    pullHom_map, pullHom_inv, coverMap, Functor.map_comp, baseChange_map_diagonalizableMap]
  simp only [chartTriv, coord, Iso.trans_hom, Category.assoc]
  rw [reassoc_of% h3]
  simp

/-- The embedding is compatible with the canonical datum and the glued datum. -/
theorem embedding_compatible :
    Compatible (canonicalDatum A.projection H) A.datum A.embedding := by
  show (GroupScheme.baseChange (fst A.projection)).map A.embedding ≫ A.overlap.hom =
    (canonicalOverlap A.projection H).hom ≫
      (GroupScheme.baseChange (snd A.projection)).map A.embedding
  apply A.hom_ext_on_charts (fst A.projection) (snd A.projection)
  intro V i j q x y hx hy
  have hxl : x ≫ A.f i = q ≫ fst A.projection ≫ A.projection :=
    A.coordinate_base _ _ rfl i q x hx _ rfl
  have hyl : y ≫ A.f j = q ≫ fst A.projection ≫ A.projection :=
    A.coordinate_base (snd A.projection) (fst A.projection ≫ A.projection)
      pullback.condition.symm j q y hy _ rfl
  have hov : pullHom q rfl rfl A.overlap.hom =
      (A.chartValue i j x y _ _ hx hy _ hxl hyl).hom := by
    rw [← pullIso_hom, A.overlap_on_charts q i j x y rfl rfl hx hy _ hxl hyl]
  rw [pullHom_comp q rfl rfl rfl, pullHom_comp q rfl rfl rfl, pullHom_map, pullHom_map, hov,
    pullHom_canonicalOverlap A.projection H q rfl rfl _
      (by rw [← hx, Category.assoc, inclusion_projection, hxl])
      (by rw [← hy, Category.assoc, inclusion_projection, hyl]),
    A.embedding_on_chart i x _ hx _ hxl, A.embedding_on_chart j y _ hy _ hyl]
  have hc := A.lift_comm i j x y _ hxl hyl
  simp only [comparison, Iso.trans_hom, Iso.symm_hom, Category.assoc] at hc
  simp only [chartValue, dconj, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← reassoc_of% hc]
  simp

/-! ### Closedness of the embedding -/

/-- Closedness of a homomorphism over the atlas scheme can be checked on the charts. -/
theorem isClosedSubgroup_of_inclusions {G K : GroupScheme A.space} (φ : G ⟶ K)
    (h : ∀ i, IsClosedSubgroup ((GroupScheme.baseChange (A.inclusion i)).map φ)) :
    IsClosedSubgroup φ := by
  change IsClosedImmersion φ.hom.hom.left
  apply IsZariskiLocalAtTarget.of_openCover ((sigmaOpenCover A.Z).pullback₁ K.X.hom)
  intro i
  have hP := (baseChange_map_isPullback (A.inclusion i) φ).flip
  have hi : IsClosedImmersion ((GroupScheme.baseChange (A.inclusion i)).map φ).hom.hom.left :=
    h i
  change IsClosedImmersion (pullback.snd φ.hom.hom.left (pullback.fst K.X.hom (Sigma.ι A.Z i)))
  rw [← hP.isoPullback_hom_snd] at hi
  rwa [MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)] at hi

private theorem isIso_left_of_iso {X : Scheme.{u}} {G K : GroupScheme X} (e : G ≅ K) :
    IsIso e.hom.hom.hom.left :=
  (inferInstance : IsIso ((Over.forget X).mapIso ((Grp.forget _).mapIso e)).hom)

private theorem isIso_left_inv_of_iso {X : Scheme.{u}} {G K : GroupScheme X} (e : G ≅ K) :
    IsIso e.inv.hom.hom.left :=
  isIso_left_of_iso e.symm

theorem isClosedSubgroup_embeddingComponent (i : A.I) :
    IsClosedSubgroup (A.embeddingComponent i) := by
  have h1 : IsClosedSubgroup (A.coverMap i) := by
    have : IsClosedImmersion (diagonalizableMap A.space (proj (A.Λ i))).hom.hom.left :=
      isClosedSubgroup_diagonalizableMap_proj A.space (A.Λ i)
    have := isIso_left_of_iso (diagonalizableBaseChangeIso A.projection (A.Λ i))
    change IsClosedImmersion ((diagonalizableBaseChangeIso A.projection (A.Λ i)).hom.hom.hom.left ≫
      (diagonalizableMap A.space (proj (A.Λ i))).hom.hom.left)
    infer_instance
  have h2 : IsClosedImmersion
      ((GroupScheme.baseChange (A.inclusion i)).map (A.coverMap i)).hom.hom.left :=
    IsClosedSubgroup.baseChange (A.inclusion i) h1
  have := isIso_left_of_iso (A.pulledChart i)
  have := isIso_left_inv_of_iso (A.groupChart i)
  change IsClosedImmersion ((A.pulledChart i).hom.hom.hom.left ≫
    ((GroupScheme.baseChange (A.inclusion i)).map (A.coverMap i)).hom.hom.left ≫
      (A.groupChart i).inv.hom.hom.left)
  infer_instance

theorem isClosedSubgroup_embedding : IsClosedSubgroup A.embedding :=
  A.isClosedSubgroup_of_inclusions _ fun i => by
    rw [baseChange_map_embedding]
    exact A.isClosedSubgroup_embeddingComponent i

/-! ### Descent to the base -/

instance group_isAffineHom : IsAffineHom A.group.X.hom := by
  have : ∀ i, IsAffineHom (A.model i).X.hom := fun i => by
    have : IsAffineHom (Diagonalizable.groupScheme
        (CommRingCat.of (ULift.{u} ℤ)) (Cover (A.Λ i))).X.hom := Diagonalizable.isAffineHom _ _
    change IsAffineHom (pullback.snd _ _)
    exact MorphismProperty.pullback_snd _ _ ‹_›
  unfold group
  infer_instance

variable [Flat A.projection] [LocallyOfFinitePresentation A.projection]
  [Surjective A.projection]

/-- The descended torus. -/
def torus : GroupScheme S := A.datum.fppfSolution.obj

/-- The embedding of the original group into the descended torus. -/
def torusEmbedding : H ⟶ A.torus :=
  Solution.descendHomOfFppf (canonicalSolution A.projection H) A.datum.fppfSolution
    A.embedding A.embedding_compatible

theorem baseChange_map_torusEmbedding :
    (GroupScheme.baseChange A.projection).map A.torusEmbedding =
      A.embedding ≫ A.datum.fppfSolution.iso.inv := by
  have h := Solution.baseChange_descendHomOfFppf (canonicalSolution A.projection H)
    A.datum.fppfSolution A.embedding A.embedding_compatible
  rw [← Iso.eq_comp_inv] at h
  unfold torusEmbedding torus
  simpa [canonicalSolution] using h

theorem isClosedSubgroup_torusEmbedding : IsClosedSubgroup A.torusEmbedding := by
  apply IsClosedSubgroup.of_baseChange_of_fppf A.projection
  rw [baseChange_map_torusEmbedding]
  have : IsClosedImmersion A.embedding.hom.hom.left := A.isClosedSubgroup_embedding
  have := isIso_left_inv_of_iso A.datum.fppfSolution.iso
  change IsClosedImmersion (A.embedding.hom.hom.left ≫
    A.datum.fppfSolution.iso.inv.hom.hom.left)
  infer_instance

/-- The descended torus is a split torus over every chart. -/
theorem isSplitTorus_baseChange_torus (i : A.I) :
    IsSplitTorus ((GroupScheme.baseChange (A.f i)).obj A.torus) :=
  IsSplitTorus.of_iso
    ((pullbackComparison A.projection (A.inclusion i) (A.f i) (A.inclusion_projection i)
        A.torus).symm ≪≫
      (GroupScheme.baseChange (A.inclusion i)).mapIso A.datum.fppfSolution.iso ≪≫
        DisjointGroupGluing.componentIso A.inclusion A.model i)
    (isSplitTorus_diagonalizable_cover (A.Z i) (A.Λ i))

end DiagonalizableAtlas

end Langlands.GroupScheme.RelativeMultiplicativeType
