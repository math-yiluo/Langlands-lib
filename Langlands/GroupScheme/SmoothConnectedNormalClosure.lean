import Langlands.GroupScheme.Absolute.UnipotentAllBorelsEnvelope
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.SchemeActionDominantOrbit
import Langlands.GroupScheme.StabilizerClosedSubgroup

/-! # Smooth connected normal closures and action stabilizers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- A normal subgroup functor containing the original image contains the full
conjugation image on all scheme tests. -/
theorem containsImage_conjugationMap_of_isNormal (F : SubgroupFunctor G)
    (hn : F.IsNormal) (j : H ⟶ G) (hj : range j ≤ F) :
    F.ContainsImage (conjugationMap j (𝟙 G)) := by
  intro T v
  have h := hn T (v ≫ fst G.X H.X) ((v ≫ snd G.X H.X) ≫ j.hom.hom)
    (by trivial) (hj T ⟨v ≫ snd G.X H.X, rfl⟩)
  simpa only [conjugationMap, MonObj.comp_mul, GrpObj.comp_inv,
    Grp.id_hom_hom, Category.comp_id, Category.assoc] using h

end SubgroupFunctor

variable {k : Type u} [Field k]
variable {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual generated closed envelope of all conjugates of the image of `j`,
with smooth connected geometry, normality and containment of the original image. -/
structure SmoothConnectedNormalClosure (j : H ⟶ G) extends
    GeneratedImage (SubgroupFunctor.conjugationMap j (𝟙 G)) where
  hasSmoothConnectedGeneration : toGeneratedImage.HasSmoothConnectedGeneration
  isNormal : (SubgroupFunctor.range inclusion).IsNormal
  contains : SubgroupFunctor.range j ≤ SubgroupFunctor.range inclusion

/-- A smooth connected affine group has a smooth connected normal closure of the
image of any smooth connected affine group, over every field. -/
theorem exists_smoothConnectedNormalClosure
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (j : H ⟶ G) : Nonempty (SmoothConnectedNormalClosure j) := by
  obtain ⟨hVAff, hVFin, -, hVInt⟩ := smoothConnectedAffineGeometry.2 k G H
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
  let f := SubgroupFunctor.conjugationMap j (𝟙 G)
  have hv₀ : (lift 1 1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X ⊗ H.X) ≫
      f = 1 := by
    simp only [f, SubgroupFunctor.lift_comp_conjugationMap, MonObj.one_comp,
      mul_one, inv_one]
  obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k G inferInstance
    inferInstance (G.X ⊗ H.X) hVAff hVFin hVInt _ f hv₀
  refine ⟨{ toGeneratedImage := D
            hasSmoothConnectedGeneration := hD
            isNormal := ?_
            contains := ?_ }⟩
  · intro T g x _ hx
    rw [D.represents.2] at hx ⊢
    have hst := AutomorphicAction.closedImageEnvelope_isStable
      (AutomorphicAction.conjugation (𝟙 G)) inferInstance
      (UnipotentAllBorelsEnvelope.leftTranslation G H.X) f
      (UnipotentAllBorelsEnvelope.conjugationMap_isEquivariant j) T g x hx
    simpa only [AutomorphicAction.conjugation_act, Grp.id_hom_hom,
      Category.comp_id] using hst
  · intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [D.represents.2]
    have hy := closedImageEnvelope_containsImage f T (lift 1 y)
    simpa only [f, SubgroupFunctor.lift_comp_conjugationMap,
      Grp.id_hom_hom, Category.comp_id, one_mul, inv_one, mul_one] using hy

/-- A chosen smooth connected normal closure; no canonical choice is asserted. -/
def smoothConnectedNormalClosure
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (j : H ⟶ G) : SmoothConnectedNormalClosure j :=
  Classical.choice (exists_smoothConnectedNormalClosure j)

namespace SmoothConnectedNormalClosure

variable {j : H ⟶ G} (D : SmoothConnectedNormalClosure j)

/-- Minimality in any supplied closed subgroup containing the whole conjugation image. -/
theorem range_le_of_containsImage
    {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ G)
    (hb : IsClosedSubgroup b)
    (hf : (SubgroupFunctor.range b).ContainsImage
      (SubgroupFunctor.conjugationMap j (𝟙 G))) :
    SubgroupFunctor.range D.inclusion ≤ SubgroupFunctor.range b :=
  D.toGeneratedImage.range_le b hb
    ((factorsThrough_iff_containsImage _ b).mpr hf)

/-- The normal closure is contained in every actual closed normal subgroup
containing the original image. -/
theorem range_le
    {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ G)
    (hb : IsClosedSubgroup b) (hn : (SubgroupFunctor.range b).IsNormal)
    (hj : SubgroupFunctor.range j ≤ SubgroupFunctor.range b) :
    SubgroupFunctor.range D.inclusion ≤ SubgroupFunctor.range b :=
  D.range_le_of_containsImage b hb
    (SubgroupFunctor.containsImage_conjugationMap_of_isNormal _ hn j hj)

end SmoothConnectedNormalClosure

namespace SchemeAction

variable {S : Scheme.{u}} {G H U : GroupScheme S} {X : Over S}
variable (a : SchemeAction G X)

/-- The full action kernel lies in the stabilizer of each rational section. -/
theorem kernel_le_stabilizer (x : 𝟙_ (Over S) ⟶ X) :
    a.kernel ≤ a.stabilizer x := by
  intro T g hg
  exact a.act_eq_of_mem_kernel hg (toUnit T ≫ x)

/-- Normality of the full action kernel puts all conjugates of a trivially acting
image in the stabilizer of every rational section. -/
theorem containsImage_conjugationMap_stabilizer
    (j : H ⟶ G) (hj : SubgroupFunctor.range j ≤ a.kernel)
    (x : 𝟙_ (Over S) ⟶ X) :
    (a.stabilizer x).ContainsImage (SubgroupFunctor.conjugationMap j (𝟙 G)) := by
  intro T v
  exact a.kernel_le_stabilizer x T
    (SubgroupFunctor.containsImage_conjugationMap_of_isNormal _
      a.kernel_isNormal j hj T v)

section Field

variable {k : Type u} [Field k]
variable {G H U : GroupScheme (Spec (CommRingCat.of k))}
  {X : Over (Spec (CommRingCat.of k))} (a : SchemeAction G X)

/-- A normal subgroup fixing a section with dominant orbit under a restricted
action lies in the full kernel of the ambient action. -/
theorem range_comp_le_kernel_of_dominant_orbit
    [Smooth H.X.hom] [IsReduced X.left] [LocallyOfFiniteType X.hom]
    [IsSeparated X.hom]
    (i : U ⟶ G) (j : H ⟶ U)
    (hn : (SubgroupFunctor.range j).IsNormal)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    (hx : ((a.restrict i).restrict j).IsFixed x)
    [IsDominant ((a.restrict i).orbitMap x).left]
    [QuasiCompact ((a.restrict i).orbitMap x).left] :
    SubgroupFunctor.range (j ≫ i) ≤ a.kernel := by
  have h := (a.restrict i).range_le_kernel_of_dominant_orbit j hn x hx
  intro T g hg
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  intro T' c z
  have hy := h T ⟨y, rfl⟩ T' c z
  change (a.restrict i).act (c ≫ (y ≫ j.hom.hom)) z = z at hy
  simpa only [restrict_act, Grp.comp_hom_hom, Category.assoc] using hy

/-- The smooth normal closure of a trivially acting image lies in any supplied
closed representative of a point stabilizer. The full kernel need not be represented. -/
theorem normalClosure_range_le_stabilizer
    {j : H ⟶ G} (D : SmoothConnectedNormalClosure j)
    (hj : SubgroupFunctor.range j ≤ a.kernel)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ G)
    (hb : IsClosedSubgroup b)
    (hrep : (a.stabilizer x).IsRepresentedBy b) :
    SubgroupFunctor.range D.inclusion ≤ SubgroupFunctor.range b := by
  apply D.range_le_of_containsImage b hb
  rw [hrep.2]
  exact a.containsImage_conjugationMap_stabilizer j hj x

end Field

end SchemeAction

end Langlands.GroupScheme
