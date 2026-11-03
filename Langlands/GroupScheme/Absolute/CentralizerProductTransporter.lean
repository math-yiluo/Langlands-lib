import Langlands.GroupScheme.Absolute.ConjugationIntoLocus
import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker

/-! # The centralizer product and its closed inverse-conjugation locus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralizerProduct

variable {S : Scheme.{u}} {M B G : GroupScheme S}

/-- Actual multiplication of the images of the two group schemes. -/
def productHom (j : M ⟶ G) (b : B ⟶ G) : M.X ⊗ B.X ⟶ G.X :=
  SubgroupFunctor.cellMultiplication j b

theorem lift_productHom (j : M ⟶ G) (b : B ⟶ G) {V : Over S}
    (m : V ⟶ M.X) (x : V ⟶ B.X) :
    lift m x ≫ productHom j b = (m ≫ j.hom.hom) * (x ≫ b.hom.hom) := by
  simp only [productHom, SubgroupFunctor.cellMultiplication, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]

/-- Every product of a centralizing point and a point of the containing subgroup conjugates
the whole cocharacter into that subgroup, after every refinement of every test scheme. -/
theorem product_holds (χ : (Gm S).toGrp ⟶ G) (j : M ⟶ G)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j) (b : B ⟶ G)
    (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b) :
    ConjugationInto.Holds χ b (productHom j b) := by
  intro V a t
  let c : V ⟶ G.X := (a ≫ fst M.X B.X) ≫ j.hom.hom
  let d : V ⟶ G.X := (a ≫ snd M.X B.X) ≫ b.hom.hom
  have hc : c ∈ (torusCentralizer χ).carrier V := by
    rw [torusCentralizer_gm_eq_dynamicCentralizer, ← hrep.2]
    exact SubgroupFunctor.mem_range.mpr ⟨a ≫ fst M.X B.X, rfl⟩
  have hct : Commute c (t ≫ χ.hom.hom) := by
    simpa only [Category.id_comp] using hc V (𝟙 V) t
  have hd : d ∈ (SubgroupFunctor.range b).carrier V :=
    SubgroupFunctor.mem_range.mpr ⟨a ≫ snd M.X B.X, rfl⟩
  have ht : t ≫ χ.hom.hom ∈ (SubgroupFunctor.range b).carrier V :=
    hχ V (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩)
  have he : a ≫ productHom j b = c * d := by
    simp only [productHom, SubgroupFunctor.cellMultiplication, MonObj.comp_mul, Category.assoc, c, d]
  rw [he]
  have heq : (c * d)⁻¹ * (t ≫ χ.hom.hom) * (c * d) =
      d⁻¹ * (t ≫ χ.hom.hom) * d := by
    calc
      (c * d)⁻¹ * (t ≫ χ.hom.hom) * (c * d) =
          d⁻¹ * (c⁻¹ * (t ≫ χ.hom.hom) * c) * d := by
        simp only [mul_inv_rev, mul_assoc]
      _ = d⁻¹ * (t ≫ χ.hom.hom) * d := by
        rw [hct.inv_left.eq, inv_mul_cancel_right]
  rw [heq]
  exact ((SubgroupFunctor.range b).carrier V).mul_mem
    (((SubgroupFunctor.range b).carrier V).mul_mem
      (((SubgroupFunctor.range b).carrier V).inv_mem hd) ht) hd

section Field

variable {k : Type u} [Field k]
variable {M B G : GroupScheme (Spec (CommRingCat.of k))}

local instance instCentralizerProductTransporter1 : IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom :=
  isSplitTorus_gm.isAffineHom

/-- The centralizer product factors through the actual closed inverse-conjugation locus. -/
theorem product_factors (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : M ⟶ G)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j) (b : B ⟶ G)
    (hb : IsClosedSubgroup b) (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b) :
    ∃ p : M.X ⊗ B.X ⟶ ConjugationInto.locus χ b hb,
      p ≫ ConjugationInto.inclusion χ b hb = productHom j b :=
  (ConjugationInto.factors_inclusion_iff χ b hb _).mpr (product_holds χ j hrep b hχ)

/-- The vanishing ideal of the topological closure of the actual multiplication image. -/
def closureIdeal (j : M ⟶ G) (b : B ⟶ G) : G.X.left.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure (Set.range (productHom j b).left))

/-- The reduced closed subscheme on the closure of the multiplication image. -/
def imageClosure (j : M ⟶ G) (b : B ⟶ G) : Over (Spec (CommRingCat.of k)) :=
  Over.mk ((closureIdeal j b).subschemeι ≫ G.X.hom)

def closureInclusion (j : M ⟶ G) (b : B ⟶ G) : imageClosure j b ⟶ G.X :=
  Over.homMk (closureIdeal j b).subschemeι

theorem closureInclusion_isClosedImmersion (j : M ⟶ G) (b : B ⟶ G) :
    IsClosedImmersion (closureInclusion j b).left := by
  change IsClosedImmersion (closureIdeal j b).subschemeι
  infer_instance

theorem imageClosure_isReduced (j : M ⟶ G) (b : B ⟶ G) :
    IsReduced (imageClosure j b).left :=
  (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker _).1

theorem range_closureInclusion (j : M ⟶ G) (b : B ⟶ G) :
    Set.range (closureInclusion j b).left = _root_.closure (Set.range (productHom j b).left) := by
  change Set.range (closureIdeal j b).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι (closureIdeal j b)]
  simp only [closureIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_closure]

/-- A closed subscheme through which the product factors also contains the reduced closure. -/
theorem closure_factors_of_product_factors {Z : Over (Spec (CommRingCat.of k))}
    (j : M ⟶ G) (b : B ⟶ G) (i : Z ⟶ G.X) [IsClosedImmersion i.left]
    (hp : ∃ p : M.X ⊗ B.X ⟶ Z, p ≫ i = productHom j b) :
    ∃ q : imageClosure j b ⟶ Z, q ≫ i = closureInclusion j b := by
  obtain ⟨p, hp⟩ := hp
  have hrange : Set.range (productHom j b).left ⊆ Set.range i.left := by
    rw [← hp]
    rintro _ ⟨x, rfl⟩
    exact ⟨p.left x, rfl⟩
  have hclosed : IsClosed (Set.range i.left) := i.left.isClosedEmbedding.isClosed_range
  have hker : i.left.ker ≤ (closureIdeal j b).subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    apply Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
    change _root_.closure (Set.range (productHom j b).left) ⊆ i.left.ker.support
    rw [Scheme.Hom.support_ker, hclosed.closure_eq]
    exact closure_minimal hrange hclosed
  let ql := IsClosedImmersion.lift i.left (closureIdeal j b).subschemeι hker
  have hq : ql ≫ i.left = (closureIdeal j b).subschemeι :=
    IsClosedImmersion.lift_fac _ _ _
  refine ⟨Over.homMk ql ?_, Over.OverMorphism.ext hq⟩
  change ql ≫ Z.hom = (closureIdeal j b).subschemeι ≫ G.X.hom
  rw [← Over.w i, ← Category.assoc, hq]

/-- The reduced image closure still conjugates the cocharacter into the containing subgroup. -/
theorem closure_factors (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : M ⟶ G)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j) (b : B ⟶ G)
    (hb : IsClosedSubgroup b) (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b) :
    ∃ q : imageClosure j b ⟶ ConjugationInto.locus χ b hb,
      q ≫ ConjugationInto.inclusion χ b hb = closureInclusion j b := by
  let : IsClosedImmersion (ConjugationInto.inclusion χ b hb).left :=
    ConjugationInto.inclusion_isClosedImmersion χ b hb
  exact closure_factors_of_product_factors j b _ (product_factors χ j hrep b hb hχ)

theorem closure_holds (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : M ⟶ G)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j) (b : B ⟶ G)
    (hb : IsClosedSubgroup b) (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b) :
    ConjugationInto.Holds χ b (closureInclusion j b) :=
  (ConjugationInto.factors_inclusion_iff χ b hb _).mp (closure_factors χ j hrep b hb hχ)

/-- A connected multiplication source has connected reduced image closure. -/
theorem imageClosure_connected_of_product (j : M ⟶ G) (b : B ⟶ G)
    [ConnectedSpace (M.X ⊗ B.X).left] : ConnectedSpace (imageClosure j b).left := by
  have hc := (isConnected_range (productHom j b).left.continuous).closure
  change ConnectedSpace (closureIdeal j b).support
  apply Subtype.connectedSpace
  simpa only [closureIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    TopologicalSpace.Closeds.coe_closure] using hc

/-- Smooth connected affine factors over a field give a connected reduced product closure. -/
theorem imageClosure_connected (j : M ⟶ G) (b : B ⟶ G)
    [Smooth M.X.hom] [IsAffineHom M.X.hom] [ConnectedSpace M.X.left]
    [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left] :
    ConnectedSpace (imageClosure j b).left := by
  let : GeometricallyConnected B.X.hom := B.geometricallyConnected_of_connected
  let : ConnectedSpace (M.X ⊗ B.X).left := by
    change ConnectedSpace ↥(pullback M.X.hom B.X.hom)
    infer_instance
  exact imageClosure_connected_of_product j b

end Field

end Langlands.GroupScheme.CentralizerProduct
