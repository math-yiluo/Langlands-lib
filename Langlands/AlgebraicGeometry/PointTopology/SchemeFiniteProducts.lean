import Langlands.AlgebraicGeometry.PointTopology.SchemeProducts
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! # Finite products of actual scheme point spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S]

/-- Actual relative points with their independently constructed final topologies. -/
def schemePointTopCatFunctor : Over (Spec (CommRingCat.of R)) ⥤ TopCat.{u} where
  obj X := @TopCat.of (RingPoint R X S) (schemePointTopology R X S)
  map {X Y} f := by
    let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
    let : TopologicalSpace (RingPoint R Y S) := schemePointTopology R Y S
    exact TopCat.ofHom ⟨fun p => p ≫ f, schemePointContinuity_proof R S _ _ f⟩
  map_id X := by
    apply TopCat.ext
    intro p
    exact Category.comp_id p
  map_comp f g := by
    apply TopCat.ext
    intro p
    exact (Category.assoc p f g).symm

/-- A terminal scheme has exactly one relative point and hence a terminal point space. -/
def schemePointTopCatIsTerminal
    (X : Over (Spec (CommRingCat.of R))) (hX : IsTerminal X) :
    IsTerminal ((schemePointTopCatFunctor R S).obj X) := by
  let : TopologicalSpace (RingPoint R X S) := schemePointTopology R X S
  let : TopologicalSpace (ringTest R S ⟶ X) := schemePointTopology R X S
  apply IsTerminal.ofUniqueHom
    (fun _ => TopCat.ofHom
      ⟨fun _ => (hX.from (ringTest R S) : RingPoint R X S), continuous_const⟩)
  intro Y f
  apply TopCat.ext
  intro p
  exact hX.hom_ext _ _

instance schemePointTopCatPreservesTerminal :
    PreservesLimit (Functor.empty.{0} (Over (Spec (CommRingCat.of R))))
      (schemePointTopCatFunctor R S) := by
  apply preservesLimit_of_preserves_limit_cone
    (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
  exact (isLimitMapConeEmptyConeEquiv _ _).symm
    (schemePointTopCatIsTerminal R S _ Over.mkIdTerminal)

/-- The published binary point homeomorphism gives preservation of binary products. -/
instance schemePointTopCatPreservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) (schemePointTopCatFunctor R S) := by
  let F := schemePointTopCatFunctor R S
  have hpair (X Y : Over (Spec (CommRingCat.of R))) : PreservesLimit (pair X Y) F := by
    apply preservesLimit_of_preserves_limit_cone (tensorProductIsBinaryProduct X Y)
    refine (isLimitMapConeBinaryFanEquiv F (fst X Y) (snd X Y)).symm ?_
    let H := schemeProductPointHomeomorph R S X Y
    have he : BinaryFan.mk (F.map (fst X Y)) (F.map (snd X Y)) ≅
        TopCat.prodBinaryFan (F.obj X) (F.obj Y) :=
      Cone.ext (TopCat.isoOfHomeo H) (by
        rintro ⟨j⟩
        cases j <;> ext p <;> rfl)
    exact IsLimit.ofIsoLimit (TopCat.prodBinaryFanIsLimit (F.obj X) (F.obj Y)) he.symm
  refine ⟨fun {K} => ?_⟩
  let := hpair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
  exact preservesLimit_of_iso_diagram F (diagramIsoPair K).symm

/-- Local-value-ring points preserve finite products for their canonical topologies. -/
instance schemePointTopCatPreservesFiniteProducts :
    PreservesFiniteProducts (schemePointTopCatFunctor R S) := by
  let := preservesLimitsOfShape_pempty_of_preservesTerminal (schemePointTopCatFunctor R S)
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal _

variable {ι : Type u} [Finite ι]

/-- The actual projection fan remains limiting in topological spaces. -/
def schemePointTopCatFanIsLimit
    (X : ι → Over (Spec (CommRingCat.of R))) (c : Fan X) (hc : IsLimit c) :
    IsLimit (Fan.mk ((schemePointTopCatFunctor R S).obj c.pt)
      (fun i => (schemePointTopCatFunctor R S).map (c.proj i))) :=
  isLimitFanMkObjOfIsLimit (schemePointTopCatFunctor R S) X c.proj
    (IsLimit.ofIsoLimit hc (Fan.ext (Iso.refl _) (by intro i; simp)))

/-- Any actual finite limiting fan induces the canonical product homeomorphism
on independently topologized relative point spaces. -/
def schemeFiniteProductPointHomeomorph
    (X : ι → Over (Spec (CommRingCat.of R))) (c : Fan X) (hc : IsLimit c) :
    letI : ∀ i, TopologicalSpace (RingPoint R (X i) S) :=
      fun i => schemePointTopology R (X i) S
    letI : TopologicalSpace (RingPoint R c.pt S) := schemePointTopology R c.pt S
    RingPoint R c.pt S ≃ₜ (∀ i, RingPoint R (X i) S) := by
  let F := schemePointTopCatFunctor R S
  exact TopCat.homeoOfIso
    (IsLimit.conePointUniqueUpToIso (schemePointTopCatFanIsLimit R S X c hc)
      (TopCat.piFanIsLimit (fun i => F.obj (X i))))

/-- The finite-product homeomorphism uses exactly the given scheme projections. -/
@[simp]
theorem schemeFiniteProductPointHomeomorph_apply
    (X : ι → Over (Spec (CommRingCat.of R))) (c : Fan X) (hc : IsLimit c)
    (p : RingPoint R c.pt S) (i : ι) :
    schemeFiniteProductPointHomeomorph R S X c hc p i = p ≫ c.proj i := by
  let F := schemePointTopCatFunctor R S
  have h := ConcreteCategory.congr_hom
    (IsLimit.conePointUniqueUpToIso_hom_comp (schemePointTopCatFanIsLimit R S X c hc)
      (TopCat.piFanIsLimit (fun i => F.obj (X i))) ⟨i⟩) p
  exact h

end Langlands.AlgebraicGeometry.PointTopology
