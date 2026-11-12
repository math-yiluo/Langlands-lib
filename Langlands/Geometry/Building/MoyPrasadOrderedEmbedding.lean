import Langlands.Geometry.Building.KPMoyPrasadProductStatement
import Langlands.Geometry.Building.MoyPrasadRootSeparation
import Langlands.Geometry.Building.ChamberOrderedProductInjective
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof

/-! # Actual ordered Moy–Prasad products are embeddings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Both actual factors of every root block lie in its actual root group,
at arbitrary real depths and without a sign condition on those depths. -/
theorem filtrationBlock_subset_rootGroupPoints (x : D.Apartment)
    (f : characterLattice S → ℝ) (a : characterLattice S) :
    D.filtrationBlock x f a ⊆ rootGroupPoints i a := by
  rintro g ⟨v, hv, w, hw, rfl⟩
  refine Subgroup.mul_mem _ hv.1 ?_
  by_cases h2a : 2 • a ∈ relativeRoots i
  · rw [D.doubleFiltration_of_mem x a (f (2 • a)) h2a] at hw
    exact RelativeRoot.double_subgroup_le i a (Over.mk (𝟙 _)) hw.1
  · rw [D.doubleFiltration_of_not_mem x a (f (2 • a)) h2a] at hw
    rw [Subgroup.mem_bot.mp hw]
    exact Subgroup.one_mem _

/-- Restrict actual algebraic ordered root multiplication to the unchanged
blocks, for every real depth function and every complete primitive-root order. -/
theorem orderedFiltrationBlockProduct_injective
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) (f : characterLattice S → ℝ) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (ha : Function.Injective a)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    Function.Injective (D.orderedFiltrationBlockProduct x f a) := by
  let lift (v : ∀ j, D.filtrationBlock x f (a j)) :
      ∀ j, rootGroupPoints i (a j) := fun j =>
    ⟨v j, D.filtrationBlock_subset_rootGroupPoints x f (a j) (v j).property⟩
  have hinj := RelativeRoot.orderedRootSubgroupPoints_injective_of_statement
    RelativeRoot.dynamicRootOrderedProduct hG hi ν a ha hrange (Over.mk (𝟙 _))
  intro v w hvw
  have heq : lift v = lift w := hinj hvw
  funext j
  exact Subtype.ext (congrArg (fun z => (z j : rationalPoints G)) heq)

/-- The actual ordered block product is in its prescribed Dynamic unipotent
group. No covering or filtration-axiom premise is needed. -/
theorem orderedFiltrationBlockProduct_mem_dynamicUnipotent
    (x : D.Apartment) (f : characterLattice S → ℝ) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (hpos : ∀ j, 0 < latticePairing S (a j) ν)
    (v : ∀ j, D.filtrationBlock x f (a j)) :
    D.orderedFiltrationBlockProduct x f a v ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) :=
  orderedRootSubsetProduct_mem_dynamicUnipotent i ν a hpos
    (fun j => D.filtrationBlock x f (a j))
    (fun j => D.filtrationBlock_subset_rootGroupPoints x f (a j)) v

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} (Zf : P.CentralizerFiltration)
    (x : P.Apartment) (r : NNReal) (ν : cocharacterLattice P.S)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice P.S)
    (apos : Fin npos → characterLattice P.S)
    (haneg : Function.Injective aneg)
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-ν))
    (hapos : Function.Injective apos)
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i ν)

include ν haneg hrneg hapos hrpos in
/-- The original negative-block, centralizer-depth, positive-block product
is injective at every nonnegative depth, independently of covering. -/
theorem orderedMoyPrasadProduct_injective :
    Function.Injective (Zf.orderedMoyPrasadProduct x r aneg apos) := by
  have hn j : aneg j ∈ RelativeRoot.indivisiblePositiveRoots P.i (-ν) :=
    hrneg ▸ Set.mem_range_self j
  have hp j : apos j ∈ RelativeRoot.indivisiblePositiveRoots P.i ν :=
    hrpos ▸ Set.mem_range_self j
  apply unipotentTripleProduct_injective_of_maps P.i ν
    (P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) aneg)
    (fun z : Zf.filtration r => rationalPoints.map P.centralizer.j z)
    (P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) apos)
  · exact P.apartment.orderedFiltrationBlockProduct_injective
      P.isConnectedReductive P.isMaximalSplitTorus x _ (-ν) aneg haneg hrneg
  · intro z w hzw
    apply Subtype.ext
    have : Mono P.centralizer.j.hom.hom := P.centralizer.isRepresentedBy.1
    exact (cancel_mono P.centralizer.j.hom.hom).mp hzw
  · exact P.apartment.orderedFiltrationBlockProduct_injective
      P.isConnectedReductive P.isMaximalSplitTorus x _ ν apos hapos hrpos
  · exact P.apartment.orderedFiltrationBlockProduct_mem_dynamicUnipotent
      x _ (-ν) aneg (fun j => (hn j).2)
  · exact P.apartment.orderedFiltrationBlockProduct_mem_dynamicUnipotent
      x _ ν apos (fun j => (hp j).2)
  · intro z
    exact map_mem_centralizerPoints P.centralizer.isRepresentedBy z

/-- The original ordered Moy–Prasad product, with exactly its original
coordinates and underlying multiplication, packaged as an embedding. -/
def orderedMoyPrasadProductEmbedding :
    ((∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (aneg j)) ×
      Zf.filtration r ×
      (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (apos j))) ↪
        rationalPoints G where
  toFun := Zf.orderedMoyPrasadProduct x r aneg apos
  inj' := Zf.orderedMoyPrasadProduct_injective x r ν aneg apos haneg hrneg hapos hrpos

omit r in
include ν haneg hrneg hapos hrpos in
/-- For one fixed complete root ordering, positive-depth covering alone
now implies separation of the original Moy–Prasad family. -/
theorem iInf_moyPrasad_eq_bot_of_positive_cover
    (hcover : ∀ r : NNReal, 0 < r →
      Set.range (Zf.orderedMoyPrasadProduct x r aneg apos) =
        (Zf.moyPrasad x r : Set (rationalPoints G))) :
    ⨅ r, Zf.moyPrasad x r = ⊥ := by
  apply Zf.iInf_moyPrasad_eq_bot_of_ordered_cover x aneg apos
  · intro j
    exact (show aneg j ∈ RelativeRoot.indivisiblePositiveRoots P.i (-ν) from
      hrneg ▸ Set.mem_range_self j).1.1
  · intro j
    exact (show apos j ∈ RelativeRoot.indivisiblePositiveRoots P.i ν from
      hrpos ▸ Set.mem_range_self j).1.1
  · exact Zf.orderedMoyPrasadProduct_injective x 1 ν aneg apos haneg hrneg hapos hrpos
  · exact hcover

end Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration
