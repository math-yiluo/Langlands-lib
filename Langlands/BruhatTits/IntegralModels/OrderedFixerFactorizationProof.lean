import Langlands.BruhatTits.IntegralModels.OrderedFixerFactorizationStatement
import Langlands.Geometry.Building.GenericOppositeUnipotentFixer
import Langlands.Geometry.Building.UnramifiedZeroNormalizerComparison
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Proof of the ordered fixer factorization in the unramified open cell -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))} [IsAffineHom G.X.hom]

namespace OrderedFixerFactorizationProof

/-- The ordered product splits into the negative block, the torus slot and the positive
block. -/
theorem list_prod_ofFn_eq {M : Type*} [Monoid M] {nneg npos : ℕ}
    (h : Fin (nneg + (npos + 1)) → M) :
    (List.ofFn h).prod =
      (List.ofFn fun j : Fin nneg => h (Fin.castAdd (npos + 1) j)).prod *
        h (Fin.natAdd nneg 0) *
          (List.ofFn fun j : Fin npos => h (Fin.natAdd nneg j.succ)).prod := by
  rw [List.ofFn_add, List.prod_append, List.ofFn_succ, List.prod_cons, mul_assoc]
  rfl

variable {C : MaximalUnramified.BuildingData F G} {nneg npos : ℕ}
  (aneg : Fin nneg → relativeRoots C.i) (apos : Fin npos → relativeRoots C.i)

theorem orderedIntegralIndex_castAdd (j : Fin nneg) :
    TorusRootModelFamilyData.orderedIntegralIndex aneg apos (Fin.castAdd (npos + 1) j) =
      some (aneg j) := by
  simp [TorusRootModelFamilyData.orderedIntegralIndex]

theorem orderedIntegralIndex_natAdd_zero :
    TorusRootModelFamilyData.orderedIntegralIndex aneg apos
      (Fin.natAdd nneg (0 : Fin (npos + 1))) = none := by
  simp [TorusRootModelFamilyData.orderedIntegralIndex]

theorem orderedIntegralIndex_natAdd_succ (j : Fin npos) :
    TorusRootModelFamilyData.orderedIntegralIndex aneg apos (Fin.natAdd nneg j.succ) =
      some (apos j) := by
  simp [TorusRootModelFamilyData.orderedIntegralIndex]

/-- A point of the torus Iwahori subgroup `T(K)⁰` of a zero datum whose torus is the
centralizer of the maximal split torus maps to a normalizer point that acts trivially on
characters and fixes every apartment point. -/
theorem exists_normalizer_of_mem_torusIwahori (C : MaximalUnramified.BuildingData F G)
    (E : UnramifiedZeroDatum F G) (hrep : (torusCentralizer C.i).IsRepresentedBy E.i)
    {s : rationalPoints E.T.toGrp} (hs : s ∈ E.torusIwahori) :
    ∃ tn : normalizerPoints C.i, (tn : rationalPoints G) = rationalPoints.map E.i s ∧
      weylAction C.i tn = 1 ∧ ∀ x : C.Apartment, tn • x = x := by
  let cz := SubgroupFunctor.IsRepresentedBy.factorHom C.centralizer.isRepresentedBy E.i
    hrep.2.le
  have hcz : cz ≫ C.centralizer.j = E.i :=
    SubgroupFunctor.IsRepresentedBy.factorHom_comp C.centralizer.isRepresentedBy E.i hrep.2.le
  have hz : rationalPoints.map cz s ∈
      characterValuationKernel (MaximalUnramified.valuation F) C.centralizer.Z :=
    map_characterValuationKernel_le _ cz
      ⟨s, E.torusIwahori_le_integerCharacterValuationKernel hs, rfl⟩
  refine ⟨C.centralizer.toNormalizer (rationalPoints.map cz s), ?_,
    weylAction_centralizerToNormalizer _ _, fun x => C.isOmegaCompatible.smul_eq_self hz x⟩
  rw [CentralizerDatum.toNormalizer, coe_centralizerToNormalizer]
  simp only [rationalPoints.map_apply, ← hcz, Grp.comp_hom_hom, Category.assoc]

end OrderedFixerFactorizationProof

open OrderedFixerFactorizationProof in
/-- **The ordered fixer factorization in the unramified open cell.** For supplied building
data over the maximal unramified extension, a zero datum whose torus is the centralizer of the
maximal split torus, a generic cocharacter `ν` and injective complete enumerations of the
negative and positive indivisible roots, `OrderedFixerFactorization` holds for the order
negative roots, torus, positive roots, for all apartment subsets `Ω` and `Ω'`. -/
theorem unramifiedOrderedFixerFactorization :
    UnramifiedOrderedFixerFactorizationStatement.{u} := by
  intro F _ _ _ _ G _ C E hrep ν hν nneg npos aneg apos haneg hrneg hapos hrpos Ω Ω' _ _ h hh hmem
  have hG := C.isConnectedReductive
  have hi := C.isMaximalSplitTorus
  have hgn (j : Fin nneg) : h (Fin.castAdd (npos + 1) j) ∈
      rootGroupPoints C.i (aneg j : characterLattice C.S) := by
    have hj := hh (Fin.castAdd (npos + 1) j)
    rw [orderedIntegralIndex_castAdd] at hj
    exact (C.apartment.mem_rootFixer.1 hj).1
  have hgp (j : Fin npos) : h (Fin.natAdd nneg j.succ) ∈
      rootGroupPoints C.i (apos j : characterLattice C.S) := by
    have hj := hh (Fin.natAdd nneg j.succ)
    rw [orderedIntegralIndex_natAdd_succ] at hj
    exact (C.apartment.mem_rootFixer.1 hj).1
  have ht := hh (Fin.natAdd nneg 0)
  rw [orderedIntegralIndex_natAdd_zero] at ht
  obtain ⟨s, hs, hst⟩ := ht
  obtain ⟨tn, htn, htw, htx⟩ := exists_normalizer_of_mem_torusIwahori C E hrep hs
  -- the factorization at every point of `Ω'`
  have hfac (x : C.Apartment) (hx : x ∈ Ω') :
      (∀ j, h (Fin.castAdd (npos + 1) j) ∈
          C.apartment.filtration x (aneg j : characterLattice C.S) 0) ∧
        (∀ j, h (Fin.natAdd nneg j.succ) ∈
          C.apartment.filtration x (apos j : characterLattice C.S) 0) := by
    have hfix : (List.ofFn h).prod • C.apartmentMap x = C.apartmentMap x :=
      (C.apartment.mem_pointwiseFixer.1 hmem.2) _ ⟨x, hx, rfl⟩
    rw [list_prod_ofFn_eq, ← hst, ← htn] at hfix
    exact C.apartment.mem_filtration_of_orderedProduct_mul_smul_apartmentMap_eq hG hi ν hν x
      (fun j => (aneg j : characterLattice C.S)) (Subtype.val_injective.comp haneg) hrneg
      (fun j => (apos j : characterLattice C.S)) (Subtype.val_injective.comp hapos) hrpos
      _ hgn _ hgp tn htw (htx x) hfix
  intro idx
  induction idx using Fin.addCases with
  | left j =>
    rw [orderedIntegralIndex_castAdd]
    exact C.apartment.mem_rootFixer.2 ⟨hgn j, fun x hx => (hfac x hx).1 j⟩
  | right j =>
    induction j using Fin.cases with
    | zero =>
      rw [orderedIntegralIndex_natAdd_zero]
      exact ⟨s, hs, hst⟩
    | succ j =>
      rw [orderedIntegralIndex_natAdd_succ]
      exact C.apartment.mem_rootFixer.2 ⟨hgp j, fun x hx => (hfac x hx).2 j⟩

end Langlands.BruhatTits.IntegralModels
