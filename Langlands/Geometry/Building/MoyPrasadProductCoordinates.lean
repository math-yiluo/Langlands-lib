import Langlands.Geometry.Building.MoyPrasadGlobalExchange
import Langlands.Geometry.Building.MoyPrasadPositiveCollection

/-! # Original ordered Moy–Prasad coordinates at positive depth -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} (Zf : P.CentralizerFiltration)

/-- The range of the original ordered multiplication is exactly the original
positive-depth Moy–Prasad subgroup, for every complete root ordering. -/
theorem range_orderedMoyPrasadProduct_eq
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (x : P.Apartment) (r : NNReal) (hr : 0 < r)
    (nu : cocharacterLattice P.S) (hnu : IsGenericCocharacter P.i nu)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice P.S)
    (apos : Fin npos → characterLattice P.S)
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-nu))
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i nu) :
    Set.range (Zf.orderedMoyPrasadProduct x r aneg apos) =
      (Zf.moyPrasad x r : Set (rationalPoints G)) := by
  have hN := P.apartment.range_orderedPositiveFiltrationBlockProduct_eq_iSup
    hP.isAffineRootSystem_extendedAffineRoots hP.derivativeRoots_extendedAffineRoots
    x r r.coe_nonneg (-nu) aneg hrneg
  have hQ := P.apartment.range_orderedPositiveFiltrationBlockProduct_eq_iSup
    hP.isAffineRootSystem_extendedAffineRoots hP.derivativeRoots_extendedAffineRoots
    x r r.coe_nonneg nu apos hrpos
  change Set.range (P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) aneg) =
    (P.depthRootSpan x r (positiveRelativeRoots P.i (-nu)) : Set (rationalPoints G)) at hN
  change Set.range (P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) apos) =
    (P.depthRootSpan x r (positiveRelativeRoots P.i nu) : Set (rationalPoints G)) at hQ
  rw [Zf.moyPrasad_eq_negative_image_positive hP hZ x r hr nu hnu]
  ext g
  constructor
  · rintro ⟨p, rfl⟩
    exact Set.mul_mem_mul (Set.mul_mem_mul
      (hN ▸ Set.mem_range_self p.1)
      (⟨p.2.1, p.2.1.property, rfl⟩ :
        rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) ∈
          Zf.image r)) (hQ ▸ Set.mem_range_self p.2.2)
  · rintro ⟨_, ⟨n, hn, z, hz, rfl⟩, q, hq, rfl⟩
    obtain ⟨un, hun⟩ := (show n ∈ Set.range
      (P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) aneg) from hN ▸ hn)
    obtain ⟨up, hup⟩ := (show q ∈ Set.range
      (P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) apos) from hQ ▸ hq)
    obtain ⟨c, hc, hcz⟩ := hz
    refine ⟨(un, ⟨c, hc⟩, up), ?_⟩
    change P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) aneg un *
      rationalPoints.map P.centralizer.j c *
        P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) apos up = n * z * q
    rw [hun, hup, hcz]

/-- The unchanged original ordered product as an equivalence onto the
original positive-depth Moy–Prasad subgroup. -/
def orderedMoyPrasadProductEquiv
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (x : P.Apartment) (r : NNReal) (hr : 0 < r)
    (nu : cocharacterLattice P.S) (hnu : IsGenericCocharacter P.i nu)
    {nneg npos : ℕ} (aneg : Fin nneg → characterLattice P.S)
    (apos : Fin npos → characterLattice P.S)
    (haneg : Function.Injective aneg)
    (hrneg : Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-nu))
    (hapos : Function.Injective apos)
    (hrpos : Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i nu) :
    ((∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (aneg j)) ×
      Zf.filtration r ×
      (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (apos j))) ≃
        Zf.moyPrasad x r := by
  let f (p : (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (aneg j)) ×
      Zf.filtration r ×
      (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (apos j))) :
      Zf.moyPrasad x r :=
    ⟨Zf.orderedMoyPrasadProduct x r aneg apos p, by
      change Zf.orderedMoyPrasadProduct x r aneg apos p ∈
        (Zf.moyPrasad x r : Set (rationalPoints G))
      rw [← Zf.range_orderedMoyPrasadProduct_eq hP hZ x r hr nu hnu aneg apos hrneg hrpos]
      exact Set.mem_range_self p⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    exact Zf.orderedMoyPrasadProduct_injective x r nu aneg apos haneg hrneg hapos hrpos
      (congrArg Subtype.val hpq)
  · intro g
    have hg : (g : rationalPoints G) ∈
        Set.range (Zf.orderedMoyPrasadProduct x r aneg apos) := by
      rw [Zf.range_orderedMoyPrasadProduct_eq hP hZ x r hr nu hnu aneg apos hrneg hrpos]
      exact g.property
    obtain ⟨p, hp⟩ := hg
    exact ⟨p, Subtype.ext hp⟩

/-- The actual Moy–Prasad filtration is separated, by its positive-depth
coordinates, the original block separation and the centralizer separation. -/
theorem iInf_moyPrasad_eq_bot
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (x : P.Apartment) :
    ⨅ r, Zf.moyPrasad x r = ⊥ := by
  classical
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hT := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hfinite := hT.finite_relativeRoots P.i
  obtain ⟨nu, hnu⟩ := hT.exists_genericCocharacter P.i
  obtain ⟨nneg, aneg, haneg, hrneg⟩ :=
    RelativeRoot.exists_fin_enumeration_indivisiblePositiveRoots P.i (-nu) hfinite
  obtain ⟨npos, apos, hapos, hrpos⟩ :=
    RelativeRoot.exists_fin_enumeration_indivisiblePositiveRoots P.i nu hfinite
  exact Zf.iInf_moyPrasad_eq_bot_of_positive_cover x nu aneg apos haneg hrneg hapos hrpos
    (fun r hr => Zf.range_orderedMoyPrasadProduct_eq hP hZ x r hr nu hnu aneg apos hrneg hrpos)

end Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration
