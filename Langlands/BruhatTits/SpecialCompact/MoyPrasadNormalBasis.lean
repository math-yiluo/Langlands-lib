import Langlands.BruhatTits.SpecialCompact.InheritedNormalBasis
import Langlands.Geometry.Building.KPMoyPrasadFiltrationStatement
import Langlands.Geometry.Building.KPParahoricFixerComparison
import Langlands.Geometry.Building.SpecialCompact

/-! # A normal basis from the original Moy–Prasad filtration -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology Filter Set
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

/-- A prescribed decreasing separated family of open subgroups inside a compact
subgroup is cofinal at the identity. If its members are normal in that compact,
the very same family is a compact-open normal basis. -/
theorem compactOpenNormalBasis_of_antitone
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {Idx : Type v} [SemilatticeSup Idx] [Nonempty Idx]
    (K0 : Subgroup H) (K : Idx → Subgroup H)
    (hcompact : IsCompact (K0 : Set H))
    (hle : ∀ r, K r ≤ K0) (hanti : Antitone K)
    (hopen : ∀ r, IsOpen (K r : Set H))
    (hnormal : ∀ r, ((K r).subgroupOf K0).Normal)
    (hsep : ⨅ r, K r = ⊥) :
    CompactOpenNormalBasis K0 (Set.range K) := by
  have hclosed (r : Idx) : IsClosed (K r : Set H) :=
    (K r).isClosed_of_isOpen (hopen r)
  have hcpct (r : Idx) : IsCompact (K r : Set H) :=
    hcompact.of_isClosed_subset (hclosed r) (hle r)
  have hinter : (⋂ r, (K r : Set H)) = {1} := by
    rw [← Subgroup.coe_iInf, hsep]
    rfl
  refine ⟨?_, hasBasis_iff.mpr ?_⟩
  · rintro L ⟨r, rfl⟩
    exact ⟨hle r, hnormal r, hopen r, hcpct r⟩
  · intro W
    constructor
    · intro hW
      have hW' : W ∈ 𝓝ˢ (⋂ r, (K r : Set H)) := by
        simpa only [hinter, nhdsSet_singleton] using hW
      obtain ⟨r, hr⟩ := exists_subset_nhds_of_isCompact'
        (fun a b => ⟨a ⊔ b, hanti le_sup_left, hanti le_sup_right⟩)
        hcpct hclosed hW'
      exact ⟨K r, ⟨r, rfl⟩, hr⟩
    · rintro ⟨L, ⟨r, rfl⟩, hLW⟩
      exact mem_of_superset ((hopen r).mem_nhds (K r).one_mem) hLW

section MoyPrasad

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration) (x : P.Apartment)

local instance moyPrasadNormalBasisAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance moyPrasadNormalBasisTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- The actual nonnegative-depth subgroups at the specified apartment point,
without replacing them by normal cores or other subgroups. -/
def moyPrasadFamily : Set (Subgroup (rationalPoints G)) :=
  Set.range (Zf.moyPrasad x)

/-- Uniqueness of presentations at this building point makes every depth
subgroup invariant under every element fixing the point. -/
theorem moyPrasad_map_conj_eq_of_fixes
    (hcov : ∀ (r : NNReal) (Q Q' : Subgroup (rationalPoints G)),
      Zf.IsMoyPrasadAt (P.apartmentMap x) r Q →
      Zf.IsMoyPrasadAt (P.apartmentMap x) r Q' → Q = Q')
    (r : NNReal) (g : rationalPoints G)
    (hg : g • P.apartmentMap x = P.apartmentMap x) :
    (Zf.moyPrasad x r).map (MulAut.conj g).toMonoidHom = Zf.moyPrasad x r := by
  have hconj := (Zf.isMoyPrasadAt_apartmentMap x r).smul g
  rw [hg] at hconj
  exact hcov r _ _ hconj (Zf.isMoyPrasadAt_apartmentMap x r)

/-- The original depth subgroups are normal in the original norm-one point
fixer when the supplied covariance uniqueness holds there. -/
theorem moyPrasad_normal_in_specialCompactSubgroup
    (hcov : ∀ (r : NNReal) (Q Q' : Subgroup (rationalPoints G)),
      Zf.IsMoyPrasadAt (P.apartmentMap x) r Q →
      Zf.IsMoyPrasadAt (P.apartmentMap x) r Q' → Q = Q') (r : NNReal) :
    ((Zf.moyPrasad x r).subgroupOf (P.apartment.specialCompactSubgroup x)).Normal := by
  constructor
  intro n hn g
  change (g : rationalPoints G) * (n : rationalPoints G) *
    (g : rationalPoints G)⁻¹ ∈ Zf.moyPrasad x r
  have heq := moyPrasad_map_conj_eq_of_fixes P Zf x hcov r g
    (P.apartment.mem_specialCompactSubgroup.mp g.property).2
  rw [← heq]
  exact Subgroup.mem_map.mpr ⟨(n : rationalPoints G), hn, rfl⟩

/-- Openness, separatedness and covariance of the original depth groups give
a normal compact-open basis of the same geometric compact stabilizer. -/
theorem compactOpenNormalBasis_moyPrasadFamily
    (hP : P.apartment.IsTopologyCompatible)
    (hcompact : IsCompact (P.apartment.specialCompactSubgroup x : Set (rationalPoints G)))
    (hopen : ∀ r : NNReal, IsOpen (Zf.moyPrasad x r : Set (rationalPoints G)))
    (hsep : ⨅ r, Zf.moyPrasad x r = ⊥)
    (hcov : ∀ (r : NNReal) (Q Q' : Subgroup (rationalPoints G)),
      Zf.IsMoyPrasadAt (P.apartmentMap x) r Q →
      Zf.IsMoyPrasadAt (P.apartmentMap x) r Q' → Q = Q') :
    CompactOpenNormalBasis (P.apartment.specialCompactSubgroup x)
      (moyPrasadFamily P Zf x) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  exact compactOpenNormalBasis_of_antitone _ _ hcompact
    (fun r => (Zf.moyPrasad_le_parahoricAt x r).trans
      (P.parahoricAt_le_compactStabilizer hP x))
    (Zf.moyPrasad_antitone x) hopen
    (moyPrasad_normal_in_specialCompactSubgroup P Zf x hcov) hsep

/-- Specialize the normal-basis construction to the three published
Moy–Prasad proposition targets, which remain explicit hypotheses here. -/
theorem compactOpenNormalBasis_moyPrasadFamily_of_statements
    (hseparated : MoyPrasadSeparatedStatement.{u})
    (hboundedOpen : MoyPrasadBoundedOpenStatement.{u})
    (hcovariance : MoyPrasadCovarianceStatement.{u})
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.SatisfiesFiltrationAxioms)
    (hZo : Zf.IsOpenFiltration)
    (hcompact : IsCompact (P.apartment.specialCompactSubgroup x : Set (rationalPoints G))) :
    CompactOpenNormalBasis (P.apartment.specialCompactSubgroup x)
      (moyPrasadFamily P Zf x) := by
  exact compactOpenNormalBasis_moyPrasadFamily P Zf x hP.topologyCompatible hcompact
    (fun r => (hboundedOpen F G P Zf hP hZ hZo x r).1)
    (hseparated F G P Zf hP hZ x)
    (hcovariance F G P Zf hP hZ (P.apartmentMap x))

end MoyPrasad

end Langlands.BruhatTits.SpecialCompact
