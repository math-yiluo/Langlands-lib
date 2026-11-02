import Langlands.Sheaf.Equivariant.SmoothSpatialInduction
import Langlands.Sheaf.Equivariant.LocallyConstantSmooth
import Langlands.Representation.Induction.OpenAdjunction

/-! # Full smooth locally constant sheaves under spatial induction -/

noncomputable section

universe u

namespace Langlands.Sheaf.Equivariant.SpatialInduction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
open Langlands.TopologicalInduction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))
  (X : Type u) [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X]

include hH in
/-- Stable neighbourhoods on the local space give actual stable neighbourhoods
in every translated chart of the balanced quotient. -/
theorem hasStableNeighbourhoods_induced [HasStableNeighbourhoods H X] :
    HasStableNeighbourhoods G (Space H X) where
  exists_stable z O hO hz := by
    obtain ⟨⟨g, x⟩, rfl⟩ := Quotient.exists_rep z
    obtain ⟨K, V, hV, hxV, hVO, hKV⟩ :=
      HasStableNeighbourhoods.exists_stable (G := H) x (chart H g ⁻¹' O)
        (hO.preimage (continuous_chart H g)) hz
    have hc : Continuous (MulAut.conj g⁻¹).toMonoidHom := by
      change Continuous fun k : G => g⁻¹ * k * (g⁻¹)⁻¹
      fun_prop
    let K₀ := openSubgroupImage H hH K
    let L := K₀.comap (MulAut.conj g⁻¹).toMonoidHom hc
    refine ⟨L, chart H g '' V, (isOpenEmbedding_chart H hH g).isOpenMap _ hV,
      ⟨x, hxV, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hVO hy
    · intro k hk z hz
      obtain ⟨y, hy, rfl⟩ := hz
      have hkg : g⁻¹ * k * g ∈ K₀ := by
        change (MulAut.conj g⁻¹) k ∈ K₀ at hk
        simpa only [MulAut.conj_apply, inv_inv] using hk
      obtain ⟨h, hh, he⟩ := hkg
      refine ⟨h • y, hKV h hh y hy, ?_⟩
      have hmul : k * g = g * (h : G) := by
        change (h : G) = g⁻¹ * k * g at he
        rw [he]
        group
      change mk H g (h • y) = mk H (k * g) y
      rw [hmul, mk_balance]

include hH in
/-- Stable neighbourhoods on the quotient restrict to actual preimages in
the open unit chart. -/
theorem hasStableNeighbourhoods_local [HasStableNeighbourhoods G (Space H X)] :
    HasStableNeighbourhoods H X where
  exists_stable x O hO hx := by
    obtain ⟨K, V, hV, hxV, hVO, hKV⟩ :=
      HasStableNeighbourhoods.exists_stable (G := G) (unit H x) (unit H '' O)
        ((isOpenEmbedding_unit (X := X) hH).isOpenMap O hO) ⟨x, hx, rfl⟩
    let L := K.comap H.subtype continuous_subtype_val
    refine ⟨L, unit H ⁻¹' V, hV.preimage continuous_unit, hxV, ?_, ?_⟩
    · intro y hy
      obtain ⟨w, hw, he⟩ := hVO hy
      exact unit_injective he ▸ hw
    · intro h hh y hy
      change unit H (h • y) ∈ V
      rw [unit_subgroup_smul]
      exact hKV (h : G) hh (unit H y) hy

include hH in
/-- The local and ambient stable-neighbourhood properties agree on these actual spaces. -/
theorem hasStableNeighbourhoods_iff :
    HasStableNeighbourhoods H X ↔ HasStableNeighbourhoods G (Space H X) := by
  constructor
  · intro h
    let _ := h
    exact hasStableNeighbourhoods_induced H hH X
  · intro h
    let _ := h
    exact hasStableNeighbourhoods_local H hH X

variable (R : Type u) [CommRing R] [HasStableNeighbourhoods H X]

/-- The actual full smooth ambient coefficient functor, using the proved
stable neighbourhoods of the balanced quotient. -/
def smoothLocallyConstantFunctor :
    Langlands.SmoothRep.{u, u, u} R G ⥤ SmoothTopologicalSheaf R G (Space H X) := by
  letI := hasStableNeighbourhoods_induced H hH X
  exact LocallyConstantSheaf.smoothFunctor R G (Space H X)

/-- Forgetting smoothness recovers all original ambient sections and coefficient maps. -/
def smoothLocallyConstantFunctorForgetIso :
    smoothLocallyConstantFunctor H hH X R ⋙ smoothInclusion R G (Space H X) ≅
      Langlands.SmoothRep.toRep ⋙ LocallyConstantSheaf.functor R G (Space H X) := by
  letI := hasStableNeighbourhoods_induced H hH X
  exact LocallyConstantSheaf.smoothFunctorForgetIso R G (Space H X)

/-- Restriction identifies the unchanged full smooth locally constant sheaves. -/
def smoothRestrictLocallyConstantIso (A : Langlands.SmoothRep.{u, u, u} R G) :
    (smoothRestrict R H hH X).obj ((smoothLocallyConstantFunctor H hH X R).obj A) ≅
      (LocallyConstantSheaf.smoothFunctor R H X).obj
        ((Langlands.Induction.smoothRestriction R H).obj A) :=
  (smoothSheafProperty R H X).isoMk (restrictLocallyConstantIso H hH X A.representation)

@[simp]
theorem smoothRestrictLocallyConstantIso_hom_app
    (A : Langlands.SmoothRep.{u, u, u} R G) (U : ActionOpens H X)
    (s : LocallyConstant (unitOpen H hH X U).openSet A) (x : U.openSet) :
    LocallyConstant.toFun
        (((smoothRestrictLocallyConstantIso H hH X R A).hom.hom.hom.app (op U)) s) x =
      s (unitOpenHomeomorph H hH X U x) := rfl

@[simp]
theorem smoothRestrictLocallyConstantIso_inv_app
    (A : Langlands.SmoothRep.{u, u, u} R G) (U : ActionOpens H X)
    (s : LocallyConstant U.openSet A) (x : (unitOpen H hH X U).openSet) :
    LocallyConstant.toFun
        (((smoothRestrictLocallyConstantIso H hH X R A).inv.hom.hom.app (op U)) s) x =
      s ((unitOpenHomeomorph H hH X U).symm x) := rfl

/-- The smooth unit-chart comparison is natural in every original coefficient intertwiner. -/
def smoothRestrictLocallyConstantNatIso :
    smoothLocallyConstantFunctor H hH X R ⋙ smoothRestrict R H hH X ≅
      Langlands.Induction.smoothRestriction R H ⋙
        LocallyConstantSheaf.smoothFunctor R H X :=
  NatIso.ofComponents (fun A => smoothRestrictLocallyConstantIso H hH X R A) (by
    intro A B a
    apply ObjectProperty.hom_ext
    exact (restrictLocallyConstantNatIso (R := R) H hH X).hom.naturality a.hom)

/-- Genuine smooth right Kan induction reconstructs the full ambient coefficient
sheaf, naturally in all original smooth coefficient maps. -/
def smoothInduceLocallyConstantNatIso :
    (Langlands.Induction.smoothRestriction R H ⋙
        LocallyConstantSheaf.smoothFunctor R H X) ⋙ smoothInduce R H hH X ≅
      smoothLocallyConstantFunctor H hH X R :=
  Functor.isoWhiskerRight (smoothRestrictLocallyConstantNatIso H hH X R).symm
      (smoothInduce R H hH X) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (smoothLocallyConstantFunctor H hH X R)
      (smoothInduceRestrictIso R H hH X) ≪≫
    Functor.rightUnitor _

/-- The converse full smooth sheaf comparison at an arbitrary smooth coefficient object. -/
def smoothInduceLocallyConstantIso (A : Langlands.SmoothRep.{u, u, u} R G) :
    (smoothInduce R H hH X).obj
        ((LocallyConstantSheaf.smoothFunctor R H X).obj
          ((Langlands.Induction.smoothRestriction R H).obj A)) ≅
      (smoothLocallyConstantFunctor H hH X R).obj A :=
  (smoothInduceLocallyConstantNatIso H hH X R).app A

end Langlands.Sheaf.Equivariant.SpatialInduction
