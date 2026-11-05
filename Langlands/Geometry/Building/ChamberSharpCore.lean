import Langlands.Geometry.Building.ChamberPositiveCollection
import Langlands.Geometry.Building.ChamberOrderedProductInjective
import Langlands.Geometry.Building.ChamberNormalizerSeparation

/-! # Sharp chamber conclusions from right-central core factorization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Every positive zero-depth root generator lies in the corresponding
Dynamic unipotent group and the point's sharp fixer. -/
theorem positiveChamberRootGroups_le_sharpUnipotentPoints
    (x : D.Apartment) (ν : cocharacterLattice S) :
    (⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x false b) ≤
      D.sharpUnipotentPoints ν {x} := by
  refine iSup_le fun b => le_inf ?_ ?_
  · exact (D.filtration_le_rootGroupPoints x b 0).trans
      (RelativeRoot.subgroup_le_dynamicUnipotent i ν b.2.2 (Over.mk (𝟙 _)))
  · change D.filtration x b 0 ≤ D.sharpFixer {x}
    rw [← D.rootFixer_singleton]
    exact D.rootFixer_le_sharpFixer ⟨b, b.2.1⟩ {x}

omit [Mono i.hom.hom.left] [IsAffineHom G.X.hom] in
/-- Torus-central points preserve every Dynamic unipotent subgroup. -/
theorem centralizer_conj_mem_dynamicUnipotent
    (ν : cocharacterLattice S) {z g : rationalPoints G}
    (hz : z ∈ centralizerPoints i)
    (hg : g ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))) :
    z * g * z⁻¹ ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
  have hzχ : z ∈ (Dynamic.centralizer
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
    apply torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ν)
      (Over.mk (𝟙 _))
    change z ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _))
    rw [torusCentralizer_carrier_base]
    exact hz
  exact Dynamic.conj_mem_unipotent _ (Dynamic.centralizer_le_parabolic _ _ hzχ) hg

/-- A right-central core factorization identifies the positive generated
subgroup with the actual sharp unipotent intersection. -/
theorem positiveChamberRootGroups_eq_sharpUnipotentPoints_of_core
    (x : D.Apartment) (ν : cocharacterLattice S)
    (hcore : (D.sharpFixer {x} : Set (rationalPoints G)) ⊆
      ((⨆ b : positiveRelativeRoots i (-ν), D.chamberRootGroup x false b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
      ((⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x false b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
      (D.sharpCentralizer {x} : Set (rationalPoints G))) :
    (⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x false b) =
      D.sharpUnipotentPoints ν {x} := by
  apply le_antisymm (D.positiveChamberRootGroups_le_sharpUnipotentPoints x ν)
  intro g hg
  obtain ⟨vw, ⟨v, hv, w, hw, rfl⟩, z, hz, hmul⟩ := hcore hg.2
  let Uminus := (Dynamic.unipotent
    (CommGroupScheme.groupHom (-ν) ≫ i)).carrier (Over.mk (𝟙 _))
  let Uplus := (Dynamic.unipotent
    (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))
  have hvU : v ∈ Uminus :=
    (D.positiveChamberRootGroups_le_sharpUnipotentPoints x (-ν) hv).1
  have hwU : w ∈ Uplus :=
    (D.positiveChamberRootGroups_le_sharpUnipotentPoints x ν hw).1
  have hcU : z⁻¹ * w * z ∈ Uplus := by
    simpa only [inv_inv] using centralizer_conj_mem_dynamicUnipotent ν
      ((centralizerPoints i).inv_mem hz.1) hwU
  let p : Uminus × centralizerPoints i × Uplus :=
    (⟨v, hvU⟩, ⟨z, hz.1⟩, ⟨z⁻¹ * w * z, hcU⟩)
  let q : Uminus × centralizerPoints i × Uplus := (1, 1, ⟨g, hg.1⟩)
  have hpq : p = q :=
    unipotentTripleProduct_injective i ν Uminus Uplus
      (fun z : centralizerPoints i => (z : rationalPoints G))
      Subtype.val_injective le_rfl le_rfl (fun z => z.property) (by
        change v * z * (z⁻¹ * w * z) = (1 : rationalPoints G) * 1 * g
        simpa only [mul_assoc, mul_inv_cancel_left, one_mul] using hmul)
  have hv1 : v = 1 := congrArg (fun t : Uminus × centralizerPoints i × Uplus =>
    (t.1 : rationalPoints G)) hpq
  have hz1 : z = 1 := congrArg (fun t : Uminus × centralizerPoints i × Uplus =>
    (t.2.1 : rationalPoints G)) hpq
  have hwg : w = g := by simpa only [hv1, hz1, one_mul, mul_one] using hmul
  exact hwg ▸ hw

/-- The identity on rational points identifies the actual generated positive
subgroup with the sharp unipotent intersection under the core inclusion. -/
def positiveChamberSharpEquivOfCore
    (x : D.Apartment) (ν : cocharacterLattice S)
    (hcore : (D.sharpFixer {x} : Set (rationalPoints G)) ⊆
      ((⨆ b : positiveRelativeRoots i (-ν), D.chamberRootGroup x false b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
      ((⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x false b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
      (D.sharpCentralizer {x} : Set (rationalPoints G))) :
    (⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x false b :
      Subgroup (rationalPoints G)) ≃*
      D.sharpUnipotentPoints ν {x} :=
  MulEquiv.subgroupCongr
    (D.positiveChamberRootGroups_eq_sharpUnipotentPoints_of_core x ν hcore)

/-- The equivalence changes only subgroup membership proofs. -/
@[simp]
theorem coe_positiveChamberSharpEquivOfCore
    (x : D.Apartment) (ν : cocharacterLattice S)
    (hcore : (D.sharpFixer {x} : Set (rationalPoints G)) ⊆
      ((⨆ b : positiveRelativeRoots i (-ν), D.chamberRootGroup x false b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
      ((⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x false b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
      (D.sharpCentralizer {x} : Set (rationalPoints G)))
    (g : (⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x false b :
      Subgroup (rationalPoints G))) :
    (D.positiveChamberSharpEquivOfCore x ν hcore g : rationalPoints G) = g :=
  MulEquiv.subgroupCongr_apply _ g

/-- The core inclusion already gives the exact sharp three-factor range;
centrality preserves the Dynamic condition when moving the last factor. -/
theorem range_sharpUnipotentProduct_of_core
    (C : Set D.Apartment) (x : D.Apartment) (ν : cocharacterLattice S)
    (hfixer : D.sharpFixer C = D.sharpFixer {x})
    (hcore : (D.sharpFixer {x} : Set (rationalPoints G)) ⊆
      ((⨆ b : positiveRelativeRoots i (-ν), D.chamberRootGroup x false b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
      ((⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x false b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
      (D.sharpCentralizer {x} : Set (rationalPoints G))) :
    Set.range (D.sharpUnipotentProduct C x ν) =
      (D.sharpFixer C : Set (rationalPoints G)) := by
  ext g
  constructor
  · rintro ⟨p, rfl⟩
    exact (D.sharpFixer C).mul_mem
      ((D.sharpFixer C).mul_mem p.1.property.2
        (by rw [hfixer]; exact p.2.1.property.2)) p.2.2.property.2
  · intro hg
    have hgx : g ∈ D.sharpFixer {x} := by rw [← hfixer]; exact hg
    obtain ⟨vw, ⟨v, hv, w, hw, rfl⟩, z, hz, hmul⟩ := hcore hgx
    have hvS := D.positiveChamberRootGroups_le_sharpUnipotentPoints x (-ν) hv
    have hwS := D.positiveChamberRootGroups_le_sharpUnipotentPoints x ν hw
    have hvC : v ∈ D.sharpUnipotentPoints (-ν) C := by
      simpa only [sharpUnipotentPoints, hfixer] using hvS
    have hcS : z⁻¹ * w * z ∈ D.sharpUnipotentPoints ν {x} := by
      refine ⟨?_, (D.sharpFixer {x}).mul_mem
        ((D.sharpFixer {x}).mul_mem ((D.sharpFixer {x}).inv_mem hz.2) hwS.2) hz.2⟩
      change z⁻¹ * w * z ∈ (Dynamic.unipotent
        (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))
      simpa only [inv_inv] using centralizer_conj_mem_dynamicUnipotent ν
        ((centralizerPoints i).inv_mem hz.1) hwS.1
    have hcC : z⁻¹ * w * z ∈ D.sharpUnipotentPoints ν C := by
      simpa only [sharpUnipotentPoints, hfixer] using hcS
    refine ⟨(⟨v, hvC⟩, ⟨z, hz⟩, ⟨z⁻¹ * w * z, hcC⟩), ?_⟩
    change v * z * (z⁻¹ * w * z) = g
    simpa only [mul_assoc, mul_inv_cancel_left] using hmul

/-- Individual factor ranges transport to the original ordered sharp product
without changing any coordinate or the central factor. -/
theorem range_orderedSharpChamberProduct_of_block_ranges
    (C : Set D.Apartment) (x : D.Apartment) (strict : Bool)
    (ν : cocharacterLattice S) {nneg npos : ℕ}
    (aneg : Fin nneg → characterLattice S) (apos : Fin npos → characterLattice S)
    (hrneg : Set.range (D.orderedChamberBlockProduct x strict aneg) =
      (D.sharpUnipotentPoints (-ν) C : Set (rationalPoints G)))
    (hrpos : Set.range (D.orderedChamberBlockProduct x strict apos) =
      (D.sharpUnipotentPoints ν C : Set (rationalPoints G))) :
    Set.range (D.orderedSharpChamberProduct x strict aneg apos) =
      Set.range (D.sharpUnipotentProduct C x ν) := by
  ext g
  constructor
  · rintro ⟨p, rfl⟩
    have hv : D.orderedChamberBlockProduct x strict aneg p.1 ∈
        D.sharpUnipotentPoints (-ν) C := by
      change _ ∈ (D.sharpUnipotentPoints (-ν) C : Set (rationalPoints G))
      rw [← hrneg]
      exact Set.mem_range_self p.1
    have hw : D.orderedChamberBlockProduct x strict apos p.2.2 ∈
        D.sharpUnipotentPoints ν C := by
      change _ ∈ (D.sharpUnipotentPoints ν C : Set (rationalPoints G))
      rw [← hrpos]
      exact Set.mem_range_self p.2.2
    exact ⟨(⟨_, hv⟩, p.2.1, ⟨_, hw⟩), rfl⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨v, hv⟩ := (show (p.1 : rationalPoints G) ∈
        Set.range (D.orderedChamberBlockProduct x strict aneg) by
      rw [hrneg]; exact p.1.property)
    obtain ⟨w, hw⟩ := (show (p.2.2 : rationalPoints G) ∈
        Set.range (D.orderedChamberBlockProduct x strict apos) by
      rw [hrpos]; exact p.2.2.property)
    refine ⟨(v, p.2.1, w), ?_⟩
    simp only [orderedSharpChamberProduct, sharpUnipotentProduct, hv, hw]

/-- At a chamber point either zero-depth root group is the depth-zero one. -/
theorem chamberRootGroup_eq_zero_of_mem_chamber
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {C : Set D.Apartment} (hC : AffineRootSystem.IsChamber D.affineRoots C)
    {x : D.Apartment} (hx : x ∈ C) (strict : Bool)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.chamberRootGroup x strict a = D.chamberRootGroup x false a := by
  cases strict with
  | false => rfl
  | true => exact (D.filtration_eq_filtrationPlus_of_mem_chamber hAS4 hC hx ha).symm

/-- The exact sharp chamber conclusion follows from the right-central core
inclusion, with the Dynamic premise supplying ordered-coordinate injectivity. -/
theorem chamberSharpConclusion_of_core
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots = Set.range (rootForm i))
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {C : Set D.Apartment} (hC : AffineRootSystem.IsChamber D.affineRoots C)
    {x : D.Apartment} (hx : x ∈ C)
    (hcore : ∀ mu : cocharacterLattice S, IsGenericCocharacter i mu →
      (D.sharpFixer {x} : Set (rationalPoints G)) ⊆
      ((⨆ b : positiveRelativeRoots i (-mu), D.chamberRootGroup x false b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
      ((⨆ b : positiveRelativeRoots i mu, D.chamberRootGroup x false b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
      (D.sharpCentralizer {x} : Set (rationalPoints G)))
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν) :
    D.ChamberSharpConclusion C x ν := by
  have hfixer := D.sharpFixer_eq_singleton_of_isFacet hAS4 hC.isFacet hx
  have hrange := D.range_sharpUnipotentProduct_of_core C x ν hfixer (hcore ν hν)
  have hνneg : IsGenericCocharacter i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  have hblock (mu : cocharacterLattice S) (hmu : IsGenericCocharacter i mu)
      (strict : Bool) {n : ℕ} (a : Fin n → characterLattice S)
      (ha : Set.range a = RelativeRoot.indivisiblePositiveRoots i mu) :
      Set.range (D.orderedChamberBlockProduct x strict a) =
        (D.sharpUnipotentPoints mu C : Set (rationalPoints G)) := by
    rw [D.range_orderedPositiveChamberBlockProduct_eq_iSup hsys hderiv x strict mu a ha]
    apply congrArg (fun H : Subgroup (rationalPoints G) => (H : Set (rationalPoints G)))
    calc
      (⨆ b : positiveRelativeRoots i mu, D.chamberRootGroup x strict b) =
          ⨆ b : positiveRelativeRoots i mu, D.chamberRootGroup x false b :=
        iSup_congr fun b => D.chamberRootGroup_eq_zero_of_mem_chamber
          hAS4 hC hx strict b.2.1
      _ = D.sharpUnipotentPoints mu {x} :=
        D.positiveChamberRootGroups_eq_sharpUnipotentPoints_of_core x mu (hcore mu hmu)
      _ = D.sharpUnipotentPoints mu C := by simp only [sharpUnipotentPoints, hfixer]
  refine ⟨D.chamberRootFiltrationConclusion hAS4 hC hx,
    D.sharpNormalizer_eq_sharpCentralizer_of_sharpProductRange C x ν hfixer hrange,
    D.sharpUnipotentProduct_injective C x ν, hrange, ?_⟩
  intro strict nneg npos aneg apos haneg hrneg hapos hrpos
  have hn := hblock (-ν) hνneg strict aneg hrneg
  have hp := hblock ν hν strict apos hrpos
  exact ⟨D.orderedChamberBlockProduct_injective_of_dynamicRootOrderedProduct
      hprod hG hi x strict (-ν) aneg haneg hrneg, hn,
    D.orderedChamberBlockProduct_injective_of_dynamicRootOrderedProduct
      hprod hG hi x strict ν apos hapos hrpos, hp,
    D.orderedSharpChamberProduct_injective_of_dynamicRootOrderedProduct
      hprod hG hi x strict ν aneg apos haneg hrneg hapos hrpos,
    (D.range_orderedSharpChamberProduct_of_block_ranges C x strict ν aneg apos hn hp).trans
      hrange⟩

end Langlands.Geometry.Building.KPApartmentData
