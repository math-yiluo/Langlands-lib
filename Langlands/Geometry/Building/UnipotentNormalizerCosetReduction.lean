import Langlands.Geometry.Building.IwahoriWeylStatement
import Langlands.Geometry.Building.ChamberIwahoriStatement
import Langlands.Geometry.Building.IwahoriWeylChamberLemmas
import Langlands.GroupScheme.Rational.BruhatOppositeCellReduction
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy

/-! # Reduction of the corrected chamber normalizer-coset lemma -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The literal standard unipotent at the empty index is contained in
the dynamic unipotent of its defining cocharacter. -/
theorem standardUnipotentPoints_empty_le_dynamic (ν : cocharacterLattice P.S) :
    standardUnipotentPoints P.i ν ∅ ≤
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ P.i)).carrier
        (Over.mk (𝟙 _)) :=
  standardUnipotent_le_dynamicUnipotent P.i ν
    (isStandardCocharacter_empty_self P.i ν) _

/-- An actual normalizing point in `U(ν)⁻¹ P_C` lies in `Z(F)^0`,
provided the reversed chamber product covers `P_C`. -/
theorem mem_normalizerZero_of_unipotent_mul_mem_parahoric
    (C : Set P.Apartment) (ν : cocharacterLattice P.S)
    (hrange : Set.range (P.iwahoriUnipotentProduct C (-ν)) =
      (P.chamberIwahori C : Set (rationalPoints G)))
    (n : normalizerPoints P.i) {u : rationalPoints G}
    (hu : u ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ P.i)).carrier
      (Over.mk (𝟙 _)))
    (hun : u * (n : rationalPoints G) ∈ P.parahoric C) :
    n ∈ P.normalizerZero := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hχ : CommGroupScheme.groupHom (- -ν) ≫ P.i =
      CommGroupScheme.groupHom ν ≫ P.i := by rw [neg_neg]
  have hun' : u * (n : rationalPoints G) ∈
      Set.range (P.iwahoriUnipotentProduct C (-ν)) := by
    rw [hrange]
    exact hun
  obtain ⟨⟨a, z, b⟩, hprod⟩ := hun'
  have ha : (a : rationalPoints G) ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)) := by
    rw [← hχ]
    exact a.property.1
  have hb : (b : rationalPoints G) ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ P.i)).carrier
        (Over.mk (𝟙 _)) := b.property.1
  let zn : normalizerPoints P.i := P.centralizer.toNormalizer z
  let zg : rationalPoints G := rationalPoints.map P.centralizer.j z
  have hz : zg ∈ (Dynamic.centralizer
      (CommGroupScheme.groupHom (-ν) ≫ P.i)).carrier (Over.mk (𝟙 _)) :=
    torusCentralizer_le_dynamicCentralizer P.i (CommGroupScheme.groupHom (-ν)) _
      (by
        have hz0 := map_mem_centralizerPoints P.centralizer.isRepresentedBy z
        rw [← torusCentralizer_carrier_base P.i] at hz0
        exact hz0)
  have hb' : zg * (b : rationalPoints G) * zg⁻¹ ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ P.i)).carrier
        (Over.mk (𝟙 _)) :=
    Dynamic.conj_mem_unipotent _ (Dynamic.centralizer_le_parabolic _ _ hz) hb
  have ha' : u⁻¹ * (a : rationalPoints G) ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ P.i)).carrier
        (Over.mk (𝟙 _)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) ha
  have haopp : u⁻¹ * (a : rationalPoints G) ∈
      (Dynamic.unipotent
        (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫
          (CommGroupScheme.groupHom (-ν) ≫ P.i))).carrier (Over.mk (𝟙 _)) := by
    change u⁻¹ * (a : rationalPoints G) ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (CommGroupScheme.groupHom (-ν) ≫ P.i))).carrier (Over.mk (𝟙 _))
    rw [← groupHom_neg_comp_eq_oppositeCocharacter P.i (-ν), hχ]
    exact ha'
  have heq : ((n * zn⁻¹ : normalizerPoints P.i) : rationalPoints G) =
      (u⁻¹ * (a : rationalPoints G)) * (zg * (b : rationalPoints G) * zg⁻¹) := by
    change (n : rationalPoints G) * zg⁻¹ = _
    change (a : rationalPoints G) * zg * (b : rationalPoints G) =
      u * (n : rationalPoints G) at hprod
    calc
      _ = u⁻¹ * (u * (n : rationalPoints G)) * zg⁻¹ := by
        rw [inv_mul_cancel_left]
      _ = u⁻¹ * ((a : rationalPoints G) * zg * (b : rationalPoints G)) * zg⁻¹ := by
        rw [hprod]
      _ = _ := by simp only [mul_assoc]
  have hone : n * zn⁻¹ = 1 :=
    normalizer_eq_one_of_unipotent_product P.i (-ν) (n * zn⁻¹)
      ⟨_, haopp⟩ ⟨_, hb'⟩ heq
  have hn : n = zn := mul_inv_eq_one.mp hone
  rw [hn]
  exact Subgroup.mem_map.mpr ⟨z, z.property, rfl⟩

/-- Normality of the actual zero subgroup extends sharp-fixer covariance
to full parahorics. -/
theorem parahoric_le_comap_normalizer [P.normalizerZero.Normal]
    (n : normalizerPoints P.i) (C : Set P.Apartment) :
    P.parahoric C ≤
      (P.parahoric (n • C)).comap (MulAut.conj (n : rationalPoints G)).toMonoidHom := by
  refine sup_le ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    have hzN : P.centralizer.toNormalizer z ∈ P.normalizerZero :=
      Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    have hconj := (inferInstance : P.normalizerZero.Normal).conj_mem _ hzN n
    exact P.map_centralizerZero_le_parahoric (n • C)
      (P.mem_normalizerZero_iff.mp hconj)
  · exact (P.apartment.sharpFixer_le_comap n C).trans
      (Subgroup.comap_mono (P.sharpFixer_le_parahoric (n • C)))

/-- The backward implication of the replaced lemma uses only the
normality of `Z(F)^0` and its inclusion in every full parahoric. -/
theorem exists_unipotent_normalizer_parahoric_of_mem_normalizerZero
    [P.normalizerZero.Normal] (C : Set P.Apartment) (ν : cocharacterLattice P.S)
    (n n' : normalizerPoints P.i) (h : n' * n⁻¹ ∈ P.normalizerZero) :
    ∃ u ∈ standardUnipotentPoints P.i ν ∅, ∃ p ∈ P.parahoric C,
      (n : rationalPoints G) = u * (n' : rationalPoints G) * p := by
  have hcomm := (inferInstance : P.normalizerZero.Normal).mem_comm h
  have hpN : n'⁻¹ * n ∈ P.normalizerZero := by
    simpa only [mul_inv_rev, inv_inv] using P.normalizerZero.inv_mem hcomm
  refine ⟨1, (standardUnipotentPoints P.i ν ∅).one_mem,
    ((n'⁻¹ * n : normalizerPoints P.i) : rationalPoints G),
    P.map_centralizerZero_le_parahoric C (P.mem_normalizerZero_iff.mp hpN), ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, one_mul, mul_inv_cancel_left]

/-- Corrected normalizer-coset equivalence assembled from reverse chamber
product surjectivity and normality, for the actual standard unipotent. -/
theorem unipotentNormalizerCoset_of_iwahoriProducts
    [P.normalizerZero.Normal]
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (C : Set P.Apartment) (ν : cocharacterLattice P.S)
    (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (hproducts : ∀ C' : Set P.Apartment,
      AffineRootSystem.IsChamber P.affineRoots C' →
      Set.range (P.iwahoriUnipotentProduct C' (-ν)) =
        (P.chamberIwahori C' : Set (rationalPoints G))) :
    P.UnipotentNormalizerCoset C ν := by
  intro n n'
  constructor
  · rintro ⟨u, hu, p, hp, hn⟩
    apply P.mem_normalizerZero_of_unipotent_mul_mem_parahoric
      (n • C) ν (hproducts _ (P.normalizer_smul_isChamber hP hC n))
      (n' * n⁻¹) (P.standardUnipotentPoints_empty_le_dynamic ν hu)
    have hp' := P.parahoric_le_comap_normalizer n C ((P.parahoric C).inv_mem hp)
    change (n : rationalPoints G) * p⁻¹ * (n : rationalPoints G)⁻¹ ∈
      P.parahoric (n • C) at hp'
    have heq : u * (n' : rationalPoints G) = (n : rationalPoints G) * p⁻¹ :=
      eq_mul_inv_iff_mul_eq.mpr hn.symm
    change u * ((n' : rationalPoints G) * (n : rationalPoints G)⁻¹) ∈ _
    rw [← mul_assoc, heq]
    exact hp'
  · exact P.exists_unipotent_normalizer_parahoric_of_mem_normalizerZero C ν n n'

/-- The published chamber statement supplies exactly the reverse-product
premise of the local reduction; no standard/dynamic equality is required. -/
theorem unipotentNormalizerCoset_of_chamberIwahori
    [P.normalizerZero.Normal]
    (hproducts : P.ChamberIwahoriDecompositionStatement)
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (C : Set P.Apartment) (ν : cocharacterLattice P.S)
    (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (hν : IsGenericCocharacter P.i ν) :
    P.UnipotentNormalizerCoset C ν := by
  have hneg : IsGenericCocharacter P.i (-ν) := by
    intro α hα
    simpa only [map_neg, neg_ne_zero] using hν α hα
  apply P.unipotentNormalizerCoset_of_iwahoriProducts hP C ν hC
  intro C' hC'
  obtain ⟨x, hx, hfacet⟩ := hC'
  have hxC : x ∈ C' := hfacet ▸ AffineRootSystem.mem_facet_self P.affineRoots x
  exact (hproducts hP C' x (-ν) ⟨x, hx, hfacet⟩ hxC hneg).2.1.2.2.2.2.2.1

end Langlands.Geometry.Building.ParahoricBuildingData

namespace Langlands.Geometry.Building

/-- The local reduction retains actual zero-subgroup normality and the
full chamber product statement as explicit intermediate premises. -/
def UnipotentNormalizerCosetReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.normalizerZero.Normal →
      P.ChamberIwahoriDecompositionStatement →
        P.apartment.SatisfiesApartmentAxioms P.centralizer →
          ∀ (C : Set P.Apartment) (ν : cocharacterLattice P.S),
            AffineRootSystem.IsChamber P.affineRoots C →
              IsGenericCocharacter P.i ν → P.UnipotentNormalizerCoset C ν

theorem unipotentNormalizerCosetReduction :
    UnipotentNormalizerCosetReductionStatement.{u} := by
  intro F _ _ _ _ G _ P hNormal hproducts hP C ν hC hν
  let := hNormal
  exact P.unipotentNormalizerCoset_of_chamberIwahori hproducts hP C ν hC hν

/-- Global assembly from the two separately owned statement conclusions;
the inputs remain explicit and are not proved by this reduction. -/
theorem unipotentNormalizerCosetStatement_of_chamberIwahori_and_exactSequence
    (hproducts : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
      [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
        P.ChamberIwahoriDecompositionStatement)
    (hsequence : IwahoriWeylExactSequenceStatement.{u}) :
    UnipotentNormalizerCosetStatement.{u} := by
  intro F _ _ _ _ G _ P _ _ hP C ν hC hν
  obtain ⟨hNormal, _, _⟩ := hsequence F G P hP
  let := hNormal
  exact P.unipotentNormalizerCoset_of_chamberIwahori (hproducts F G P) hP C ν hC hν

end Langlands.Geometry.Building
