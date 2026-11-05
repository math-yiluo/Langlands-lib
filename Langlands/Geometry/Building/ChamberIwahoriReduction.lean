import Langlands.Geometry.Building.ChamberIwahoriStatement
import Langlands.Geometry.Building.ChamberParahoricConstancy
import Langlands.Geometry.Building.KPParahoricProduct
import Langlands.Geometry.Building.CentralizerParahoricStatement
import Langlands.Geometry.Building.ChamberProductInjective
import Langlands.GroupScheme.Dynamic.Decomposition

/-!
# Reduction of the full chamber Iwahori decompositions

The full-parahoric conclusions of `ChamberIwahoriDecompositionStatement`
follow from the sharp statement `ChamberSharpDecompositionStatement` and the
centralizer intersection `CentralizerParahoricIntersectionStatement`
(KP Lemma 7.4.3), using the published injectivity of the full three-factor
product.
-/

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

/-- Conjugation by the image of a point of `Z = Z_G(S)` preserves the
dynamic unipotent of every cocharacter of `S`. -/
theorem map_centralizer_conj_mem_unipotent (c : cocharacterLattice P.S)
    (z : rationalPoints P.centralizer.Z) {u : rationalPoints G}
    (hu : u ∈ (Dynamic.unipotent (CommGroupScheme.groupHom c ≫ P.i)).carrier
      (Over.mk (𝟙 _))) :
    rationalPoints.map P.centralizer.j z * u * (rationalPoints.map P.centralizer.j z)⁻¹ ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom c ≫ P.i)).carrier (Over.mk (𝟙 _)) := by
  have hz : rationalPoints.map P.centralizer.j z ∈
      (Dynamic.centralizer (CommGroupScheme.groupHom c ≫ P.i)).carrier (Over.mk (𝟙 _)) :=
    torusCentralizer_le_dynamicCentralizer P.i (CommGroupScheme.groupHom c) _
      (by
        have hz0 := map_mem_centralizerPoints P.centralizer.isRepresentedBy z
        rw [← torusCentralizer_carrier_base P.i] at hz0
        exact hz0)
  exact Dynamic.conj_mem_unipotent _ (Dynamic.centralizer_le_parabolic _ _ hz) hu

/-- The sharp unipotent intersection lies in the full one. -/
theorem sharpUnipotentPoints_le_iwahoriUnipotentPoints (c : cocharacterLattice P.S)
    (C : Set P.Apartment) :
    P.apartment.sharpUnipotentPoints c C ≤ P.iwahoriUnipotentPoints c C :=
  inf_le_inf_left _ (P.sharpFixer_le_parahoric C)

/-- If the sharp product covers `G(F)^♯_C`, and `Z(F) ∩ I_C ⊆ Z(F)^0`, then
every element of `I_C` is a product of a sharp negative factor, an element
of `Z(F)^0` and a sharp positive factor. -/
theorem exists_sharpUnipotent_factorization {C : Set P.Apartment} {x : P.Apartment}
    {ν : cocharacterLattice P.S}
    (hfix : P.sharpFixer C = P.sharpFixer {x})
    (hrange : Set.range (P.apartment.sharpUnipotentProduct C x ν) =
      (P.sharpFixer C : Set (rationalPoints G)))
    (hZ : centralizerPoints P.i ⊓ P.chamberIwahori C ≤
      P.centralizerZero.map (rationalPoints.map P.centralizer.j))
    {g : rationalPoints G} (hg : g ∈ P.chamberIwahori C) :
    ∃ a ∈ P.apartment.sharpUnipotentPoints (-ν) C, ∃ z ∈ P.centralizerZero,
      ∃ b ∈ P.apartment.sharpUnipotentPoints ν C,
        a * rationalPoints.map P.centralizer.j z * b = g := by
  obtain ⟨z₀, hz₀, h, hh, rfl⟩ := P.mem_parahoric_iff.mp hg
  have hh' : h ∈ Set.range (P.apartment.sharpUnipotentProduct C x ν) := by
    rw [hrange]
    exact hh
  obtain ⟨⟨u, n, v⟩, rfl⟩ := hh'
  have hw : rationalPoints.map P.centralizer.j z₀ ∈
      P.centralizerZero.map (rationalPoints.map P.centralizer.j) := ⟨z₀, hz₀, rfl⟩
  have hn : rationalPoints.map P.centralizer.j z₀ * (n : rationalPoints G) ∈
      centralizerPoints P.i ⊓ P.chamberIwahori C := by
    refine ⟨Subgroup.mul_mem _
      (map_mem_centralizerPoints P.centralizer.isRepresentedBy z₀) n.property.1,
      Subgroup.mul_mem _ (P.map_centralizerZero_le_parahoric C hw)
        (P.sharpFixer_le_parahoric C ?_)⟩
    rw [hfix]
    exact n.property.2
  obtain ⟨z, hz, hzn⟩ := hZ hn
  refine ⟨rationalPoints.map P.centralizer.j z₀ * (u : rationalPoints G) *
      (rationalPoints.map P.centralizer.j z₀)⁻¹,
    ⟨P.map_centralizer_conj_mem_unipotent (-ν) z₀ u.property.1,
      (Subgroup.mem_normalizer_iff.mp
        (P.map_centralizerZero_le_normalizer_sharpFixer C hw) u).mp u.property.2⟩,
    z, hz, v, v.property, ?_⟩
  rw [hzn]
  simp only [KPApartmentData.sharpUnipotentProduct]
  group

/-- A factorization through sharp factors and injectivity of the full product
identify the full and sharp unipotent intersections, in both signs. -/
theorem iwahoriUnipotentPoints_eq_of_factorization {C : Set P.Apartment}
    {ν : cocharacterLattice P.S}
    (hinj : Function.Injective (P.iwahoriUnipotentProduct C ν))
    (hfac : ∀ g ∈ P.chamberIwahori C,
      ∃ a ∈ P.apartment.sharpUnipotentPoints (-ν) C, ∃ z ∈ P.centralizerZero,
        ∃ b ∈ P.apartment.sharpUnipotentPoints ν C,
          a * rationalPoints.map P.centralizer.j z * b = g) :
    P.iwahoriUnipotentPoints (-ν) C = P.apartment.sharpUnipotentPoints (-ν) C ∧
      P.iwahoriUnipotentPoints ν C = P.apartment.sharpUnipotentPoints ν C := by
  constructor
  · refine le_antisymm (fun u hu => ?_) (P.sharpUnipotentPoints_le_iwahoriUnipotentPoints _ C)
    obtain ⟨a, ha, z, hz, b, hb, hab⟩ := hfac u hu.2
    have h := @hinj
      (⟨a, P.sharpUnipotentPoints_le_iwahoriUnipotentPoints _ C ha⟩, ⟨z, hz⟩,
        ⟨b, P.sharpUnipotentPoints_le_iwahoriUnipotentPoints _ C hb⟩)
      (⟨u, hu⟩, 1, 1) (by simp [iwahoriUnipotentProduct, hab])
    have hau : a = u := congrArg (fun p => (p.1 : rationalPoints G)) h
    rw [← hau]
    exact ha
  · refine le_antisymm (fun u hu => ?_) (P.sharpUnipotentPoints_le_iwahoriUnipotentPoints _ C)
    obtain ⟨a, ha, z, hz, b, hb, hab⟩ := hfac u hu.2
    have h := @hinj
      (⟨a, P.sharpUnipotentPoints_le_iwahoriUnipotentPoints _ C ha⟩, ⟨z, hz⟩,
        ⟨b, P.sharpUnipotentPoints_le_iwahoriUnipotentPoints _ C hb⟩)
      (1, 1, ⟨u, hu⟩) (by simp [iwahoriUnipotentProduct, hab])
    have hbu : b = u := congrArg (fun p => (p.2.2 : rationalPoints G)) h
    rw [← hbu]
    exact hb

/-- A factorization through sharp factors gives the range of the full product. -/
theorem range_iwahoriUnipotentProduct_of_factorization {C : Set P.Apartment}
    {ν : cocharacterLattice P.S}
    (hfac : ∀ g ∈ P.chamberIwahori C,
      ∃ a ∈ P.apartment.sharpUnipotentPoints (-ν) C, ∃ z ∈ P.centralizerZero,
        ∃ b ∈ P.apartment.sharpUnipotentPoints ν C,
          a * rationalPoints.map P.centralizer.j z * b = g) :
    Set.range (P.iwahoriUnipotentProduct C ν) =
      (P.chamberIwahori C : Set (rationalPoints G)) := by
  ext g
  constructor
  · rintro ⟨⟨a, z, b⟩, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ a.property.2
      (P.map_centralizerZero_le_parahoric C ⟨z, z.property, rfl⟩)) b.property.2
  · intro hg
    obtain ⟨a, ha, z, hz, b, hb, rfl⟩ := hfac g hg
    exact ⟨(⟨a, P.sharpUnipotentPoints_le_iwahoriUnipotentPoints _ C ha⟩, ⟨z, hz⟩,
      ⟨b, P.sharpUnipotentPoints_le_iwahoriUnipotentPoints _ C hb⟩), rfl⟩

/-- Ordered negative/central/positive products built from injective maps onto
the full unipotent intersections are injective with range `I_C`, provided the
full product is. -/
theorem orderedTripleProduct_injective_range {X Y : Type*} {C : Set P.Apartment}
    {ν : cocharacterLattice P.S}
    (hinj : Function.Injective (P.iwahoriUnipotentProduct C ν))
    (hrange : Set.range (P.iwahoriUnipotentProduct C ν) =
      (P.chamberIwahori C : Set (rationalPoints G)))
    (f : X → rationalPoints G) (hf : Function.Injective f)
    (hfr : Set.range f = (P.iwahoriUnipotentPoints (-ν) C : Set (rationalPoints G)))
    (g : Y → rationalPoints G) (hg : Function.Injective g)
    (hgr : Set.range g = (P.iwahoriUnipotentPoints ν C : Set (rationalPoints G))) :
    Function.Injective (fun p : X × P.centralizerZero × Y =>
      f p.1 * rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
        g p.2.2) ∧
    Set.range (fun p : X × P.centralizerZero × Y =>
      f p.1 * rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
        g p.2.2) = (P.chamberIwahori C : Set (rationalPoints G)) := by
  have hfm (x : X) : f x ∈ P.iwahoriUnipotentPoints (-ν) C := by
    rw [← SetLike.mem_coe, ← hfr]
    exact ⟨x, rfl⟩
  have hgm (y : Y) : g y ∈ P.iwahoriUnipotentPoints ν C := by
    rw [← SetLike.mem_coe, ← hgr]
    exact ⟨y, rfl⟩
  let e : X × P.centralizerZero × Y →
      P.iwahoriUnipotentPoints (-ν) C × P.centralizerZero × P.iwahoriUnipotentPoints ν C :=
    fun p => (⟨f p.1, hfm p.1⟩, p.2.1, ⟨g p.2.2, hgm p.2.2⟩)
  have he : (fun p : X × P.centralizerZero × Y =>
      f p.1 * rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
        g p.2.2) = P.iwahoriUnipotentProduct C ν ∘ e := rfl
  have hes : Function.Surjective e := by
    rintro ⟨⟨a, ha⟩, z, ⟨b, hb⟩⟩
    have ha' : a ∈ Set.range f := by
      rw [hfr]
      exact ha
    have hb' : b ∈ Set.range g := by
      rw [hgr]
      exact hb
    obtain ⟨x, rfl⟩ := ha'
    obtain ⟨y, rfl⟩ := hb'
    exact ⟨(x, z, y), rfl⟩
  rw [he]
  refine ⟨hinj.comp ?_, by rw [hes.range_comp, hrange]⟩
  rintro ⟨x, z, y⟩ ⟨x', z', y'⟩ h
  simp only [e, Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [hf h1, h2, hg h3]

variable {P}

/-- The full chamber conclusion, from the sharp chamber conclusion, the
centralizer intersection at `C`, and injectivity of the full product. -/
theorem chamberIwahoriConclusion_of_sharp
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {C : Set P.Apartment} {x : P.Apartment} {ν : cocharacterLattice P.S}
    (hC : AffineRootSystem.IsChamber P.affineRoots C) (hx : x ∈ C)
    (hsharp : P.apartment.ChamberSharpConclusion C x ν)
    (hZ : centralizerPoints P.i ⊓ P.chamberIwahori C =
      P.centralizerZero.map (rationalPoints.map P.centralizer.j))
    (hinj : Function.Injective (P.iwahoriUnipotentProduct C ν)) :
    P.ChamberIwahoriConclusion C x ν := by
  obtain ⟨-, -, -, hrangeS, hordS⟩ := hsharp
  have hfix : P.sharpFixer C = P.sharpFixer {x} :=
    P.apartment.sharpFixer_eq_singleton_of_isFacet hD.mem_or_two_smul_mem hC.isFacet hx
  have hfac := fun g (hg : g ∈ P.chamberIwahori C) =>
    P.exists_sharpUnipotent_factorization (ν := ν) hfix hrangeS hZ.le hg
  obtain ⟨hneg, hpos⟩ := P.iwahoriUnipotentPoints_eq_of_factorization hinj hfac
  have hrange := P.range_iwahoriUnipotentProduct_of_factorization hfac
  refine ⟨P.chamberIwahori_eq_parahoricAt hD hC hx, hZ, hneg, hpos, hinj, hrange, ?_⟩
  intro strict nneg npos aneg apos ha hra hp hrp
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hordS strict nneg npos aneg apos ha hra hp hrp
  rw [← hneg] at h2
  rw [← hpos] at h4
  exact ⟨h1, h2, h3, h4,
    P.orderedTripleProduct_injective_range hinj hrange _ h1 h2 _ h3 h4⟩

/-- The full facet conclusion, from the sharp facet conclusion and the full
chamber unipotent identifications. -/
theorem chamberIwahoriFacetConclusion_of_sharp
    {Fa C : Set P.Apartment} {x : P.Apartment} {ν : cocharacterLattice P.S}
    (hfacet : P.apartment.ChamberSharpFacetConclusion Fa C x ν)
    (hneg : P.iwahoriUnipotentPoints (-ν) C = P.apartment.sharpUnipotentPoints (-ν) C)
    (hpos : P.iwahoriUnipotentPoints ν C = P.apartment.sharpUnipotentPoints ν C)
    (hinj : Function.Injective (P.iwahoriUnipotentProduct C ν))
    (hrange : Set.range (P.iwahoriUnipotentProduct C ν) =
      (P.chamberIwahori C : Set (rationalPoints G))) :
    P.ChamberIwahoriFacetConclusion Fa C ν := by
  intro nneg npos aneg apos ha hra hp hrp
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hfacet.2.2 nneg npos aneg apos ha hra hp hrp
  rw [← hneg] at h2
  rw [← hpos] at h4
  exact ⟨h1, h2, h3, h4,
    P.orderedTripleProduct_injective_range hinj hrange _ h1 h2 _ h3 h4⟩

/-- The full chamber Iwahori decompositions follow from the sharp ones and the
centralizer intersection of KP Lemma 7.4.3. -/
theorem chamberIwahoriDecomposition_of_sharp
    (hsharp : P.toValuationBuildingData.ChamberSharpDecompositionStatement)
    (hcent : P.CentralizerParahoricIntersectionStatement) :
    P.ChamberIwahoriDecompositionStatement := by
  intro hD C x ν hC hx hν
  obtain ⟨hS, hF⟩ := hsharp hD C x ν hC hx hν
  have hinj := P.iwahoriUnipotentProduct_injective C ν
  have hIw := chamberIwahoriConclusion_of_sharp hD hC hx hS (hcent hD C ⟨x, hx⟩) hinj
  obtain ⟨-, -, hneg, hpos, -, hrange, -⟩ := id hIw
  exact ⟨hS, hIw, fun Fa hFa hpsys => ⟨hF Fa hFa hpsys,
    chamberIwahoriFacetConclusion_of_sharp (hF Fa hFa hpsys) hneg hpos hinj hrange⟩⟩

end Langlands.Geometry.Building.ParahoricBuildingData

namespace Langlands.Geometry.Building

/-- The reduction keeps the sharp chamber statement and the centralizer
intersection statement as explicit premises for each actual datum. -/
def ChamberIwahoriReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.toValuationBuildingData.ChamberSharpDecompositionStatement →
      P.CentralizerParahoricIntersectionStatement →
        P.ChamberIwahoriDecompositionStatement

theorem chamberIwahoriReduction : ChamberIwahoriReductionStatement.{u} := by
  intro F _ _ _ _ G _ P hsharp hcent
  exact ParahoricBuildingData.chamberIwahoriDecomposition_of_sharp hsharp hcent

end Langlands.Geometry.Building
