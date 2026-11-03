import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.Geometry.Building.ValuationBuildingData

/-!
# Parahoric and Iwahori subgroups

Let `F` be a nonarchimedean local field and `G` a connected reductive `F`-group.
`ParahoricBuildingData G` extends the building data `ValuationBuildingData G` (a maximal split
torus `S`, the class `A(S)` of valuations of the root datum, and the centralizer
`Z = Z_G(S)`) by the data of KP Definition 2.6.23 for `Z(F)^0` and `G(F)^0`, relative to the
same `S` and `Z`. For a subset `Ω` of the apartment it defines

* `P_Ω = G(F)^0_Ω = Z(F)^0 · G(F)^♯_Ω` (KP Definition 7.4.1(4)), with `P_x = P_{x}`;
* `N^0_Ω = N(F) ∩ G(F)^0_Ω` (KP Definition 7.4.1(5));
* the parahoric subgroup `P_F` of a facet `F` and the Iwahori subgroup `P_C` of a chamber `C`
  of the apartment, and the parahoric and Iwahori subgroups of `G(F)`, their `G(F)`-conjugates
  (KP Definition 7.4.5);
* the parahoric subgroups of points of the reduced building, as conjugates `g P_x g⁻¹`.

`P_x`, `K_x = G(F)^1 ∩ G(F)_x` (`compactStabilizer`) and the full fixer `G(F)_x` (`fixer`) are
distinct definitions; no relation among them beyond the definitions is asserted.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]

/-- Building data for `G` (`ValuationBuildingData G`) together with the data of KP
Definition 2.6.23 for `G(F)^0`, relative to the same maximal split torus `i : S → G` and the
same centralizer `j : Z → G`. -/
structure ParahoricBuildingData extends ValuationBuildingData G where
  /-- Data for `Z(F)^0` and `G(F)^0` (KP Definition 2.6.23) relative to `S` and `Z = Z_G(S)`. -/
  zeroDatum : ZeroSubgroupDatum i centralizer.j

namespace ParahoricBuildingData

variable {G} (P : ParahoricBuildingData G)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] in
/-- `Q.map (MulAut.conj g).toMonoidHom` is `g Q g⁻¹`. Conjugating by `g` and then by `h` is
conjugating by `h * g`. -/
theorem map_conj_map_conj (Q : Subgroup (rationalPoints G)) (g h : rationalPoints G) :
    (Q.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      Q.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] in
theorem map_conj_one (Q : Subgroup (rationalPoints G)) :
    Q.map (MulAut.conj (1 : rationalPoints G)).toMonoidHom = Q := by
  ext x
  simp

/-! ### `Z(F)^0`, `G(F)^0` and `G(F)^1` -/

/-- The Iwahori subgroup `Z(F)^0` of `Z(F)`, `Z = Z_G(S)` (KP Definition 2.6.23(2)). -/
abbrev centralizerZero : Subgroup (rationalPoints P.centralizer.Z) :=
  P.zeroDatum.centralizerZero

/-- `G(F)^♮`, the image of `G_sc(F) → G(F)` (KP Definition 2.6.20). -/
abbrev simplyConnectedImage : Subgroup (rationalPoints G) :=
  P.zeroDatum.simplyConnectedImage

/-- `G(F)^0 = G(F)^♮ · Z(F)^0` (KP Definition 2.6.23(3)). -/
abbrev zeroSubgroup : Subgroup (rationalPoints G) :=
  P.zeroDatum.zeroSubgroup

/-- `G(F)^1`, the kernel of the valuation homomorphism `ω_G` (KP 2.6(d)): the elements `g`
with `|χ(g)| = 1` for every rational character `χ`. -/
abbrev normOneSubgroup : Subgroup (rationalPoints G) :=
  rationalCommonNormKernel G

/-! ### `P_Ω = G(F)^0_Ω` -/

/-- `P_Ω = G(F)^0_Ω = Z(F)^0 · G(F)^♯_Ω` for `Ω ⊆ A(S)` (KP Definition 7.4.1(4)). -/
def parahoric (Ω : Set P.Apartment) : Subgroup (rationalPoints G) :=
  P.centralizerZero.map (rationalPoints.map P.centralizer.j) ⊔ P.sharpFixer Ω

/-- `P_x = G(F)^0_x = G(F)^0_{x}` for a point `x` of the apartment (KP Definition 7.4.1). -/
abbrev parahoricAt (x : P.Apartment) : Subgroup (rationalPoints G) :=
  P.parahoric {x}

theorem map_centralizerZero_le_parahoric (Ω : Set P.Apartment) :
    P.centralizerZero.map (rationalPoints.map P.centralizer.j) ≤ P.parahoric Ω :=
  le_sup_left

theorem sharpFixer_le_parahoric (Ω : Set P.Apartment) : P.sharpFixer Ω ≤ P.parahoric Ω :=
  le_sup_right

theorem rootFixer_le_parahoric (a : relativeRoots P.i) (Ω : Set P.Apartment) :
    P.rootFixer a Ω ≤ P.parahoric Ω :=
  (P.apartment.rootFixer_le_sharpFixer a Ω).trans (P.sharpFixer_le_parahoric Ω)

theorem parahoric_anti {Ω Ω' : Set P.Apartment} (h : Ω ⊆ Ω') :
    P.parahoric Ω' ≤ P.parahoric Ω :=
  sup_le_sup_left (P.apartment.sharpFixer_anti h) _

/-- `N^0_Ω = N(F) ∩ G(F)^0_Ω` (KP Definition 7.4.1(5)). -/
def zeroNormalizer (Ω : Set P.Apartment) : Subgroup (rationalPoints G) :=
  normalizerPoints P.i ⊓ P.parahoric Ω

/-! ### Parahoric and Iwahori subgroups (KP Definition 7.4.5) -/

/-- A subgroup of `G(F)` is parahoric if it is a `G(F)`-conjugate of `P_F` for a facet `F` of
the apartment (KP Definition 7.4.5(1), (3)). -/
def IsParahoricSubgroup (Q : Subgroup (rationalPoints G)) : Prop :=
  ∃ (g : rationalPoints G) (Fa : Set P.Apartment),
    AffineRootSystem.IsFacet P.affineRoots Fa ∧
      Q = (P.parahoric Fa).map (MulAut.conj g).toMonoidHom

/-- A subgroup of `G(F)` is Iwahori if it is a `G(F)`-conjugate of `P_C` for a chamber `C` of
the apartment (KP Definition 7.4.5(2), (4)). -/
def IsIwahoriSubgroup (Q : Subgroup (rationalPoints G)) : Prop :=
  ∃ (g : rationalPoints G) (Ca : Set P.Apartment),
    AffineRootSystem.IsChamber P.affineRoots Ca ∧
      Q = (P.parahoric Ca).map (MulAut.conj g).toMonoidHom

theorem isParahoricSubgroup_parahoric {Fa : Set P.Apartment}
    (h : AffineRootSystem.IsFacet P.affineRoots Fa) : P.IsParahoricSubgroup (P.parahoric Fa) :=
  ⟨1, Fa, h, (map_conj_one _).symm⟩

theorem isIwahoriSubgroup_parahoric {Ca : Set P.Apartment}
    (h : AffineRootSystem.IsChamber P.affineRoots Ca) : P.IsIwahoriSubgroup (P.parahoric Ca) :=
  ⟨1, Ca, h, (map_conj_one _).symm⟩

theorem IsParahoricSubgroup.conj {Q : Subgroup (rationalPoints G)}
    (hQ : P.IsParahoricSubgroup Q) (h : rationalPoints G) :
    P.IsParahoricSubgroup (Q.map (MulAut.conj h).toMonoidHom) := by
  obtain ⟨g, Fa, hF, rfl⟩ := hQ
  exact ⟨h * g, Fa, hF, map_conj_map_conj _ g h⟩

theorem IsIwahoriSubgroup.conj {Q : Subgroup (rationalPoints G)}
    (hQ : P.IsIwahoriSubgroup Q) (h : rationalPoints G) :
    P.IsIwahoriSubgroup (Q.map (MulAut.conj h).toMonoidHom) := by
  obtain ⟨g, Ca, hC, rfl⟩ := hQ
  exact ⟨h * g, Ca, hC, map_conj_map_conj _ g h⟩

/-- Every chamber is a facet, so every Iwahori subgroup is parahoric. -/
theorem IsIwahoriSubgroup.isParahoricSubgroup {Q : Subgroup (rationalPoints G)}
    (hQ : P.IsIwahoriSubgroup Q) : P.IsParahoricSubgroup Q := by
  obtain ⟨g, Ca, ⟨x, -, hx⟩, rfl⟩ := hQ
  exact ⟨g, Ca, ⟨x, hx⟩, rfl⟩

/-! ### Parahoric subgroups of points of the building -/

/-- `Q` is a parahoric subgroup of the point `y` of the reduced building: `Q = g P_x g⁻¹` for
some `g ∈ G(F)` and some point `x` of the apartment with `y = g · x`. -/
def IsParahoricAt (y : P.ReducedBuilding) (Q : Subgroup (rationalPoints G)) : Prop :=
  ∃ (g : rationalPoints G) (x : P.Apartment),
    g • P.apartmentMap x = y ∧ Q = (P.parahoricAt x).map (MulAut.conj g).toMonoidHom

theorem isParahoricAt_apartmentMap (x : P.Apartment) :
    P.IsParahoricAt (P.apartmentMap x) (P.parahoricAt x) :=
  ⟨1, x, one_smul _ _, (map_conj_one _).symm⟩

theorem IsParahoricAt.smul {y : P.ReducedBuilding} {Q : Subgroup (rationalPoints G)}
    (hQ : P.IsParahoricAt y Q) (h : rationalPoints G) :
    P.IsParahoricAt (h • y) (Q.map (MulAut.conj h).toMonoidHom) := by
  obtain ⟨g, x, rfl, rfl⟩ := hQ
  exact ⟨h * g, x, mul_smul h g _, map_conj_map_conj _ g h⟩

end ParahoricBuildingData

end Langlands.Geometry.Building
