import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.CrossTorusCentralizerCompatibility
import Langlands.Geometry.Building.SimplyConnectedImageNormal
import Langlands.BruhatTits.SpecialCompact.ApartmentCompactTransport

/-!
# Parahoric building data under based group isomorphisms

Let `f : G ≅ H` be an isomorphism of groups over a nonarchimedean local field and
`σ : S ≅ S'` an isomorphism of the maximal split torus of building data `B` for `G` with a torus
`i' : S' → H`, with `B.i ≫ f = σ ≫ i'`. This module carries `B` to building data for `H` with
torus exactly `i'`, and parahoric data along with it, and records the comparison of the reduced
buildings.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

namespace DatumTransport

/-! ### Tori -/

section Tori

variable {k : Type u} [Field k] {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The isomorphism of underlying group schemes of an isomorphism of commutative group
schemes. -/
def torusGrpIso (σ : T ≅ T') : T.toGrp ≅ T'.toGrp where
  hom := CommGroupScheme.groupHom σ.hom
  inv := CommGroupScheme.groupHom σ.inv
  hom_inv_id := congrArg Additive.toMul σ.hom_inv_id
  inv_hom_id := congrArg Additive.toMul σ.inv_hom_id

@[simp] theorem torusGrpIso_hom (σ : T ≅ T') :
    (torusGrpIso σ).hom = CommGroupScheme.groupHom σ.hom := rfl

@[simp] theorem torusGrpIso_inv (σ : T ≅ T') :
    (torusGrpIso σ).inv = CommGroupScheme.groupHom σ.inv := rfl

/-- Precomposing a maximal split torus with an isomorphism of tori gives a maximal split
torus. -/
theorem isMaximalSplitTorus_torusIso_comp {i : T'.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    (σ : T ≅ T') : IsMaximalSplitTorus (CommGroupScheme.groupHom σ.hom ≫ i) := by
  refine ⟨⟨IsSplitTorus.of_iso (torusGrpIso σ) hi.1.1,
    IsClosedSubgroup.iso_comp (torusGrpIso σ) hi.1.2⟩, ?_⟩
  intro T'' i' hi' g hg
  have hcomp : ((torusGrpIso σ).inv ≫ g) ≫ i' = i := by
    rw [Category.assoc, hg]
    exact (torusGrpIso σ).inv_hom_id_assoc i
  have := hi.2 T'' i' hi' _ hcomp
  have hg' : g = (torusGrpIso σ).hom ≫ ((torusGrpIso σ).inv ≫ g) :=
    ((torusGrpIso σ).hom_inv_id_assoc g).symm
  rw [hg']
  infer_instance

end Tori

/-! ### Rational points -/

section Points

variable {k : Type u} [CommRing k] {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- The isomorphism of rational points induced by `f : G ≅ H`. -/
def pointsEquiv (f : G ≅ H) : rationalPoints G ≃* rationalPoints H :=
  isoPointsEquiv f (Over.mk (𝟙 _))

@[simp] theorem pointsEquiv_apply (f : G ≅ H) (g : rationalPoints G) :
    pointsEquiv f g = rationalPoints.map f.hom g := rfl

@[simp] theorem pointsEquiv_symm_apply (f : G ≅ H) (g : rationalPoints H) :
    (pointsEquiv f).symm g = rationalPoints.map f.inv g := by
  apply (pointsEquiv f).injective
  rw [MulEquiv.apply_symm_apply]
  change g = (g ≫ f.inv.hom.hom) ≫ f.hom.hom.hom
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id]

theorem map_hom_map_inv (f : G ≅ H) (g : rationalPoints H) :
    rationalPoints.map f.hom (rationalPoints.map f.inv g) = g := by
  rw [← pointsEquiv_symm_apply, ← pointsEquiv_apply, MulEquiv.apply_symm_apply]

theorem map_inv_map_hom (f : G ≅ H) (g : rationalPoints G) :
    rationalPoints.map f.inv (rationalPoints.map f.hom g) = g := by
  rw [← pointsEquiv_symm_apply, ← pointsEquiv_apply, MulEquiv.symm_apply_apply]

theorem map_comp_apply {K : GroupScheme (Spec (CommRingCat.of k))} (a : G ⟶ H) (b : H ⟶ K)
    (g : rationalPoints G) :
    rationalPoints.map (a ≫ b) g = rationalPoints.map b (rationalPoints.map a g) := by
  change g ≫ (a ≫ b).hom.hom = (g ≫ a.hom.hom) ≫ b.hom.hom
  rw [Grp.comp_hom_hom, Category.assoc]

theorem map_comp_eq {K : GroupScheme (Spec (CommRingCat.of k))} (a : G ⟶ H) (b : H ⟶ K) :
    rationalPoints.map (a ≫ b) = (rationalPoints.map b).comp (rationalPoints.map a) :=
  MonoidHom.ext (map_comp_apply a b)

theorem subgroup_map_comp {K : GroupScheme (Spec (CommRingCat.of k))} (a : G ⟶ H) (b : H ⟶ K)
    (L : Subgroup (rationalPoints G)) :
    L.map (rationalPoints.map (a ≫ b)) = (L.map (rationalPoints.map a)).map
      (rationalPoints.map b) := by
  rw [map_comp_eq, Subgroup.map_map]

theorem mem_map_iff (f : G ≅ H) (L : Subgroup (rationalPoints G)) (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈ L.map (rationalPoints.map f.hom) ↔ g ∈ L :=
  Subgroup.mem_map_iff_mem (pointsEquiv f).injective

theorem map_injective (f : G ≅ H) :
    Function.Injective (Subgroup.map (rationalPoints.map f.hom)) := by
  intro K L hKL
  ext g
  rw [← mem_map_iff f K g, ← mem_map_iff f L g, hKL]

end Points

end DatumTransport

open DatumTransport

/-! ### The centralizer and the zero-subgroup data -/

section Centralizer

variable {F : Type u} [Field F]
  {S S' : CommGroupScheme (Spec (CommRingCat.of F))}
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
  (e : S ≅ S') (f : G ≅ H) (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

include h in
/-- The target torus is the source torus transported by both isomorphisms. -/
theorem DatumTransport.target_eq : j = CommGroupScheme.groupHom e.inv ≫ i ≫ f.hom := by
  rw [h, ← Category.assoc]
  change j = CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ j
  rw [Iso.inv_hom_id]
  exact (Category.id_comp j).symm

/-- Restriction-evaluation after an isomorphism of tori. -/
theorem DatumTransport.restrictionEvaluation_torusIso {Z : GroupScheme (Spec (CommRingCat.of F))}
    (s : S.toGrp ⟶ Z) :
    BruhatTits.Cartan.restrictionEvaluation (CommGroupScheme.groupHom e.inv ≫ s) =
      (BruhatTits.Cartan.restrictionEvaluation s).comp
        (cocharacterRealCongr e).symm.toLinearMap := by
  apply LinearMap.ext
  intro v
  apply AddMonoidHom.ext
  intro χ
  obtain ⟨w, rfl⟩ := (cocharacterRealCongr e).surjective v
  change eval S' (BruhatTits.Cartan.characterRestriction (CommGroupScheme.groupHom e.inv ≫ s) χ)
      (cocharacterRealCongr e w) =
    eval S (BruhatTits.Cartan.characterRestriction s χ)
      ((cocharacterRealCongr e).symm (cocharacterRealCongr e w))
  rw [LinearEquiv.symm_apply_apply, ← eval_cocharacterRealCongr e]
  rfl

/-- The actual centralizer, with its inclusion composed with `f` and its torus factorization
precomposed with `σ⁻¹`. -/
def CentralizerDatum.basedTransport (C : CentralizerDatum i) : CentralizerDatum j where
  Z := C.Z
  j := C.j ≫ f.hom
  s := CommGroupScheme.groupHom e.inv ≫ C.s
  isClosedSubgroup := C.isClosedSubgroup.comp_iso f
  isRepresentedBy := C.isRepresentedBy.torusCentralizer_of_iso_square (torusGrpIso e) f h
  comp_eq := by
    rw [Category.assoc, ← Category.assoc C.s, C.comp_eq, target_eq e f h]
  bijective := by
    rw [restrictionEvaluation_torusIso]
    exact C.bijective.comp (cocharacterRealCongr e).symm.bijective

@[simp] theorem CentralizerDatum.basedTransport_Z (C : CentralizerDatum i) :
    (C.basedTransport e f h).Z = C.Z := rfl

@[simp] theorem CentralizerDatum.basedTransport_j (C : CentralizerDatum i) :
    (C.basedTransport e f h).j = C.j ≫ f.hom := rfl

end Centralizer

section ZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S S' : CommGroupScheme (Spec (CommRingCat.of F))}
  {G H Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H} {jZ : Z ⟶ G}
  (e : S ≅ S') (f : G ≅ H) (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

/-- The data of KP Definition 2.6.23 transported along `f`: the same centralizer data for
`Z_K`, the same derived subgroup and simply connected cover, with the derived inclusion
composed with `f`. -/
def ZeroSubgroupDatum.basedTransport (E : ZeroSubgroupDatum i jZ) :
    ZeroSubgroupDatum j (jZ ≫ f.hom) where
  isMaximalSplitTorus := by
    rw [target_eq e f h]
    exact isMaximalSplitTorus_torusIso_comp (E.isMaximalSplitTorus.comp_iso f) e.symm
  isRepresentedBy := E.isRepresentedBy.torusCentralizer_of_iso_square (torusGrpIso e) f h
  centralizerDatum := E.centralizerDatum
  D := E.D
  C := E.C
  d := E.d ≫ f.hom
  π := E.π
  isSimplyConnectedDerivedCover :=
    ⟨E.isSimplyConnectedDerivedCover.isConnectedReductive.of_iso f.symm,
      E.isSimplyConnectedDerivedCover.isDerivedSubgroup.comp_iso f,
      E.isSimplyConnectedDerivedCover.isSimplyConnectedCover⟩

theorem ZeroSubgroupDatum.basedTransport_centralizerZero (E : ZeroSubgroupDatum i jZ) :
    (E.basedTransport e f h).centralizerZero = E.centralizerZero := rfl

theorem ZeroSubgroupDatum.basedTransport_simplyConnectedImage (E : ZeroSubgroupDatum i jZ) :
    (E.basedTransport e f h).simplyConnectedImage =
      E.simplyConnectedImage.map (rationalPoints.map f.hom) :=
  (map_simplyConnectedImage_eq E.isSimplyConnectedDerivedCover
    (E.basedTransport e f h).isSimplyConnectedDerivedCover f).symm

/-- `G(F)^0` is carried onto `H(F)^0`. -/
theorem ZeroSubgroupDatum.basedTransport_zeroSubgroup (E : ZeroSubgroupDatum i jZ) :
    (E.basedTransport e f h).zeroSubgroup = E.zeroSubgroup.map (rationalPoints.map f.hom) := by
  rw [ZeroSubgroupDatum.zeroSubgroup, ZeroSubgroupDatum.zeroSubgroup, Subgroup.map_sup,
    E.basedTransport_simplyConnectedImage e f h, E.basedTransport_centralizerZero e f h,
    subgroup_map_comp]

end ZeroDatum

end Langlands.Geometry.Building
