import Langlands.Geometry.Building.KPApartment
import Langlands.Geometry.Building.ApartmentQuotient
import Langlands.Geometry.Building.AffineRootSystem
import Langlands.Representation.Plancherel.RationalCharacterValuation

/-!
# The reduced building, sharp fixers and compact stabilizers of valid apartment data

For valid apartment data `D : KPApartmentData i ω` this module defines:

* the conjugation law `n U_a(k) n⁻¹ = U_{n·a}(k)` for the actual root groups and `n ∈ N(k)`;
* the groups `U_{a,Ω,0}`, `G(k)^♯_Ω`, `N^♯_Ω` and `Z^♯_Ω` of KP Definition 7.4.1;
* the reduced building `D.ReducedBuilding`, the quotient of `G(k) × A` by the relation (7.6.2)
  of KP Remark 7.6.5, with its `G(k)`-action and the `N(k)`-equivariant map `D.apartmentMap`;
* the full fixer `D.reducedFixer y` of a point and the pointwise fixer of a subset;
* special points of the reduced building, from KP Definition 1.3.39 on the apartment;
* over a nonarchimedean local field, `K_y = G(F)^1 ∩ G(F)_y` (KP Theorem 4.2.15).

The parahoric subgroups `P_Ω = Z(k)^0 · G(k)^♯_Ω` need the actual `Z(k)^0` of KP
Definition 2.6.23, which is not available; they are not defined here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

section General

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

section Conjugation

variable {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- `n U_a(k) n⁻¹ ⊆ U_{n·a}(k)` for the actual root groups and `n ∈ N(k)`. -/
theorem conj_mem_rootGroupPoints (n : normalizerPoints i) {a : characterLattice S}
    {u : rationalPoints G} (hu : u ∈ rootGroupPoints i a) :
    (n : rationalPoints G) * u * (n : rationalPoints G)⁻¹ ∈
      rootGroupPoints i (weylAction i n a) := by
  obtain ⟨e, he, he0⟩ := hu
  have hσ := (isNormalizingPoint_normalizingAut i n).inv
  refine ⟨G.constantPoint n (Over.mk (𝟙 _) ⊗ AffineLine.scheme _) * e *
    (G.constantPoint n (Over.mk (𝟙 _) ⊗ AffineLine.scheme _))⁻¹, ?_, ?_⟩
  · -- conjugation by `n⁻¹` on `i`, evaluated at any point of `S`
    have hconj : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ S.X),
        x ≫ (CommGroupScheme.groupHom (normalizingAut i n).inv).hom.hom ≫ i.hom.hom =
          (G.constantPoint (n : rationalPoints G) V)⁻¹ * (x ≫ i.hom.hom) *
            G.constantPoint (n : rationalPoints G) V := by
      intro V x
      have h := congrArg (fun f : S.toGrp ⟶ G => x ≫ f.hom.hom) hσ
      simp only [Grp.comp_hom_hom, ← Category.assoc, Iso.symm_hom] at h
      rw [← Category.assoc, ← h, comp_innerIso_hom G _ V (x ≫ i.hom.hom), constantPoint_inv, inv_inv]
    rw [RelativeRoot.IsOrbitExtension, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
      constantPoint_naturality, weylAction_apply]
    have hw : Over.mk (𝟙 (Spec (CommRingCat.of k))) ◁
        ((CommGroupScheme.groupHom ((normalizingAut i n).inv ≫ a)).hom.hom ≫
          AffineLine.unitInclusion _) =
        Over.mk (𝟙 (Spec (CommRingCat.of k))) ◁
            (CommGroupScheme.groupHom (normalizingAut i n).inv).hom.hom ≫
          Over.mk (𝟙 (Spec (CommRingCat.of k))) ◁
            ((CommGroupScheme.groupHom a).hom.hom ≫ AffineLine.unitInclusion _) := by
      rw [← MonoidalCategory.whiskerLeft_comp]
      rfl
    rw [hw, Category.assoc, he]
    simp only [RelativeRoot.orbit, AutomorphicAction.conjugation_act, MonObj.comp_mul,
      GrpObj.comp_inv, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hconj]
    rw [← constantPoint_naturality G (n : rationalPoints G) (fst _ S.X),
      constantPoint_self]
    group
  · rw [Dynamic.evalZero_mul, Dynamic.evalZero_mul, Dynamic.evalZero_inv, he0, mul_one,
      mul_inv_cancel]

theorem weylAction_inv_apply_apply (n : normalizerPoints i) (a : characterLattice S) :
    weylAction i n⁻¹ (weylAction i n a) = a := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem weylAction_apply_inv_apply (n : normalizerPoints i) (a : characterLattice S) :
    weylAction i n (weylAction i n⁻¹ a) = a := by
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- `n U_a(k) n⁻¹ = U_{n·a}(k)` for `n ∈ N(k)`. -/
theorem conj_rootGroupPoints (n : normalizerPoints i) (a : characterLattice S) :
    (rootGroupPoints i a).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
      rootGroupPoints i (weylAction i n a) := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact conj_mem_rootGroupPoints n hu
  · intro u hu
    refine ⟨(n : rationalPoints G)⁻¹ * u * (n : rationalPoints G), ?_, ?_⟩
    · have h := conj_mem_rootGroupPoints n⁻¹ hu
      rwa [weylAction_inv_apply_apply, Subgroup.coe_inv, inv_inv] at h
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

end Conjugation

namespace KPApartmentData

variable {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}
  (D : KPApartmentData i ω)

/-- `n U_{a,x,r} n⁻¹ ⊆ U_{n·a,nx,r}` for `n ∈ N(k)` (KP 6.1.8 and Fact 6.3.3). -/
theorem conj_mem_filtration (n : normalizerPoints i) {x : D.Apartment} {a : characterLattice S}
    {r : ℝ} {u : rationalPoints G} (hu : u ∈ D.filtration x a r) :
    (n : rationalPoints G) * u * (n : rationalPoints G)⁻¹ ∈
      D.filtration (n • x) (weylAction i n a) r := by
  rw [mem_filtration] at hu ⊢
  refine ⟨conj_mem_rootGroupPoints n hu.1, ?_⟩
  have hu' : (n : rationalPoints G)⁻¹ * ((n : rationalPoints G) * u * (n : rationalPoints G)⁻¹) *
      (n : rationalPoints G) = u := by
    group
  rw [val_smul, RootFunctionFamily.smul_apply, weylAction_inv_apply_apply, hu']
  exact hu.2

/-! ### Sharp fixers (KP Definition 7.4.1) -/

/-- `U_{a,Ω,0} = ⋂_{x ∈ Ω} U_{a,x,0}` (KP Definition 7.4.1(1)), intersected with `U_a(k)` so
that it is `U_a(k)` for empty `Ω`. -/
def rootFixer (a : characterLattice S) (Ω : Set D.Apartment) : Subgroup (rationalPoints G) :=
  rootGroupPoints i a ⊓ ⨅ x ∈ Ω, D.filtration x a 0

theorem mem_rootFixer {a : characterLattice S} {Ω : Set D.Apartment} {u : rationalPoints G} :
    u ∈ D.rootFixer a Ω ↔ u ∈ rootGroupPoints i a ∧ ∀ x ∈ Ω, u ∈ D.filtration x a 0 := by
  simp only [rootFixer, Subgroup.mem_inf, Subgroup.mem_iInf]

theorem rootFixer_singleton (a : characterLattice S) (x : D.Apartment) :
    D.rootFixer a {x} = D.filtration x a 0 := by
  ext u
  rw [mem_rootFixer, Set.forall_mem_singleton]
  exact ⟨fun h => h.2, fun h => ⟨D.filtration_le_rootGroupPoints x a 0 h, h⟩⟩

theorem rootFixer_anti (a : characterLattice S) {Ω Ω' : Set D.Apartment} (h : Ω ⊆ Ω') :
    D.rootFixer a Ω' ≤ D.rootFixer a Ω := fun _ hu =>
  D.mem_rootFixer.2 ⟨(D.mem_rootFixer.1 hu).1, fun x hx => (D.mem_rootFixer.1 hu).2 x (h hx)⟩

/-- `G(k)^♯_Ω`, the subgroup of `G(k)` generated by the `U_{a,Ω,0}` for `a ∈ Φ`
(KP Definition 7.4.1(2)). -/
def sharpFixer (Ω : Set D.Apartment) : Subgroup (rationalPoints G) :=
  ⨆ α : relativeRoots i, D.rootFixer α Ω

theorem sharpFixer_eq_closure (Ω : Set D.Apartment) :
    D.sharpFixer Ω = Subgroup.closure (⋃ α : relativeRoots i, (D.rootFixer α Ω : Set _)) :=
  Subgroup.iSup_eq_closure _

theorem rootFixer_le_sharpFixer (α : relativeRoots i) (Ω : Set D.Apartment) :
    D.rootFixer α Ω ≤ D.sharpFixer Ω :=
  le_iSup (fun β : relativeRoots i => D.rootFixer β Ω) α

theorem sharpFixer_anti {Ω Ω' : Set D.Apartment} (h : Ω ⊆ Ω') :
    D.sharpFixer Ω' ≤ D.sharpFixer Ω :=
  iSup_mono fun α => D.rootFixer_anti α h

/-- `N^♯_Ω = N(k) ∩ G(k)^♯_Ω` (KP Definition 7.4.1(3)). -/
def sharpNormalizer (Ω : Set D.Apartment) : Subgroup (rationalPoints G) :=
  normalizerPoints i ⊓ D.sharpFixer Ω

/-- `Z^♯_Ω = Z(k) ∩ G(k)^♯_Ω` (KP Definition 7.4.1(3)). -/
def sharpCentralizer (Ω : Set D.Apartment) : Subgroup (rationalPoints G) :=
  centralizerPoints i ⊓ D.sharpFixer Ω

/-- `n G(k)^♯_Ω n⁻¹ ⊆ G(k)^♯_{nΩ}` for `n ∈ N(k)`. -/
theorem sharpFixer_le_comap (n : normalizerPoints i) (Ω : Set D.Apartment) :
    D.sharpFixer Ω ≤
      (D.sharpFixer (n • Ω)).comap (MulAut.conj (n : rationalPoints G)).toMonoidHom := by
  refine iSup_le fun α u hu => ?_
  rw [mem_rootFixer] at hu
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine D.rootFixer_le_sharpFixer
    ⟨weylAction i n α, weylAction_mapsTo_relativeRoots i n α.2⟩ (n • Ω) ?_
  rw [mem_rootFixer]
  refine ⟨conj_mem_rootGroupPoints n hu.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact D.conj_mem_filtration n (hu.2 x hx)

/-! ### The reduced building (KP (7.6.2)) -/

/-- The `N(k)`-covariant family `x ↦ G(k)^♯_x` of subgroups of `G(k)`. -/
def sharpFixerFamily : CovariantSubgroupFamily (normalizerPoints i) D.Apartment where
  toFun x := D.sharpFixer {x}
  isConjCovariant n x p hp := by
    have h := D.sharpFixer_le_comap n {x} hp
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Set.smul_set_singleton] at h

/-- The reduced building `B(G) = G(k) × A / ∼` with `(g, x) ∼ (h, y)` iff `nx = y` and
`g⁻¹ h n ∈ G(k)^♯_x` for some `n ∈ N(k)` (KP Remark 7.6.5, (7.6.2)). -/
def ReducedBuilding : Type u :=
  ApartmentQuotient D.sharpFixerFamily

instance : MulAction (rationalPoints G) D.ReducedBuilding :=
  inferInstanceAs (MulAction (rationalPoints G) (ApartmentQuotient D.sharpFixerFamily))

/-- The map `A → B(G)`, `x ↦ [(1, x)]`. -/
def apartmentMap (x : D.Apartment) : D.ReducedBuilding :=
  ApartmentQuotient.apartment D.sharpFixerFamily x

/-- The apartment map is `N(k)`-equivariant. -/
theorem apartmentMap_smul (n : normalizerPoints i) (x : D.Apartment) :
    D.apartmentMap (n • x) = (n : rationalPoints G) • D.apartmentMap x :=
  ApartmentQuotient.apartment_smul _ n x

/-- Every point of the building is a `G(k)`-translate of a point of the apartment. -/
theorem exists_smul_apartmentMap (y : D.ReducedBuilding) :
    ∃ (g : rationalPoints G) (x : D.Apartment), g • D.apartmentMap x = y :=
  ApartmentQuotient.exists_smul_apartment _ y

theorem apartmentMap_eq_apartmentMap_iff (x y : D.Apartment) :
    D.apartmentMap x = D.apartmentMap y ↔
      ∃ n : normalizerPoints i, n • x = y ∧ (n : rationalPoints G) ∈ D.sharpFixer {x} :=
  ApartmentQuotient.apartment_eq_apartment_iff _ x y

/-! ### Fixers -/

/-- The full fixer `G(k)_y` of a point `y` of the reduced building: its stabilizer in `G(k)`. -/
def reducedFixer (y : D.ReducedBuilding) : Subgroup (rationalPoints G) :=
  MulAction.stabilizer (rationalPoints G) y

theorem mem_reducedFixer {y : D.ReducedBuilding} {g : rationalPoints G} :
    g ∈ D.reducedFixer y ↔ g • y = y :=
  MulAction.mem_stabilizer_iff

theorem sharpFixer_le_reducedFixer (x : D.Apartment) :
    D.sharpFixer {x} ≤ D.reducedFixer (D.apartmentMap x) :=
  ApartmentQuotient.le_stabilizer_apartment D.sharpFixerFamily x

/-- `G(k)_x = G(k)^♯_x · N(k)_x` for `x ∈ A`. -/
theorem reducedFixer_apartmentMap (x : D.Apartment) :
    D.reducedFixer (D.apartmentMap x) =
      D.sharpFixer {x} ⊔
        (MulAction.stabilizer (normalizerPoints i) x).map (normalizerPoints i).subtype :=
  ApartmentQuotient.stabilizer_apartment_eq_sup D.sharpFixerFamily x

theorem reducedFixer_smul (g : rationalPoints G) (y : D.ReducedBuilding) :
    D.reducedFixer (g • y) = (D.reducedFixer y).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g y

/-- The pointwise fixer in `G(k)` of a subset of the reduced building. -/
def pointwiseFixer (Y : Set D.ReducedBuilding) : Subgroup (rationalPoints G) :=
  fixingSubgroup (rationalPoints G) Y

theorem mem_pointwiseFixer {Y : Set D.ReducedBuilding} {g : rationalPoints G} :
    g ∈ D.pointwiseFixer Y ↔ ∀ y ∈ Y, g • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun hg y => hg y y.2⟩

theorem pointwiseFixer_singleton (y : D.ReducedBuilding) :
    D.pointwiseFixer {y} = D.reducedFixer y := by
  ext g
  rw [mem_pointwiseFixer, mem_reducedFixer, Set.forall_mem_singleton]

/-! ### Special points -/

/-- A point of the reduced building is special if it is a `G(k)`-translate of the image of a
special point of the apartment (KP Definition 1.3.39 for `Ψ = D.affineRoots`), that is, if it
is special in some apartment `g · A` containing it. -/
def IsSpecialBuildingPoint (y : D.ReducedBuilding) : Prop :=
  ∃ (g : rationalPoints G) (x : D.Apartment), g • D.apartmentMap x = y ∧
    AffineRootSystem.IsSpecialPoint D.affineRoots x

theorem isSpecialBuildingPoint_apartmentMap {x : D.Apartment}
    (hx : AffineRootSystem.IsSpecialPoint D.affineRoots x) :
    D.IsSpecialBuildingPoint (D.apartmentMap x) :=
  ⟨1, x, one_smul _ _, hx⟩

theorem IsSpecialBuildingPoint.smul {y : D.ReducedBuilding} (hy : D.IsSpecialBuildingPoint y)
    (g : rationalPoints G) : D.IsSpecialBuildingPoint (g • y) := by
  obtain ⟨h, x, rfl, hx⟩ := hy
  exact ⟨g * h, x, mul_smul g h _, hx⟩

end KPApartmentData

end General

/-! ### Local fields: `G(F)^1` and `K_x` -/

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

variable (F) in
/-- The normalized valuation `ω = ord : Fˣ → ℤ ⊆ ℝ` of a nonarchimedean local field, the
published `fieldOrderUnits` (positive on the maximal ideal). -/
def localFieldOrder (t : Fˣ) : ℝ :=
  ((Plancherel.fieldOrderUnits F t).toAdd : ℝ)

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  [IsAffineHom G.X.hom]

namespace KPApartmentData

variable (D : KPApartmentData i (localFieldOrder F))

/-- `K_y = G(F)^1 ∩ G(F)_y`, the stabilizer in `G(F)^1` of a point `y` of the reduced
building (KP Theorem 4.2.15, `G(k)^1_x`). `G(F)^1` is the published
`Plancherel.rationalCommonNormKernel G`. -/
def compactStabilizer (y : D.ReducedBuilding) : Subgroup (rationalPoints G) :=
  Plancherel.rationalCommonNormKernel G ⊓ D.reducedFixer y

theorem mem_compactStabilizer {y : D.ReducedBuilding} {g : rationalPoints G} :
    g ∈ D.compactStabilizer y ↔ g ∈ Plancherel.rationalCommonNormKernel G ∧ g • y = y := by
  rw [compactStabilizer, Subgroup.mem_inf, mem_reducedFixer]

theorem compactStabilizer_le_reducedFixer (y : D.ReducedBuilding) :
    D.compactStabilizer y ≤ D.reducedFixer y :=
  inf_le_right

theorem compactStabilizer_le_rationalCommonNormKernel (y : D.ReducedBuilding) :
    D.compactStabilizer y ≤ Plancherel.rationalCommonNormKernel G :=
  inf_le_left

end KPApartmentData

end LocalField

end Langlands.Geometry.Building
