import Langlands.Geometry.Building.FullValidity.DatumTransport.Building
import Langlands.Geometry.Building.FullValidity.ChamberAxioms
import Langlands.Geometry.Building.CrossTorusAffineRoots

/-!
# KP Axiom 4.1.16 under based group isomorphisms

Let `P` be parahoric building data for `G`, `f : G ≅ H`, `σ : S ≅ S'` and `j : S' → H` with
`P.i ≫ f = σ ≫ j`, and let `P'` be the transported data `P.basedTransport σ f h`. With
`A : A(S) ≃ A(S')` the apartment comparison and `Φ : B(G) ≃ B(H)` the building comparison, this
module shows that `f` carries every group in KP Axiom 4.1.16 for `P` onto the corresponding
group for `P'`:

* `G(F)^0_Y` onto `H(F)^0_{Φ(Y)}`, and `U(ν)(F) ∩ G(F)^0_Y` onto `U(ν')(F) ∩ H(F)^0_{Φ(Y)}` for
  `ν' = σ ∘ ν`;
* the affine root group `U_ψ` onto `U_{ψ ∘ A⁻¹}` of the transported root.

The roots, the non-divisible roots, the generic cocharacters and the least non-negative
functionals correspond under `σ` and `A`. Hence the Iwahori decomposition at a chamber `C` of
`A(S)` and a generic `ν` gives the Iwahori decomposition at `A(C)` and `σ ∘ ν`, and
`P.HasIwahoriDecomposition` gives `P'.HasIwahoriDecomposition`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

open DatumTransport

namespace IwahoriTransport

/-! ### Maps intertwined by bijections -/

/-- If `q ∘ e = φ ∘ p` for bijections `e` and `φ`, then `q` is injective exactly when `p` is,
and the range of `q` is the image under `φ` of the range of `p`. -/
theorem injective_iff_and_range_eq_of_intertwined {X Y Z W : Type*} {p : X → Z} {q : Y → W}
    (e : X ≃ Y) (φ : Z ≃ W) (hpq : ∀ a, q (e a) = φ (p a)) :
    (Function.Injective q ↔ Function.Injective p) ∧ Set.range q = φ '' Set.range p := by
  have hq : q = φ ∘ p ∘ e.symm := funext fun b => by
    rw [Function.comp_apply, Function.comp_apply, ← hpq, e.apply_symm_apply]
  subst hq
  refine ⟨?_, ?_⟩
  · rw [Equiv.comp_injective, Equiv.injective_comp]
  · rw [Set.range_comp, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]

section Points

variable {k : Type u} [CommRing k] {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- The bijection `L ≃ L'` given by `f` when `f(L) = L'`. -/
def subgroupMapEquiv (f : G ≅ H) {L : Subgroup (rationalPoints G)}
    {L' : Subgroup (rationalPoints H)} (hL : L.map (rationalPoints.map f.hom) = L') : L ≃ L' :=
  (pointsEquiv f).toEquiv.subtypeEquiv fun g => by
    rw [← hL]
    exact (mem_map_iff f L g).symm

@[simp] theorem subgroupMapEquiv_apply (f : G ≅ H) {L : Subgroup (rationalPoints G)}
    {L' : Subgroup (rationalPoints H)} (hL : L.map (rationalPoints.map f.hom) = L') (x : L) :
    (subgroupMapEquiv f hL x : rationalPoints H) = rationalPoints.map f.hom x :=
  rfl

end Points

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (P : ParahoricBuildingData G) {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : S.toGrp ⟶ H} (σ : P.S ≅ S) (f : G ≅ H)
  (h : P.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j)

/-! ### Stabilizers and unipotent radicals -/

/-- `Φ(g · Y) = f(g) · Φ(Y)`. -/
theorem image_smul (g : rationalPoints G) (Y : Set P.ReducedBuilding) :
    P.basedBuildingEquiv σ f h '' (g • Y) =
      rationalPoints.map f.hom g • P.basedBuildingEquiv σ f h '' Y := by
  rw [← Set.image_smul, ← Set.image_smul, Set.image_image, Set.image_image]
  exact Set.image_congr fun y _ => P.basedBuildingEquiv_smul σ f h g y

/-- `Φ(A(Ω)) = Φ(Ω)` for subsets of the apartment: the image of `A(Ω)` in `B(H)` is the image
under `Φ` of the image of `Ω` in `B(G)`. -/
theorem apartmentMap_image_basedApartmentEquiv (Ω : Set P.Apartment) :
    (P.basedTransport σ f h).apartmentMap '' (P.basedApartmentEquiv σ f h '' Ω) =
      P.basedBuildingEquiv σ f h '' (P.apartmentMap '' Ω) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨P.apartmentMap x, ⟨x, hx, rfl⟩, P.basedBuildingEquiv_apartmentMap σ f h x⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨P.basedApartmentEquiv σ f h x, ⟨x, hx, rfl⟩,
      (P.basedBuildingEquiv_apartmentMap σ f h x).symm⟩

/-- `f(G(F)^0_Y) = H(F)^0_{Φ(Y)}`. -/
theorem map_zeroStabilizer (Y : Set P.ReducedBuilding) :
    (P.zeroStabilizer Y).map (rationalPoints.map f.hom) =
      (P.basedTransport σ f h).zeroStabilizer (P.basedBuildingEquiv σ f h '' Y) := by
  ext y
  obtain ⟨g, rfl⟩ := (pointsEquiv f).surjective y
  rw [pointsEquiv_apply, mem_map_iff, ParahoricBuildingData.mem_zeroStabilizer,
    ParahoricBuildingData.mem_zeroStabilizer,
    ParahoricBuildingData.basedTransport_zeroSubgroup, mem_map_iff]
  refine and_congr_right fun _ => ?_
  refine (Set.image_injective.mpr (P.basedBuildingEquiv σ f h).injective).eq_iff.symm.trans ?_
  rw [image_smul P σ f h]
  exact Iff.rfl

omit [IsAffineHom H.X.hom] in
include h in
/-- `f(U(ν)(F)) = U(σ ∘ ν)(F)`, for the Dynamic unipotent radicals of `ν ≫ i` and of
`(σ ∘ ν) ≫ j = ν ≫ i ≫ f`. -/
theorem map_unipotentPoints (ν : cocharacterLattice P.S) :
    ((Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _))).map
        (rationalPoints.map f.hom) =
      (Dynamic.unipotent (CommGroupScheme.groupHom (cocharacterLattice.congr σ ν) ≫ j)).carrier
        (Over.mk (𝟙 _)) := by
  have hχ : CommGroupScheme.groupHom (cocharacterLattice.congr σ ν) ≫ j =
      (CommGroupScheme.groupHom ν ≫ P.i) ≫ f.hom := by
    rw [Category.assoc, h]
    rfl
  rw [hχ]
  ext y
  obtain ⟨g, rfl⟩ := (pointsEquiv f).surjective y
  rw [pointsEquiv_apply, mem_map_iff,
    Dynamic.unipotent_eq_comap_of_iso (CommGroupScheme.groupHom ν ≫ P.i) f]
  rfl

/-- `f(U(ν)(F) ∩ G(F)^0_Y) = U(σ ∘ ν)(F) ∩ H(F)^0_{Φ(Y)}`. -/
theorem map_zeroStabilizerUnipotentPoints (ν : cocharacterLattice P.S)
    (Y : Set P.ReducedBuilding) :
    (P.zeroStabilizerUnipotentPoints ν Y).map (rationalPoints.map f.hom) =
      (P.basedTransport σ f h).zeroStabilizerUnipotentPoints (cocharacterLattice.congr σ ν)
        (P.basedBuildingEquiv σ f h '' Y) := by
  rw [ParahoricBuildingData.zeroStabilizerUnipotentPoints,
    Subgroup.map_inf_eq _ _ (rationalPoints.map f.hom) (pointsEquiv f).injective, map_unipotentPoints P σ f h,
    map_zeroStabilizer P σ f h]
  rfl

/-- The product map `(u, z, v) ↦ u z v` for `P'` at `Φ(Y)` and `σ ∘ ν` is the product map for
`P` at `Y` and `ν` followed by `f`, up to the bijection of factors given by `f`. So it is
injective exactly when the product map for `P` is, and its range is the `f`-image. -/
theorem zeroStabilizerProduct_basedTransport (ν : cocharacterLattice P.S)
    (Y : Set P.ReducedBuilding) :
    (Function.Injective ((P.basedTransport σ f h).zeroStabilizerProduct
        (P.basedBuildingEquiv σ f h '' Y) (cocharacterLattice.congr σ ν)) ↔
      Function.Injective (P.zeroStabilizerProduct Y ν)) ∧
    Set.range ((P.basedTransport σ f h).zeroStabilizerProduct (P.basedBuildingEquiv σ f h '' Y)
        (cocharacterLattice.congr σ ν)) =
      rationalPoints.map f.hom '' Set.range (P.zeroStabilizerProduct Y ν) := by
  have hneg := map_zeroStabilizerUnipotentPoints P σ f h (-ν) Y
  rw [map_neg] at hneg
  let e : P.zeroStabilizerUnipotentPoints ν Y × P.centralizerZero ×
        P.zeroStabilizerUnipotentPoints (-ν) Y ≃
      (P.basedTransport σ f h).zeroStabilizerUnipotentPoints (cocharacterLattice.congr σ ν)
          (P.basedBuildingEquiv σ f h '' Y) × (P.basedTransport σ f h).centralizerZero ×
        (P.basedTransport σ f h).zeroStabilizerUnipotentPoints (-cocharacterLattice.congr σ ν)
          (P.basedBuildingEquiv σ f h '' Y) :=
    (subgroupMapEquiv f (map_zeroStabilizerUnipotentPoints P σ f h ν Y)).prodCongr
      ((Equiv.refl _).prodCongr (subgroupMapEquiv f hneg))
  refine injective_iff_and_range_eq_of_intertwined e (pointsEquiv f).toEquiv fun p => ?_
  change rationalPoints.map f.hom (p.1 : rationalPoints G) *
      rationalPoints.map (P.centralizer.j ≫ f.hom) (p.2.1 : rationalPoints P.centralizer.Z) *
        rationalPoints.map f.hom (p.2.2 : rationalPoints G) =
    rationalPoints.map f.hom ((p.1 : rationalPoints G) *
      rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
        (p.2.2 : rationalPoints G))
  rw [map_mul, map_mul, map_comp_apply]

/-! ### Roots and affine functionals -/

include f h in
/-- Non-divisible roots correspond under `σ`. -/
theorem mem_indivisibleRoots_iff (a : characterLattice P.S) :
    characterLattice.congr σ a ∈ RelativeRoot.indivisibleRoots j ↔
      a ∈ RelativeRoot.indivisibleRoots P.i := by
  have hr : ∀ b, characterLattice.congr σ b ∈ relativeRoots j ↔ b ∈ relativeRoots P.i :=
    fun b => roots_mem_of_transport_iff σ f h b
  constructor
  · rintro ⟨ha, hdiv⟩
    refine ⟨(hr a).mp ha, fun b hb m hm hba => hdiv _ ((hr b).mpr hb) m hm ?_⟩
    rw [← map_nsmul, hba]
  · rintro ⟨ha, hdiv⟩
    refine ⟨(hr a).mpr ha, fun b' hb' m hm hba => ?_⟩
    obtain ⟨b, rfl⟩ := (characterLattice.congr σ).surjective b'
    refine hdiv b ((hr b).mp hb') m hm ((characterLattice.congr σ).injective ?_)
    rw [map_nsmul, hba]

include f h in
/-- Non-divisible roots positive on `ν` correspond to those positive on `σ ∘ ν`. -/
theorem mem_indivisiblePositiveRoots_iff (ν : cocharacterLattice P.S)
    (a : characterLattice P.S) :
    characterLattice.congr σ a ∈
        RelativeRoot.indivisiblePositiveRoots j (cocharacterLattice.congr σ ν) ↔
      a ∈ RelativeRoot.indivisiblePositiveRoots P.i ν := by
  change characterLattice.congr σ a ∈ RelativeRoot.indivisibleRoots j ∧
      0 < latticePairing S (characterLattice.congr σ a) (cocharacterLattice.congr σ ν) ↔
    a ∈ RelativeRoot.indivisibleRoots P.i ∧ 0 < latticePairing P.S a ν
  rw [mem_indivisibleRoots_iff P σ f h, latticePairing_congr]

include f h in
/-- The non-divisible roots positive on `σ ∘ ν` are the `σ`-images of those positive on `ν`. -/
theorem image_indivisiblePositiveRoots (ν : cocharacterLattice P.S) :
    characterLattice.congr σ '' RelativeRoot.indivisiblePositiveRoots P.i ν =
      RelativeRoot.indivisiblePositiveRoots j (cocharacterLattice.congr σ ν) := by
  ext a'
  obtain ⟨a, rfl⟩ := (characterLattice.congr σ).surjective a'
  rw [(characterLattice.congr σ).injective.mem_set_image,
    mem_indivisiblePositiveRoots_iff P σ f h]

/-- Affine functionals on `A(S)` carried to the transported apartment, `ψ ↦ ψ ∘ A⁻¹`. -/
def functionalEquiv :
    (P.Apartment →ᵃ[ℝ] ℝ) ≃ₗ[ℝ] ((P.basedTransport σ f h).Apartment →ᵃ[ℝ] ℝ) :=
  (P.basedApartmentEquiv σ f h).congrLeftₗ ℝ ℝ

@[simp] theorem functionalEquiv_apply_basedApartmentEquiv (ψ : P.Apartment →ᵃ[ℝ] ℝ)
    (x : P.Apartment) :
    functionalEquiv P σ f h ψ (P.basedApartmentEquiv σ f h x) = ψ x := by
  exact congrArg ψ ((P.basedApartmentEquiv σ f h).symm_apply_apply x)

/-- The least non-negative functional of KP Axiom 4.1.16 corresponds under `σ` and `A`. -/
theorem isLeastNonnegativeFunctional_iff (α : relativeRoots P.i) (Ω : Set P.Apartment)
    (ψ : P.Apartment →ᵃ[ℝ] ℝ) :
    (P.basedTransport σ f h).IsLeastNonnegativeFunctional (relativeRootsTransportEquiv σ f h α)
        (P.basedApartmentEquiv σ f h '' Ω) (functionalEquiv P σ f h ψ) ↔
      P.IsLeastNonnegativeFunctional α Ω ψ := by
  have := mono_of_isMaximalSplitTorus (P.isMaximalSplitTorus_of_basedIso σ f h)
  have hlin : ∀ ψ : P.Apartment →ᵃ[ℝ] ℝ, (functionalEquiv P σ f h ψ).linear =
      rootForm j (relativeRootsTransportEquiv σ f h α) ↔ ψ.linear = rootForm P.i α :=
    fun ψ => P.apartment.affineFunctionalTransportEquiv_linear_eq_rootForm_iff σ f h ψ α
  have hnn : ∀ ψ : P.Apartment →ᵃ[ℝ] ℝ,
      (∀ y ∈ P.basedApartmentEquiv σ f h '' Ω, 0 ≤ functionalEquiv P σ f h ψ y) ↔
        ∀ x ∈ Ω, 0 ≤ ψ x := by
    intro ψ
    simp only [Set.forall_mem_image, functionalEquiv_apply_basedApartmentEquiv]
  refine and_congr (hlin ψ) (and_congr (hnn ψ) ⟨fun H ψ' h₁ h₂ x => ?_, fun H ψ' h₁ h₂ y => ?_⟩)
  · simpa only [functionalEquiv_apply_basedApartmentEquiv] using
      H (functionalEquiv P σ f h ψ') ((hlin ψ').mpr h₁) ((hnn ψ').mpr h₂)
        (P.basedApartmentEquiv σ f h x)
  · obtain ⟨ψ'', rfl⟩ := (functionalEquiv P σ f h).surjective ψ'
    obtain ⟨x, rfl⟩ := (P.basedApartmentEquiv σ f h).surjective y
    simpa only [functionalEquiv_apply_basedApartmentEquiv] using
      H ψ'' ((hlin ψ'').mp h₁) ((hnn ψ'').mp h₂) x

/-! ### Affine root groups and ordered products -/

/-- `f(U_ψ) = U_{ψ ∘ A⁻¹}` for the transported root, as a membership statement. -/
theorem mem_affineRootGroup_iff (α : relativeRoots P.i) (ψ : P.Apartment →ᵃ[ℝ] ℝ)
    (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈ (P.basedTransport σ f h).affineRootGroup
        ((relativeRootsTransportEquiv σ f h α : characterLattice S)) (functionalEquiv P σ f h ψ) ↔
      g ∈ P.affineRootGroup α ψ := by
  have := mono_of_isMaximalSplitTorus (P.isMaximalSplitTorus_of_basedIso σ f h)
  exact P.apartment.mem_affineRootGroup_transport_iff σ f h α ψ g

/-- `mem_affineRootGroup_iff` for a root `α'` and a functional `ψ'` of the transported data
given as the images of `α` and `ψ`. -/
theorem mem_affineRootGroup_iff_of_eq {α : relativeRoots P.i}
    {α' : relativeRoots (P.basedTransport σ f h).i} (hα : relativeRootsTransportEquiv σ f h α = α')
    {ψ : P.Apartment →ᵃ[ℝ] ℝ} {ψ' : (P.basedTransport σ f h).Apartment →ᵃ[ℝ] ℝ}
    (hψ : functionalEquiv P σ f h ψ = ψ') (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈ (P.basedTransport σ f h).affineRootGroup α' ψ' ↔
      g ∈ P.affineRootGroup α ψ := by
  subst hα hψ
  exact mem_affineRootGroup_iff P σ f h α ψ g

/-- The ordered-product clause of KP Axiom 4.1.16 at `C` and `ν` gives the clause at `A(C)` and
`σ ∘ ν`. The roots `a'_k`, the functionals `ψ'` and the factors `u'_k` for `P'` come from
`a_k = σ⁻¹(a'_k)`, `ψ_a = ψ'_{σ(a)} ∘ A` and `u_k = f⁻¹(u'_k)` for `P`. -/
theorem isOrderedRootProductBijective {Ca : Set P.Apartment} {ν : cocharacterLattice P.S}
    (hP : P.IsOrderedRootProductBijective Ca ν) :
    (P.basedTransport σ f h).IsOrderedRootProductBijective (P.basedApartmentEquiv σ f h '' Ca)
      (cocharacterLattice.congr σ ν) := by
  intro ψ' hψ' n a' ha' hrange
  let R := relativeRootsTransportEquiv σ f h
  let T := functionalEquiv P σ f h
  let ψ : relativeRoots P.i → (P.Apartment →ᵃ[ℝ] ℝ) := fun α => T.symm (ψ' (R α))
  let a : Fin n → relativeRoots P.i := fun k => R.symm (a' k)
  have hψ : ∀ α : relativeRoots P.i, (α : characterLattice P.S) ∈
      RelativeRoot.indivisibleRoots P.i → P.IsLeastNonnegativeFunctional α Ca (ψ α) := by
    intro α hα
    rw [← isLeastNonnegativeFunctional_iff P σ f h]
    simp only [ψ, T, LinearEquiv.apply_symm_apply]
    exact hψ' (R α) ((mem_indivisibleRoots_iff P σ f h α).mpr hα)
  have ha : Function.Injective a := R.symm.injective.comp ha'
  have hcomp : (fun k => characterLattice.congr σ (a k : characterLattice P.S)) =
      fun k => ((a' k).1 : characterLattice S) :=
    funext fun k => congrArg Subtype.val (R.apply_symm_apply (a' k))
  have harange : Set.range (fun k => (a k : characterLattice P.S)) =
      RelativeRoot.indivisiblePositiveRoots P.i ν := by
    apply Set.image_injective.mpr (characterLattice.congr σ).injective
    rw [image_indivisiblePositiveRoots P σ f h, ← Set.range_comp, Function.comp_def, hcomp]
    exact hrange
  obtain ⟨hinj, hran⟩ := hP ψ hψ n a ha harange
  have hmem : ∀ k (g : rationalPoints G), g ∈ P.affineRootGroup (a k) (ψ (a k)) ↔
      rationalPoints.map f.hom g ∈
        (P.basedTransport σ f h).affineRootGroup (a' k) (ψ' (a' k)) := by
    intro k g
    have hR : R (a k) = a' k := R.apply_symm_apply (a' k)
    have hT : T (ψ (a k)) = ψ' (a' k) :=
      (T.apply_symm_apply _).trans (congrArg ψ' hR)
    exact (mem_affineRootGroup_iff_of_eq P σ f h hR hT g).symm
  let e : (∀ k, P.affineRootGroup (a k) (ψ (a k))) ≃
      ∀ k, (P.basedTransport σ f h).affineRootGroup (a' k) (ψ' (a' k)) :=
    Equiv.piCongrRight fun k => (pointsEquiv f).toEquiv.subtypeEquiv (hmem k)
  obtain ⟨h₁, h₂⟩ := injective_iff_and_range_eq_of_intertwined e (pointsEquiv f).toEquiv
    (p := P.orderedAffineRootProduct a ψ)
    (q := (P.basedTransport σ f h).orderedAffineRootProduct a' ψ') fun u => by
      change (List.ofFn fun k => rationalPoints.map f.hom (u k : rationalPoints G)).prod =
        rationalPoints.map f.hom (List.ofFn fun k => (u k : rationalPoints G)).prod
      rw [map_list_prod, List.map_ofFn]
      rfl
  refine ⟨h₁.mpr hinj, ?_⟩
  rw [h₂, hran, apartmentMap_image_basedApartmentEquiv P σ f h]
  exact (Subgroup.coe_map (rationalPoints.map f.hom) _).symm.trans
    (congrArg SetLike.coe (map_zeroStabilizerUnipotentPoints P σ f h ν _))

/-- KP Axiom 4.1.16 at the chamber `C` and the generic cocharacter `ν` gives KP Axiom 4.1.16
for the transported data at `A(C)` and `σ ∘ ν`. -/
theorem isIwahoriDecompositionAt {Ca : Set P.Apartment} {ν : cocharacterLattice P.S}
    (hP : P.IsIwahoriDecompositionAt Ca ν) :
    (P.basedTransport σ f h).IsIwahoriDecompositionAt (P.basedApartmentEquiv σ f h '' Ca)
      (cocharacterLattice.congr σ ν) := by
  have hY := apartmentMap_image_basedApartmentEquiv P σ f h Ca
  obtain ⟨hinj, hrange⟩ := zeroStabilizerProduct_basedTransport P σ f h ν (P.apartmentMap '' Ca)
  refine ⟨?_, ?_, ?_, isOrderedRootProductBijective P σ f h hP.orderedProduct_pos, ?_⟩
  · rw [hY]
    exact hinj.mpr hP.injective_product
  · rw [hY]
    refine hrange.trans ?_
    rw [hP.range_product, ← Subgroup.coe_map]
    exact congrArg SetLike.coe (map_zeroStabilizer P σ f h _)
  · intro α' hα'
    obtain ⟨α, rfl⟩ := (relativeRootsTransportEquiv σ f h).surjective α'
    obtain ⟨ψ, hψ⟩ := hP.exists_isLeastNonnegativeFunctional α
      ((mem_indivisibleRoots_iff P σ f h α).mp hα')
    exact ⟨_, (isLeastNonnegativeFunctional_iff P σ f h α Ca ψ).mpr hψ⟩
  · have := isOrderedRootProductBijective P σ f h hP.orderedProduct_neg
    rwa [map_neg] at this

end IwahoriTransport

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {j : S.toGrp ⟶ H}

/-- KP Axiom 4.1.16 is transported along a based group isomorphism: if `P` has the Iwahori
decomposition, so has `P.basedTransport σ f h`. A chamber of the transported apartment is
`A(C)` for a chamber `C` of `A(S)`, and a generic cocharacter of `S'` is `σ ∘ ν` for a generic
cocharacter `ν` of `S`. -/
theorem HasIwahoriDecomposition.basedTransport {P : ParahoricBuildingData G}
    (hP : P.HasIwahoriDecomposition) (σ : P.S ≅ S) (f : G ≅ H)
    (h : P.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j) :
    (P.basedTransport σ f h).HasIwahoriDecomposition := by
  intro Ca' hCa' ν' hν'
  obtain ⟨ν, rfl⟩ := (cocharacterLattice.congr σ).surjective ν'
  obtain ⟨Ca, rfl⟩ : ∃ Ca, P.basedApartmentEquiv σ f h '' Ca = Ca' :=
    ⟨_, Set.image_preimage_eq Ca' (P.basedApartmentEquiv σ f h).surjective⟩
  have hCa : AffineRootSystem.IsChamber P.affineRoots Ca := by
    rw [← AffineRootSystem.isChamber_image_transportedRoots_iff (P.basedApartmentEquiv σ f h),
      P.transportedRoots_basedApartmentEquiv σ f h]
    exact hCa'
  exact IwahoriTransport.isIwahoriDecompositionAt P σ f h
    (hP Ca hCa ν ((isGenericCocharacter_of_transport_iff σ f h ν).mp hν'))

end ParahoricBuildingData

end Langlands.Geometry.Building
