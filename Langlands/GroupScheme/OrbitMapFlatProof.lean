import Langlands.GroupScheme.OrbitMapFlatStatement
import Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperProof
import Langlands.Algebra.GenericFlatness
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-!
# Orbit maps onto reduced homogeneous schemes are faithfully flat

Generic flatness over an integral affine open of the target, translation by rational
points, and generalization along the flat orbit map.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme.OrbitMapFlat

/-! ### Generic flatness of localizations -/

/-- Generic flatness in the form used below: for a finite type ring map `φ : R → B` from a
noetherian domain, some nonzero `a` makes `R_b → B_b` flat for every multiple `b` of `a`. -/
theorem exists_flat_awayMap {R B : Type u} [CommRing R] [CommRing B] [IsDomain R]
    [IsNoetherianRing R] (φ : R →+* B) (hφ : φ.FiniteType) :
    ∃ a : R, a ≠ 0 ∧ ∀ b : R, a ∣ b → (Localization.awayMap φ b).Flat := by
  algebraize [φ]
  obtain ⟨a, ha, h⟩ := Langlands.Algebra.GenericFlatness.genFlat_of_finiteType (A := R) B B
  refine ⟨a, ha, fun b hb => ?_⟩
  have hM := h b hb
  have hloc : IsLocalizedModule (Submonoid.powers b)
      (IsScalarTower.toAlgHom R B (Localization.Away (algebraMap R B b))).toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization, Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact Localization.isLocalization
  have hB : Module.Flat R (Localization.Away (algebraMap R B b)) :=
    (Langlands.Algebra.GenericFlatness.flat_localizedModule_iff (Submonoid.powers b)
      (IsScalarTower.toAlgHom R B (Localization.Away (algebraMap R B b))).toLinearMap).mp hM
  let _ := (Localization.awayMap φ b).toAlgebra
  have : IsScalarTower R (Localization.Away b) (Localization.Away (algebraMap R B b)) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    show _ = Localization.awayMap φ b (algebraMap R (Localization.Away b) r)
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq,
      IsScalarTower.algebraMap_apply R B (Localization.Away _)]
    rfl
  exact (Module.flat_iff_of_isLocalization (Localization.Away b) (Submonoid.powers b) _).mpr hB

/-! ### Local flatness data -/

section Local

variable {X Y : Scheme.{u}}

/-- `f` is flat on an open neighbourhood of `z`, over an open of the target. -/
def FlatNear (f : X ⟶ Y) (z : X) : Prop :=
  ∃ (U : Y.Opens) (V : X.Opens) (_ : z ∈ V) (e : V ≤ f ⁻¹ᵁ U), Flat (f.resLE U V e)

theorem flat_of_forall_flatNear (f : X ⟶ Y) (H : ∀ z, FlatNear f z) : Flat f :=
  (IsZariskiLocalAtSource.iff_exists_resLE (P := @Flat)).mpr H

private theorem flat_resLE_of_eq {f g : X ⟶ Y} (h : f = g) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) (hf : Flat (f.resLE U V e)) :
    Flat (g.resLE U V e') := by
  subst h
  exact hf

/-- Local flatness is transported along a commuting square of isomorphisms. -/
theorem flatNear_of_comm (f : X ⟶ Y) (φ : X ⟶ X) (ψ : Y ⟶ Y) [IsIso φ] [IsIso ψ]
    (h : φ ≫ f = f ≫ ψ) (z : X) (hz : FlatNear f (φ z)) : FlatNear f z := by
  obtain ⟨U, V, hzV, e, hflat⟩ := hz
  have e' : φ ⁻¹ᵁ V ≤ f ⁻¹ᵁ (ψ ⁻¹ᵁ U) := by
    intro w hw
    have hw' : f (φ w) ∈ U := e hw
    change ψ (f w) ∈ U
    rwa [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
  refine ⟨ψ ⁻¹ᵁ U, φ ⁻¹ᵁ V, hzV, e', ?_⟩
  have h1 : Flat (φ.resLE V (φ ⁻¹ᵁ V) le_rfl ≫ f.resLE U V e) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  rw [Scheme.Hom.resLE_comp_resLE] at h1
  have h2 := flat_resLE_of_eq h _ (e'.trans ((Opens.map f.base).map (homOfLE le_rfl)).le) h1
  rw [← Scheme.Hom.resLE_comp_resLE, Scheme.Hom.resLE_eq_morphismRestrict] at h2
  · exact (MorphismProperty.cancel_right_of_respectsIso @Flat _ _).mp h2
  · exact e'
  · exact le_rfl

/-- A reduced locally noetherian scheme with a point has a nonempty affine open whose ring of
sections is a domain. -/
theorem exists_affineOpen_isDomain [IsLocallyNoetherian Y] [IsReduced Y] (y : Y) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ (V : Set Y).Nonempty ∧ IsDomain Γ(Y, V) := by
  obtain ⟨V₀, hV₀, hyV₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
  have : IsAffine V₀.toScheme := hV₀
  have : IsNoetherian V₀.toScheme := {}
  let y₀ : V₀.toScheme := ⟨y, hyV₀⟩
  obtain ⟨o, ho, ⟨p, hp⟩, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent y₀) (irreducibleComponent_mem_irreducibleComponents y₀)
  have hoirr : IsPreirreducible o :=
    isIrreducible_irreducibleComponent.isPreirreducible.open_subset ho hoZ
  have hO : IsOpen (V₀.ι '' o) := V₀.ι.isOpenEmbedding.isOpenMap o ho
  have hOirr : IsPreirreducible (V₀.ι '' o) :=
    hoirr.image _ V₀.ι.continuous.continuousOn
  obtain ⟨V, hV, hpV, hVO⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, hO⟩)
    (show V₀.ι p ∈ (⟨_, hO⟩ : Y.Opens) from ⟨p, hp, rfl⟩)
  have hVirr : IsIrreducible (V : Set Y) := ⟨⟨_, hpV⟩, hOirr.open_subset V.isOpen hVO⟩
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hVirr
  have : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced V.toScheme
  refine ⟨V, hV, ⟨_, hpV⟩, ?_⟩
  exact Function.Injective.isDomain (V.topIso.commRingCatIsoToRingEquiv.symm : Γ(Y, V) →+* Γ(V, ⊤))
    (RingEquiv.injective _)

/-- Generic flatness for a locally finite type quasi-compact morphism to a reduced locally
noetherian scheme: there is a nonempty open of the target over which the morphism is flat near
every point. -/
theorem exists_open_flatNear (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsLocallyNoetherian Y] [IsReduced Y] (y : Y) :
    ∃ U : Y.Opens, (U : Set Y).Nonempty ∧ ∀ z : X, f z ∈ U → FlatNear f z := by
  classical
  obtain ⟨V, hV, hVne, hdom⟩ := exists_affineOpen_isDomain y
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨Ws, hWs, hWfin, hWsup⟩ := X.isBasis_affineOpens.exists_finite_of_isCompact
    (f.isCompact_preimage hV.isCompact)
  obtain ⟨t, rfl⟩ := hWfin.exists_finset_coe
  have hle : ∀ W ∈ t, W ≤ f ⁻¹ᵁ V := fun W hW => hWsup ▸ le_sSup hW
  have hft : ∀ W (hW : W ∈ t), (f.appLE V W (hle W hW)).hom.FiniteType := fun W hW =>
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance ⟨V, hV⟩
      ⟨W, hWs hW⟩ (hle W hW)
  choose a ha hflat using fun W (hW : W ∈ t) => exists_flat_awayMap _ (hft W hW)
  let b : Γ(Y, V) := ∏ W ∈ t.attach, a W.1 W.2
  have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W _ => ha W.1 W.2
  have hab : ∀ W (hW : W ∈ t), a W hW ∣ b := fun W hW =>
    Finset.dvd_prod_of_mem (fun W : t => a W.1 W.2) (Finset.mem_attach t ⟨W, hW⟩)
  refine ⟨Y.basicOpen b, ?_, ?_⟩
  · rw [← Opens.ne_bot_iff_nonempty]
    simpa using hb
  · intro z hz
    have hzV : z ∈ f ⁻¹ᵁ V := Y.basicOpen_le b hz
    rw [hWsup] at hzV
    obtain ⟨W, hW, hzW⟩ := Opens.mem_sSup.mp hzV
    have hWb : X.basicOpen (f.appLE V W (hle W hW) b) ≤ f ⁻¹ᵁ Y.basicOpen b := by
      rw [Scheme.basicOpen_appLE]
      exact inf_le_right
    refine ⟨Y.basicOpen b, X.basicOpen (f.appLE V W (hle W hW) b), ?_, hWb, ?_⟩
    · rw [Scheme.basicOpen_appLE]
      exact ⟨hzW, hz⟩
    · have : IsAffine (Y.basicOpen b).toScheme := hV.basicOpen b
      have : IsAffine (X.basicOpen (f.appLE V W (hle W hW) b)).toScheme :=
        (hWs hW).basicOpen _
      have := hV.isLocalization_basicOpen b
      have := (hWs hW).isLocalization_basicOpen (f.appLE V W (hle W hW) b)
      rw [HasRingHomProperty.iff_of_isAffine (P := @Flat), Scheme.Hom.appTop,
        Scheme.Hom.resLE_app_top, CommRingCat.hom_comp,
        RingHom.Flat.respectsIso.cancel_left_isIso, CommRingCat.hom_comp,
        RingHom.Flat.respectsIso.cancel_right_isIso,
        hV.appLE_eq_away_map f (hWs hW) (hle W hW) b, CommRingCat.hom_ofHom]
      exact (RingHom.Flat.respectsIso.isLocalization_away_iff _ _ _ b).mp
        (hflat W hW b (hab W hW))

end Local

/-! ### Translations by points over the base -/

section Translation

variable {S : Scheme.{u}} {G : GroupScheme S} {O : Over S} (a : SchemeAction G O)

/-- The action `y ↦ g • y` on `O` of a point `g` of `G` over the base. -/
def actBy (g : 𝟙_ (Over S) ⟶ G.X) : O ⟶ O :=
  a.act (toUnit O ≫ g) (𝟙 O)

theorem leftMul_comp_leftMul (g h : 𝟙_ (Over S) ⟶ G.X) :
    (FiniteIndexTransfer.leftMul G) g ≫ (FiniteIndexTransfer.leftMul G) h = (FiniteIndexTransfer.leftMul G) (h * g) := by
  simp only [FiniteIndexTransfer.leftMul, ← Hom.mul_def]
  rw [comp_mul, comp_toUnit_assoc, Category.comp_id, comp_mul,
    _root_.mul_assoc]

theorem leftMul_one : (FiniteIndexTransfer.leftMul G) (1 : 𝟙_ (Over S) ⟶ G.X) = 𝟙 G.X := by
  simp only [FiniteIndexTransfer.leftMul, ← Hom.mul_def]
  rw [MonObj.comp_one, _root_.one_mul]

instance (g : 𝟙_ (Over S) ⟶ G.X) : IsIso ((FiniteIndexTransfer.leftMul G) g) :=
  ⟨⟨(FiniteIndexTransfer.leftMul G) g⁻¹, by rw [leftMul_comp_leftMul, inv_mul_cancel, leftMul_one],
    by rw [leftMul_comp_leftMul, mul_inv_cancel, leftMul_one]⟩⟩

theorem actBy_comp_actBy (g h : 𝟙_ (Over S) ⟶ G.X) :
    actBy a g ≫ actBy a h = actBy a (h * g) := by
  rw [actBy, actBy, actBy, SchemeAction.naturality, comp_toUnit_assoc, Category.comp_id,
    ← SchemeAction.act_mul, ← comp_mul]

theorem actBy_one : actBy a (1 : 𝟙_ (Over S) ⟶ G.X) = 𝟙 O := by
  rw [actBy, MonObj.comp_one, SchemeAction.act_one]

instance (g : 𝟙_ (Over S) ⟶ G.X) : IsIso (actBy a g) :=
  ⟨⟨actBy a g⁻¹, by rw [actBy_comp_actBy, inv_mul_cancel, actBy_one],
    by rw [actBy_comp_actBy, mul_inv_cancel, actBy_one]⟩⟩

/-- The orbit map intertwines left multiplication by `g` with the action of `g`. -/
theorem leftMul_comp_orbit (g : 𝟙_ (Over S) ⟶ G.X) (x : 𝟙_ (Over S) ⟶ O) :
    (FiniteIndexTransfer.leftMul G) g ≫ a.act (𝟙 G.X) (toUnit G.X ≫ x) =
      a.act (𝟙 G.X) (toUnit G.X ≫ x) ≫ actBy a g := by
  simp only [FiniteIndexTransfer.leftMul, ← Hom.mul_def]
  rw [actBy, SchemeAction.naturality, SchemeAction.naturality, Category.comp_id,
    Category.comp_id, comp_toUnit_assoc, comp_toUnit_assoc, SchemeAction.act_mul]

/-- On points over the base, `actBy a g` is the action of `g`. -/
theorem comp_actBy (g : 𝟙_ (Over S) ⟶ G.X) (y : 𝟙_ (Over S) ⟶ O) :
    y ≫ actBy a g = a.act g y := by
  rw [actBy, SchemeAction.naturality, comp_toUnit_assoc, Category.comp_id, toUnit_unit,
    Category.id_comp]

/-- On points over the base, the orbit map of `x` is `g ↦ g • x`. -/
theorem comp_orbit (g : 𝟙_ (Over S) ⟶ G.X) (x : 𝟙_ (Over S) ⟶ O) :
    g ≫ a.act (𝟙 G.X) (toUnit G.X ≫ x) = a.act g x := by
  rw [SchemeAction.naturality, Category.comp_id, comp_toUnit_assoc, toUnit_unit,
    Category.id_comp]

end Translation

end Langlands.GroupScheme.OrbitMapFlat

namespace Langlands.GroupScheme

open OrbitMapFlat

/-- Orbit maps onto reduced schemes with a transitive action of rational points are flat,
surjective and quasi-compact. -/
theorem orbitMapFaithfullyFlat : OrbitMapFaithfullyFlatStatement.{u} := by
  intro k _ _ G _ _ O _ _ a x htrans
  set π := a.act (𝟙 G.X) (toUnit G.X ≫ x) with hπ
  have hw : π.left ≫ O.hom = G.X.hom := Over.w π
  have : IsLocallyNoetherian O.left := LocallyOfFiniteType.isLocallyNoetherian O.hom
  have : JacobsonSpace O.left := LocallyOfFiniteType.jacobsonSpace O.hom
  have : QuasiSeparated O.hom :=
    HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated).mpr inferInstance
  have : LocallyOfFiniteType π.left := by
    have : LocallyOfFiniteType (π.left ≫ O.hom) := hw ▸ inferInstance
    exact locallyOfFiniteType_of_comp π.left O.hom
  have hqc : QuasiCompact π.left := by
    have : QuasiCompact (π.left ≫ O.hom) := hw ▸ inferInstance
    exact QuasiCompact.of_comp π.left O.hom
  -- Closed points of `O` are rational points, hence in the orbit of `x`.
  have hrat : ∀ c : O.left, IsClosed ({c} : Set O.left) →
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X, (g ≫ π).left
        (IsLocalRing.closedPoint k) = c := by
    intro c hc
    let c' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ O :=
      Over.homMk (pointOfClosedPoint O.hom c hc) (by simp)
    obtain ⟨g, hg⟩ := htrans c'
    refine ⟨g, ?_⟩
    rw [hπ, comp_orbit, hg]
    exact pointOfClosedPoint_apply O.hom c hc _
  -- Generic flatness over a nonempty open `U` of `O`.
  obtain ⟨U, hUne, hU⟩ := exists_open_flatNear π.left (x.left (IsLocalRing.closedPoint k))
  -- Every point of `O` is moved into `U` by a rational point of `G`.
  have hcover : ∀ w : O.left, ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X,
      (actBy a g).left w ∈ U := by
    by_contra! hne
    obtain ⟨w, hw⟩ := hne
    let Z : Set O.left := ⋂ g, (actBy a g).left ⁻¹' (U : Set O.left)ᶜ
    have hZ : IsClosed Z := isClosed_iInter fun g =>
      U.isOpen.isClosed_compl.preimage (actBy a g).left.continuous
    obtain ⟨c, hcZ, hc⟩ :=
      nonempty_inter_closedPoints ⟨w, Set.mem_iInter.mpr hw⟩ hZ.isLocallyClosed
    obtain ⟨u, huU, hu⟩ := nonempty_inter_closedPoints hUne U.isOpen.isLocallyClosed
    obtain ⟨g₁, hg₁⟩ := hrat c hc
    obtain ⟨g₂, hg₂⟩ := hrat u hu
    have hmove : (g₁ ≫ π) ≫ actBy a (g₂ * g₁⁻¹) = g₂ ≫ π := by
      rw [comp_actBy, hπ, comp_orbit, comp_orbit, ← SchemeAction.act_mul, _root_.mul_assoc,
        inv_mul_cancel, _root_.mul_one]
    have h := congr(($hmove).left (IsLocalRing.closedPoint k))
    have hcu : (actBy a (g₂ * g₁⁻¹)).left c = u := by
      rw [← hg₁, ← hg₂, ← h]
      rfl
    exact Set.mem_iInter.mp hcZ (g₂ * g₁⁻¹) (by rw [hcu]; exact huU)
  have hflat : Flat π.left := by
    apply flat_of_forall_flatNear
    intro z
    obtain ⟨g, hg⟩ := hcover (π.left z)
    have hcomm : ((FiniteIndexTransfer.leftMul G) g).left ≫ π.left = π.left ≫ (actBy a g).left :=
      congrArg (fun f => f.left) (leftMul_comp_orbit a g x)
    have : IsIso ((FiniteIndexTransfer.leftMul G) g).left := inferInstanceAs (IsIso ((Over.forget _).map ((FiniteIndexTransfer.leftMul G) g)))
    have : IsIso (actBy a g).left := inferInstanceAs (IsIso ((Over.forget _).map (actBy a g)))
    refine flatNear_of_comm π.left ((FiniteIndexTransfer.leftMul G) g).left (actBy a g).left hcomm z (hU _ ?_)
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
    exact hg
  have hsurj : Surjective π.left := by
    refine ⟨fun w => ?_⟩
    obtain ⟨c, hcw, hc⟩ := nonempty_inter_closedPoints
      (⟨w, subset_closure (Set.mem_singleton w)⟩ : (closure ({w} : Set O.left)).Nonempty)
      (isClosed_closure (s := ({w} : Set O.left))).isLocallyClosed
    obtain ⟨g, hg⟩ := hrat c hc
    have hspec : w ⤳ π.left (g.left (IsLocalRing.closedPoint k)) := by
      rw [specializes_iff_mem_closure]
      exact hg ▸ hcw
    obtain ⟨z, -, hz⟩ := Flat.generalizingMap π.left hspec
    exact ⟨z, hz⟩
  exact ⟨hflat, hsurj, hqc⟩

end Langlands.GroupScheme
