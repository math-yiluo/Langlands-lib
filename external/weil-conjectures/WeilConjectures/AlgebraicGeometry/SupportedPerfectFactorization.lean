/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import all WeilConjectures.CategoryTheory.CompactGeneratorAmbientThick
import all WeilConjectures.AlgebraicGeometry.DerivedQCohCompactRepresentatives
import all WeilConjectures.AlgebraicGeometry.SupportedKoszulRelativeDetector

/-! # Perfect factorization of maps to supported complexes

Source: Stacks Project, Tags 0A9C, 0E4G, 094A and 09SP.
(blueprint: lem-sc-supported-perfect-factorization).
-/
@[expose] public section
universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open scoped ZeroObject

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem telescope_factor
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C]
    (A : ObjectProperty C) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    [HasCoproducts.{w} A.FullSubcategory]
    [∀ I : Type w, A.IsClosedUnderColimitsOfShape (Discrete I)]
    (P : A.FullSubcategory) (hP : IsCompactObject P)
    (L : A.FullSubcategory) (f₀ : P ⟶ L)
    (X : ℕ → A.FullSubcategory) (t : ∀ n : ℕ, (X n).obj ⟶ (X (n + 1)).obj)
    (S : Cofan (fun n : ℕ ↦ (X n).obj)) (hS : IsColimit S)
    (s : S.pt ⟶ S.pt) (q : S.pt ⟶ L.obj) (r : L.obj ⟶ S.pt⟦(1 : ℤ)⟧)
    (hs : ∀ n : ℕ, S.inj n ≫ s = t n ≫ S.inj (n + 1))
    (hT : Pretriangulated.Triangle.mk (𝟙 S.pt - s) q r ∈ distTriang C) :
    ∃ (n : ℕ) (a : P.obj ⟶ (X n).obj), a ≫ S.inj n ≫ q = f₀.hom := by
  classical
  -- The ambient cofan restricts to A after raising its index universe.
  let Y : ULift.{w} ℕ → A.FullSubcategory := fun n ↦ X n.down
  let c : Cofan (fun n : ULift.{w} ℕ ↦ (X n.down).obj) :=
    Cofan.mk S.pt (fun n ↦ S.inj n.down)
  have hc : IsColimit c :=
    (Cofan.isColimitEquivOfEquiv (Equiv.ulift : ULift.{w} ℕ ≃ ℕ) S) hS
  have hAS : A S.pt := A.prop_of_isColimit (c := c) hc (fun n ↦ (X n.as.down).property)
  let Z : A.FullSubcategory := ⟨S.pt, hAS⟩
  let cA : Cofan Y := Cofan.mk Z (fun n ↦ ObjectProperty.homMk (S.inj n.down))
  have hcA : IsColimit cA := by
    refine Cofan.IsColimit.mk _ (fun d ↦ ObjectProperty.homMk
      (hc.desc (Cofan.mk d.pt.obj (fun n ↦ (d.inj n).hom)))) ?_ ?_
    · intro d n
      apply ObjectProperty.hom_ext
      exact hc.fac _ ⟨n⟩
    · intro d m hm
      apply ObjectProperty.hom_ext
      apply hc.hom_ext
      intro n
      exact (congrArg InducedCategory.Hom.hom (hm n.as)).trans
        (hc.fac (Cofan.mk d.pt.obj (fun n ↦ (d.inj n).hom)) n).symm
  let e : (∐ Y) ≅ Z := (coproductIsCoproduct Y).coconePointUniqueUpToIso hcA
  have he (n : ULift.{w} ℕ) : Sigma.ι Y n ≫ e.hom = cA.inj n :=
    (coproductIsCoproduct Y).comp_coconePointUniqueUpToIso_hom hcA ⟨n⟩
  let tA : ∀ n : ℕ, X n ⟶ X (n + 1) := fun n ↦ ObjectProperty.homMk (t n)
  let F := Functor.ofSequence tA
  let d : (∐ Y) ⟶ ∐ Y := 𝟙 _ - Sigma.desc
    (fun n : ULift.{w} ℕ ↦ tA n.down ≫ Sigma.ι Y ⟨n.down + 1⟩)
  let sA : Z ⟶ Z := ObjectProperty.homMk s
  have hde : d ≫ e.hom = e.hom ≫ (𝟙 Z - sA) := by
    apply Sigma.hom_ext
    intro n
    dsimp only [d]
    rw [← Category.assoc]
    rw [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp, Sigma.ι_comp_desc,
      Category.assoc (tA n.down), he,
      ← Category.assoc (Sigma.ι Y n), he, Preadditive.comp_sub, Category.comp_id]
    simp only [he]
    congr 1
    apply ObjectProperty.hom_ext
    exact (hs n.down).symm
  let qA : Z ⟶ L := ObjectProperty.homMk q
  let rA : L ⟶ Z⟦(1 : ℤ)⟧ := ObjectProperty.homMk
    (r ≫ (A.ι.commShiftIso (1 : ℤ)).inv.app Z)
  have hTA : Pretriangulated.Triangle.mk (𝟙 Z - sA) qA rA ∈
      distTriang A.FullSubcategory := by
    change A.ι.mapTriangle.obj _ ∈ distTriang C
    have hmap : A.ι.map (𝟙 Z - sA) = 𝟙 S.pt - s := by
      rw [Functor.map_sub, CategoryTheory.Functor.map_id]
      rfl
    change Pretriangulated.Triangle.mk (A.ι.map (𝟙 Z - sA)) q
      ((r ≫ (A.ι.commShiftIso (1 : ℤ)).inv.app Z) ≫
        (A.ι.commShiftIso (1 : ℤ)).hom.app Z) ∈ distTriang C
    rw [hmap, Category.assoc, Iso.inv_hom_id_app]
    change Pretriangulated.Triangle.mk (𝟙 S.pt - s) q (r ≫ 𝟙 _) ∈ distTriang C
    rw [Category.comp_id]
    exact hT
  have hT' : Pretriangulated.Triangle.mk d (e.hom ≫ qA)
      (rA ≫ (shiftFunctor A.FullSubcategory (1 : ℤ)).map e.inv) ∈
      distTriang A.FullSubcategory := by
    apply Pretriangulated.isomorphic_distinguished _ hTA
    exact Pretriangulated.Triangle.isoMk _ _ e e (Iso.refl L)
      hde (by simp only [Pretriangulated.Triangle.mk, Category.comp_id, Iso.refl_hom])
      (by simp only [Pretriangulated.Triangle.mk, Category.assoc, ← Functor.map_comp,
        e.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id,
        Iso.refl_hom, Category.id_comp])
  have hTF : Pretriangulated.Triangle.mk
      (𝟙 (∐ fun n : ULift.{w} ℕ ↦ F.obj n.down) -
        Sigma.desc (fun n : ULift.{w} ℕ ↦
          F.map (homOfLE (Nat.le_succ n.down)) ≫
            Sigma.ι (fun k : ULift.{w} ℕ ↦ F.obj k.down) ⟨n.down + 1⟩))
      (e.hom ≫ qA) (rA ≫ (shiftFunctor A.FullSubcategory (1 : ℤ)).map e.inv) ∈
      distTriang A.FullSubcategory := by
    simpa [F, Functor.ofSequence, Functor.OfSequence.map_le_succ, d, Y] using hT'
  -- Surjectivity on compact Hom puts the map at a finite stage.
  obtain ⟨φ, hφ, hbij⟩ := compact_hom_hocolim P hP F L _ _ hTF
  obtain ⟨z, hz⟩ := hbij.2 f₀
  obtain ⟨n, a, ha⟩ := Types.jointly_surjective' z
  have hf : a ≫ Sigma.ι Y ⟨n⟩ ≫ e.hom ≫ qA = f₀ := by
    rw [← hz, ← ha, hφ]
    rfl
  refine ⟨n, a.hom, ?_⟩
  have hf' : a ≫ cA.inj ⟨n⟩ ≫ qA = f₀ := by
    simpa only [← Category.assoc, he] using hf
  exact congrArg InducedCategory.Hom.hom hf'

/-- A map from a perfect object into a quasi-coherent derived object vanishing on V
factors through a perfect object vanishing on V.
Source: Stacks Project, Tag 0A9C, proof, finite factorization paragraph; Tags 0E4G,
094A and 09SP.
(blueprint: lem-sc-supported-perfect-factorization).

Proof: Choose the supported perfect generator E for the closed complement of V.
Express K as the telescope of a sequence starting at zero, with attaching terms
coproducts of shifts of E (0E4G). Perfect P is compact in D_QCoh(Y) (09M1).
Compact Hom commutes with the telescope (094A), so the given map factors through
some finite stage. Inverse-rotate the transition triangles. Their first terms
are coproducts of shifts of E, including the initial zero term as the empty sum.
Apply the finite-stage factorization lemma (09SP) to factor through a finite
thick object R generated by E. Finite sums, shifts, cones and retracts of perfect
objects are perfect (08CR, 08CS). Restriction to V preserves these operations;
since E restricts to zero, R restricts to zero. Compose the map R to the finite
stage with its map to K. For stage zero, take R zero. The same argument covers
empty V, V equal to Y, and the zero map. -/
theorem supported_perfect_factorization
    (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (V : Y.Opens) [CompactSpace (V : Set Y)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (P K : schemeDerivedCategory Y) (hP : Scheme.IsPerfect Y P)
    (hK : schemeDerivedQCohProperty Y K)
    (hzero : IsZero ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace)
      V).mapDerivedCategory.obj K)) (f : P ⟶ K) :
    ∃ (R : schemeDerivedCategory Y) (a : P ⟶ R) (b : R ⟶ K),
      Scheme.IsPerfect Y R ∧
      IsZero ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace)
        V).mapDerivedCategory.obj R) ∧ a ≫ b = f := by
  classical
  let A := schemeDerivedQCohProperty Y
  have : A.IsTriangulated := by
    simpa using supported_qcoh_isTriangulated Y Set.univ
  have : A.IsClosedUnderIsomorphisms := by
    constructor
    intro M N e hM n
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e) (hM n)
  let : HasCoproducts.{u} A.FullSubcategory := derivedQCohDirectSums Y
  have (I : Type u) : A.IsClosedUnderColimitsOfShape (Discrete I) :=
    schemeDerivedQCohClosedUnderCoproducts Y I
  let P' : A.FullSubcategory := ⟨P, schemeDerivedQCohProperty_of_isPerfect Y P hP⟩
  let K' : A.FullSubcategory := ⟨K, hK⟩
  obtain ⟨G, hG, hGsupp, hbuild⟩ := supported_derived_generated_perfect Y V
    (isCompact_iff_compactSpace.mpr inferInstance)
  obtain ⟨X, t, hzero, hsteps, S, ⟨hS⟩, s, q, r, hs, hT⟩ := hbuild K'
    (fun n x hx ↦ stalk_subsingleton_of_restriction_zero Y V K hzero n x hx)
  obtain ⟨n, fstage, hfstage⟩ := telescope_factor A P'
    (perfectObjectCompact Y P' hP) K' (ObjectProperty.homMk f) X t S hS s q r hs hT
  let tA : ∀ n : ℕ, X n ⟶ X (n + 1) := fun n ↦ ObjectProperty.homMk (t n)
  -- An empty coproduct supplies the initial stage, including the zero-stage case.
  have hinitial : ∃ (J : Type u) (i : J → PUnit.{u + 1}) (m : J → ℤ),
      Nonempty (X 0 ≅ ∐ fun j : J ↦ G⟦m j⟧) := by
    refine ⟨PEmpty.{u + 1}, PEmpty.elim, PEmpty.elim, ?_⟩
    have hz : IsZero (X 0) := .of_full_of_faithful_of_isZero A.ι _ hzero
    have hz' : IsZero (∐ fun j : PEmpty.{u + 1} ↦ G⟦(PEmpty.elim j : ℤ)⟧) := by
      rw [IsZero.iff_id_eq_zero]
      apply Sigma.hom_ext
      intro j
      exact j.elim
    exact ⟨hz.iso hz'⟩
  choose I m B hB a b hdist using hsteps
  have hAB (k : ℕ) : A (B k).pt :=
    A.ext_of_isTriangulatedClosed₃ _ (hdist k) (X k).property (X (k + 1)).property
  let B' (k : ℕ) : A.FullSubcategory := ⟨(B k).pt, hAB k⟩
  let T (k : ℕ) : Pretriangulated.Triangle A.FullSubcategory :=
    Pretriangulated.Triangle.mk (tA k)
      (ObjectProperty.homMk (a k) : X (k + 1) ⟶ B' k)
      (ObjectProperty.homMk (b k ≫ (A.ι.commShiftIso (1 : ℤ)).inv.app (X k)) :
        B' k ⟶ (X k)⟦(1 : ℤ)⟧)
  have hTA (k : ℕ) : T k ∈ distTriang A.FullSubcategory := by
    change A.ι.mapTriangle.obj _ ∈ distTriang (schemeDerivedCategory Y)
    change Pretriangulated.Triangle.mk (t k) (a k)
      ((b k ≫ (A.ι.commShiftIso (1 : ℤ)).inv.app (X k)) ≫
        (A.ι.commShiftIso (1 : ℤ)).hom.app (X k)) ∈ distTriang (schemeDerivedCategory Y)
    rw [Category.assoc, Iso.inv_hom_id_app]
    change Pretriangulated.Triangle.mk (t k) (a k) (b k ≫ 𝟙 _) ∈
      distTriang (schemeDerivedCategory Y)
    rw [Category.comp_id]
    exact hdist k
  have hstages : ∃ (Z : ℕ → A.FullSubcategory) (a : ∀ k : ℕ, Z k ⟶ X k)
      (b : ∀ k : ℕ, X (k + 1) ⟶ (Z k)⟦(1 : ℤ)⟧),
      (∀ k : ℕ, ∃ (J : Type u) (i : J → PUnit.{u + 1}) (m : J → ℤ),
        Nonempty (Z k ≅ ∐ fun j : J ↦ G⟦m j⟧)) ∧
      ∀ k : ℕ, Pretriangulated.Triangle.mk (a k) (tA k) (b k) ∈
        distTriang A.FullSubcategory := by
    refine ⟨fun k ↦ (T k).invRotate.obj₁, fun k ↦ (T k).invRotate.mor₁,
      fun k ↦ (T k).invRotate.mor₃, ?_, ?_⟩
    · intro k
      obtain ⟨e⟩ := ambient_shift_coproduct_iso A G (m k) (B k) (hB k).some (hAB k)
      refine ⟨I k, fun _ ↦ PUnit.unit, fun j ↦ m k j + -1, ⟨?_⟩⟩
      exact (shiftFunctor A.FullSubcategory (-1 : ℤ)).mapIso e ≪≫
        (asIso (sigmaComparison (shiftFunctor A.FullSubcategory (-1 : ℤ))
          (fun j : I k ↦ G⟦m k j⟧))).symm ≪≫
        Sigma.mapIso (fun j ↦ ((shiftFunctorAdd A.FullSubcategory (m k j) (-1)).app G).symm)
    · intro k
      exact Pretriangulated.inv_rot_of_distTriang _ (hTA k)
  obtain ⟨J, Q, α, β, hQ, hαβ⟩ := compact_factorThrough_thickClosure
    (fun _ : PUnit.{u + 1} ↦ G) (fun _ ↦ perfectObjectCompact Y G hG) X tA
    hinitial hstages P' (perfectObjectCompact Y P' hP) n
    (ObjectProperty.homMk fstage)
  -- Restriction vanishing and perfectness both define thick properties.
  let F := (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V).mapDerivedCategory
  let Z : ObjectProperty (schemeDerivedCategory Y) := fun M ↦ IsZero (F.obj M)
  have : Z.IsClosedUnderIsomorphisms := by
    constructor
    intro M N e hM
    exact hM.of_iso (F.mapIso e.symm)
  have : Z.ContainsZero := ⟨0, isZero_zero _, F.map_isZero (isZero_zero _)⟩
  have : Z.IsStableUnderShift ℤ := by
    constructor
    intro j
    constructor
    intro M hM
    exact ((shiftFunctor _ j).map_isZero hM).of_iso ((F.commShiftIso j).app M)
  have : Z.IsTriangulatedClosed₂ := by
    apply ObjectProperty.IsTriangulatedClosed₂.mk'
    intro T ht h₁ h₃
    exact (F.mapTriangle.obj T).isZero₂_of_isZero₁₃ (F.map_distinguished T ht) h₁ h₃
  have : Z.IsTriangulated := ObjectProperty.IsTriangulated.mk
  have : Z.IsStableUnderRetracts := by
    constructor
    intro M N r hN
    change IsZero (F.obj M)
    change IsZero (F.obj N) at hN
    rw [IsZero.iff_id_eq_zero]
    have he := congrArg F.map r.retract
    rw [Functor.map_comp, CategoryTheory.Functor.map_id] at he
    rw [← he, hN.eq_zero_of_src (F.map r.r), comp_zero]
  obtain ⟨hperftri, hperfretract⟩ := perfect_thick_property Y G.obj hG
  let := hperftri
  let := hperfretract
  let D := Scheme.perfectSubcategory Y ⊓ Z
  have : D.IsStableUnderRetracts := ⟨fun r h ↦
    ⟨(Scheme.perfectSubcategory Y).prop_of_retract r h.1, Z.prop_of_retract r h.2⟩⟩
  have hGD : D G.obj := ⟨hG,
    supported_derived_restriction_zero Y (V : Set Y)ᶜ V (by simp) G.obj
      (fun j x hx ↦ hGsupp j x (by simpa using hx))⟩
  let R : ObjectProperty A.FullSubcategory := D.inverseImage A.ι
  have : R.IsStableUnderRetracts := ⟨fun r h ↦ D.prop_of_retract (r.map A.ι) h⟩
  have hG' : R G := hGD
  have hsum : R (∐ fun i : {i : PUnit.{u + 1} // i ∈ J} ↦ G) := by
    let E := fun _ : {i : PUnit.{u + 1} // i ∈ J} ↦ G
    have : HasFiniteCoproducts A.FullSubcategory := hasFiniteCoproducts_of_hasCoproducts _
    have : HasFiniteBiproducts A.FullSubcategory := HasFiniteBiproducts.of_hasFiniteCoproducts
    apply R.prop_of_iso ((biproduct.isoCoproduct E).symm ≪≫ biproduct.isoProduct E).symm
    exact R.prop_product (fun _ ↦ hG')
  have hQR : R Q := ((ObjectProperty.triangEnvelope_le_iff _).mpr
    (ObjectProperty.singleton_le_iff.mpr hsum)) Q hQ
  refine ⟨Q.obj, α.hom, β.hom ≫ S.inj n ≫ q, hQR.1, hQR.2, ?_⟩
  rw [← Category.assoc α.hom β.hom]
  rw [show α.hom ≫ β.hom = fstage from congrArg InducedCategory.Hom.hom hαβ]
  exact hfstage

end AlgebraicGeometry
