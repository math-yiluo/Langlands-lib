/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import WeilConjectures.AlgebraicGeometry.Curve.CoefficientPair
import all WeilConjectures.AlgebraicGeometry.Curve.DenseOpenBaseChange
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.CategoryTheory.Sites.Point.Linear

/-!
# DenseOpenBaseChangeComparison

Source: Stacks Project, Lemma 0GJA.
(blueprint: lem-pbc-j2-dense-open-base-change-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Changing abelian coefficients to modules over the lifted integers commutes with
extension by zero followed by restriction.
Source: Stacks Project, Tag 0GJA, open-closed reduction. The coefficient transport is
formal uniqueness of left adjoints (`Adjunction.leftAdjointUniq`).

Proof: The inverse of the equivalence from integer modules to abelian groups, followed
by restriction along ULift Z ≃ Z, is an equivalence E. Postcomposition by E and its
inverse give inverse equivalences on the sheaf categories. Open restriction is
precomposition on the localized site, so commutes with postcomposition by E.
The two composites of extension by zero with E are left adjoints to the same functor,
after transporting across these equivalences. Uniqueness of left adjoints gives their
natural isomorphism. Apply it to the restriction of A and use the restriction comparison.
No density, curve, constructibility or torsion assumption is used. This includes empty
opens and the identity open. -/
private theorem dense_open_coefficient_iso {X : Scheme.{u}}
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : X.Opens) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    Nonempty ((sheafCompose X.smallEtaleTopology E).obj
      ((Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj A)) ≅
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).obj
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).obj
          ((sheafCompose X.smallEtaleTopology E).obj A))) := by
  let R := ULift.{u + 1} ℤ
  let E : AddCommGrpCat.{u + 1} ⥤ ModuleCat.{u + 1} R :=
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : R ≃+* ℤ).toRingHom
  let D := E.inv
  have adj (Y : Scheme.{u}) :
      sheafCompose Y.smallEtaleTopology E ⊣ sheafCompose Y.smallEtaleTopology D :=
    Adjunction.restrictFullyFaithful ((Functor.adjunction E).whiskerRight Y.Etaleᵒᵖ)
      (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
      (Iso.refl _) (Iso.refl _)
  have adj₁ := (Etale.openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} U.ι).comp
    (adj X)
  have adj₂ := (adj U).comp
    (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) U.ι)
  have er : sheafCompose X.smallEtaleTopology D ⋙
        Etale.openImmersionRestriction AddCommGrpCat.{u + 1} U.ι ≅
      Etale.openImmersionRestriction (ModuleCat.{u + 1} R) U.ι ⋙
        sheafCompose U.toScheme.smallEtaleTopology D := Iso.refl _
  let ei := adj₁.leftAdjointUniq (adj₂.ofNatIsoRight er.symm)
  refine ⟨?B⟩
  exact (ei.app ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj A)) ≪≫
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) U.ι).mapIso
      (((sheafCompose U.toScheme.smallEtaleTopology E).mapIso
        ((Etale.upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} U.ι).app A)) ≪≫
        ((Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} R) U.ι).app
          ((sheafCompose X.smallEtaleTopology E).obj A)).symm)

private theorem cohomology_iso_bijective {X : Scheme.{u}}
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : A ≅ B) (q : ℕ) : Function.Bijective (Sheaf.H.map e.hom q) := by
  refine ⟨?_, ?_⟩
  · intro x y h
    have := congrArg (Sheaf.H.map e.inv q) h
    simpa only [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply] using this
  · intro y
    refine ⟨Sheaf.H.map e.inv q y, ?_⟩
    rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]

private theorem comparison_iso_iff {X Y : Scheme.{u}} (a : Y ⟶ X)
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : A ≅ B) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap a A q) ↔
      Function.Bijective (Etale.cohomologyMap a B q) :=
  IsCurve.bijective_square_iff _ _ _ _ (cohomology_iso_bijective e q)
    (cohomology_iso_bijective ((Etale.upperStar _ a).mapIso e) q)
    (fun x ↦ Etale.cohomologyMap_map a q e.hom x)

/-- Source: Stacks Project, Lemma 0GJA, proof, with Lemma 095L.
(blueprint: lem-pbc-j2-dense-open-base-change-comparison).

Proof: Form the open-closed short exact sequence with quotient Q = i_* i^* F supported on
the finite set Z of k-rational closed points. Finite direct image and zero-dimensional
cohomology identify H^q(X,Q) with zero for q > 0 and H^0 with the finite product of its
geometric stalks. After any algebraically closed field extension this product is
unchanged, and the canonical pullback map is bijective. Pullback gives an exact sequence
on the base changed curve and a commuting long exact cohomology ladder. If comparison
is bijective for G, the five lemma applied with the comparisons for Q proves it for F.
Conversely, if comparison is bijective for F, the segment H^(q-1)(F) → H^(q-1)(Q) →
H^q(G) → H^q(F) → H^q(Q), with the preceding terms zero in degree zero, and the five lemma
prove bijectivity for G. Properness supplies the comparison hypotheses without a
torsion restriction. In the invertible-order case the required order condition passes
to subobjects and quotients. If F is primary while G has invertible order, G is zero
by geometric stalk conservativity, so every comparison for G is bijective. These are
the two cases in the displayed torsion alternative.
-/
theorem IsCurve.dense_open_baseChange_comparison {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k)
    (U : P.C.Opens) (hU : Dense (U : Set P.C)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let F' := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
    let G := (sheafCompose P.C.smallEtaleTopology E).obj F'
    (IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) P.toSpec G →
      IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) P.toSpec F) ∧
    ((Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
      ∃ p : ℕ, p.Prime ∧ CharP k p ∧
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
      IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) P.toSpec F →
      IsCurve.BaseChangeOfInvertibleOrder (ULift.{u + 1} ℤ) P.toSpec G) ∧
    (IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) P.toSpec G →
      IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) P.toSpec F) ∧
    ((Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
      ∃ p : ℕ, p.Prime ∧ CharP k p ∧
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
      IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) P.toSpec F →
      IsCurve.BaseChangeOfIsProper (ULift.{u + 1} ℤ) P.toSpec G) := by
  classical
  have : IsCurve P.toSpec := P.isCurve
  have : LocallySmall.{u} P.C.Etale := locallySmall_self _
  dsimp only
  let R := ULift.{u + 1} ℤ
  have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} R) :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : R ≃+* ℤ).toRingHom
  let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
  let G := (sheafCompose P.C.smallEtaleTopology E).obj
    ((Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F))
  let K := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) U.ι).obj
    ((Etale.upperStar (ModuleCat.{u + 1} R) U.ι).obj F)
  obtain ⟨e⟩ := dense_open_coefficient_iso P.F U
  change G ≅ K at e
  let ε : K ⟶ F :=
    (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) U.ι).counit.app F
  have hseq := Etale.shortExact_openClosedShortComplex (ModuleCat.{u + 1} R)
    U.ι U.ι.closedComplement F U.ι.range_closedComplement
  have : Mono ε := hseq.mono_f
  let m : G ⟶ F := e.hom ≫ ε
  have : Mono m := inferInstance
  have order_subobject [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F] :
      Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) G := by
    constructor
    intro Ω _ _ s x
    let T : Sheaf P.C.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
        ModuleCat.{u + 1} R := (Scheme.pointSmallEtale s).sheafFiber
    have : Limits.PreservesFiniteLimits T := inferInstance
    obtain ⟨n, hn, hu, hx⟩ :=
      Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
        (S := Spec (.of k)) Ω s (T.map m x)
    refine ⟨n, hn, hu, (ModuleCat.mono_iff_injective (T.map m)).mp inferInstance ?_⟩
    simpa only [map_nsmul, map_zero] using hx
  have primary_subobject (p : ℕ) (hp : Scheme.IsPrimaryTorsionSheaf R F p) :
      Scheme.IsPrimaryTorsionSheaf R G p := by
    intro Ω _ _ s x
    let T : Sheaf P.C.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
        ModuleCat.{u + 1} R := (Scheme.pointSmallEtale s).sheafFiber
    have : Limits.PreservesFiniteLimits T := inferInstance
    obtain ⟨n, hn⟩ := hp Ω s (T.map m x)
    refine ⟨n, (ModuleCat.mono_iff_injective (T.map m)).mp inferInstance ?_⟩
    simpa only [map_nsmul, map_zero] using hn
  let V := sheafCompose P.C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
  have compare (k' : Type u) [Field k'] [IsAlgClosed k'] {X' : Scheme.{u}}
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of k')}
      {ι' : X' ⟶ P.C} (h : IsPullback ι' f' P.toSpec ι) :
      (∀ q, Function.Bijective (Etale.cohomologyMap ι' (V.obj F) q)) ↔
        (∀ q, Function.Bijective (Etale.cohomologyMap ι' (V.obj G) q)) := by
    have hc := IsCurve.dense_open_all_base_change R P.toSpec h F U hU
    constructor
    · intro hf q
      exact (comparison_iso_iff ι' (V.mapIso e) q).mpr (hc.mp hf q)
    · intro hg
      exact hc.mpr (fun q ↦ (comparison_iso_iff ι' (V.mapIso e) q).mp (hg q))
  have primary_comparison (p : ℕ) (hp : p.Prime) [CharP k p]
      (hprim : Scheme.IsPrimaryTorsionSheaf R G p)
      [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) G]
      {Y : Scheme.{u}} (a : Y ⟶ P.C) (q : ℕ) :
      Function.Bijective (Etale.cohomologyMap a (V.obj G) q) := by
    have hz : Limits.IsZero G := by
      apply (Limits.IsZero.iff_id_eq_zero G).mpr
      apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
      intro s
      let T := (Scheme.pointSmallEtale (P.C.algClosurePoint s)).sheafFiber
        (A := ModuleCat.{u + 1} R)
      have hzero : T.map (0 : G ⟶ G) = 0 := by
        simpa only [zero_smul] using
          (Scheme.pointSmallEtale (P.C.algClosurePoint s)).sheafFiber_map_smul (0 : ℕ) (𝟙 G)
      change T.map (𝟙 G) = T.map (0 : G ⟶ G)
      rw [CategoryTheory.Functor.map_id, hzero]
      ext x
      obtain ⟨n, -, hn, hx⟩ :=
        Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
          (S := Spec (.of k)) _ (P.C.algClosurePoint s) x
      obtain ⟨b, hb⟩ := hprim _ (P.C.algClosurePoint s) x
      have hcop : (p ^ b).Coprime n := by
        apply Nat.Coprime.pow_left b
        apply hp.coprime_iff_not_dvd.mpr
        intro hd
        have hn' : IsUnit (n : k) := by
          simpa only [map_natCast] using hn.map (Scheme.ΓSpecIso (.of k)).hom.hom
        have hn0 : (n : k) = 0 := (CharP.cast_eq_zero_iff k p n).mpr hd
        rw [hn0] at hn'
        exact not_isUnit_zero hn'
      simpa using (nsmul_eq_zero_iff_of_coprime hcop).mp ⟨hb, hx⟩
    have hzV : Limits.IsZero (V.obj G) := by
      apply (Limits.IsZero.iff_id_eq_zero _).mpr
      have hh := congrArg V.map ((Limits.IsZero.iff_id_eq_zero G).mp hz)
      have hzero : V.map (0 : G ⟶ G) = 0 := by
        ext W x
        rfl
      simpa only [CategoryTheory.Functor.map_id, hzero] using hh
    have hs := Sheaf.subsingleton_H_of_isZero hzV q
    have ht := Sheaf.subsingleton_H_of_isZero
      ((Etale.upperStar AddCommGrpCat.{u + 1} a).map_isZero hzV) q
    exact ⟨fun x y _ ↦ hs.elim x y, fun y ↦ ⟨0, ht.elim _ y⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hg _ k' _ _ X' ι f' ι' h
    have := order_subobject
    exact (compare k' h).mpr (hg k' h)
  · intro ht hf _ k' _ _ X' ι f' ι' h
    rcases ht with horder | ⟨p, hp, hchar, hprim⟩
    · have := horder
      exact (compare k' h).mp (hf k' h)
    · have := hchar
      exact fun q ↦ primary_comparison p hp (primary_subobject p hprim) ι' q
  · intro hg _ k' _ _ X' ι f' ι' h
    exact (compare k' h).mpr (hg k' h)
  · intro _ hf _ k' _ _ X' ι f' ι' h
    exact (compare k' h).mp (hf k' h)

end AlgebraicGeometry
