/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFiniteExtension


public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Coherent

import all WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.FinitePresentationIntegralFiltration
import WeilConjectures.AlgebraicGeometry.IntegralIdealProperCohomology
import WeilConjectures.AlgebraicGeometry.CohomologyFiniteExtensionExtension
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import Mathlib.Data.Int.Interval
import all WeilConjectures.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh
import all WeilConjectures.CategoryTheory.HalfPlaneWeakConvergence

/-! # Bounded coherent direct image in the Noetherian proper case

Source: Stacks Project, Tag 08E2, specialized to a proper morphism; Tag 02O5.
(blueprint: lem-pc-noetherian-proper-bounded-coherent-image).
-/

@[expose] public section
set_option autoImplicit false
universe u wY wT
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Finite generators and coherent relations give finite local presentations. -/
private theorem finitePresentation_of_coherent {X : Scheme.{u}}
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (h : RingedSpace.IsCoherent X.toRingedSpace F) :
    SheafOfModules.IsFinitePresentation.{u} (R := X.ringCatSheaf) F := by
  classical
  have (V : X.Opens) : HasWeakSheafify
      ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u} := inferInstance
  have (V : X.Opens) : ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  have : SheafOfModules.IsFiniteType.{u} (R := X.ringCatSheaf) F := h.1
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData.{u} F
  have hfp (i : q.I) : (F.over (q.X i)).IsFinitePresentation := by
    have := hq.isFiniteType i
    let _ := Fintype.ofFinite (q.generators i).I
    let n := Fintype.card (q.generators i).I
    let e := (SheafOfModules.freeFunctor (R := X.ringCatSheaf.over (q.X i))).mapIso
      ((Equiv.ulift.trans (Fintype.equivFin (q.generators i).I).symm).toIso)
    let f := e.hom ≫ (q.generators i).π
    have : Epi f := inferInstanceAs (Epi (e.hom ≫ (q.generators i).π))
    let G := SheafOfModules.GeneratingSections.ofEpiFree f
    have : G.IsFiniteType := ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩
    have : (Limits.kernel G.π).IsFiniteType := by
      simpa only [G, SheafOfModules.GeneratingSections.ofEpiFree_π]
        using h.2 (q.X i) n f
    exact Modules.isFinitePresentation_of_generators_kernel.{u} (F.over (q.X i)) G
  have : SheafOfModules.IsFinitePresentation.{u} (R := X.ringCatSheaf) F := by
    exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _
      F q.I q.X q.coversTop hfp
  infer_instance

namespace Modules

/-- Integral-ideal devissage gives finite cohomology over an affine base (Tag 02O6). -/
private theorem finite_sections_proper {X T : Scheme.{u}} (f : X ⟶ T) [IsProper f]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Module.Finite Γ(T, ⊤) Γ((higherDirectImage f q).obj ℱ, ⊤) := by
  classical
  have : IsLocallyNoetherian T := isLocallyNoetherian_of_isOpenImmersion T.isoSpec.hom
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  let R := Γ(T, ⊤)
  let P (M : X.Modules) : Prop := ∀ n : ℕ,
    letI : Module R (M.H n) := Module.compHom _ f.appTop.hom
    Module.Finite R (M.H n)
  have hzero (M : X.Modules) (hM : IsZero M) : P M := by
    intro n
    let : Module R (M.H n) := Module.compHom _ f.appTop.hom
    have hz (x : M.H n) : x = 0 := by
      have h := congrArg (fun φ ↦ H.map φ n x) (hM.eq_of_src (𝟙 M) 0)
      simpa only [H.map_id_apply, H.map_zero_apply] using h
    have : Subsingleton (M.H n) := ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
    infer_instance
  have hiso {M N : X.Modules} (e : M ≅ N) (hM : P M) : P N := by
    intro n
    let : Module R (M.H n) := Module.compHom _ f.appTop.hom
    let : Module R (N.H n) := Module.compHom _ f.appTop.hom
    let eR : M.H n ≃ₗ[R] N.H n :=
      { H.mapLinearEquiv e n with
        map_smul' := fun a x ↦ (H.mapLinearEquiv e n).map_smul (f.appTop a) x }
    have := hM n
    exact Module.Finite.equiv eR
  obtain ⟨m, c, hc, hbot, htop, hpieces⟩ :=
    exists_finitePresentation_integral_filtration X ℱ
  have hpc : ∀ j : Fin (m + 1), P (c j : X.Modules) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      apply hzero
      exact (Subobject.isoOfEq _ _ hbot ≪≫ Subobject.botCoeIsoZero).isZero_iff.mpr
        (isZero_zero X.Modules)
    | succ j ih =>
      let a := Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ)
      let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel a }
      obtain ⟨Z, i, hi, hZ, I, ⟨e⟩⟩ := hpieces j
      have := hi
      have := hZ
      have hI : P ((pushforward i).obj I.toModules) := by
        intro n
        exact finite_H_pushforward_integral_ideal f Z i I n
      have hQ : P (cokernel a) := hiso e.symm hI
      intro n
      exact finite_H_of_shortExact_extension R f.appTop.hom S hS n (ih n) (hQ n)
  have hF : P ℱ := hiso
    (Subobject.isoOfEq _ _ htop ≪≫ asIso (⊤ : Subobject ℱ).arrow) (hpc _)
  let : Module R (ℱ.H q) := Module.compHom _ f.appTop.hom
  have := hF q
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H f ℱ q
  let eR : Γ((higherDirectImage f q).obj ℱ, ⊤) →ₗ[R] ℱ.H q :=
    { e.toAddMonoidHom with map_smul' := fun a x ↦ e.map_smulₛₗ a x }
  exact Module.Finite.equiv (LinearEquiv.ofBijective eR he).symm


/-- Higher direct images of a finitely presented quasi-coherent module have finite
global sections over a Noetherian affine base under a proper morphism.
Source: Stacks Project, Tag 02O6, by integral-ideal devissage. -/
theorem finite_sections_proper_on_affine {X T : Scheme.{u}} (f : X ⟶ T) [IsProper f]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsFinitePresentation]
    [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] [F.IsQuasicoherent] (q : ℕ) :
    Module.Finite Γ(T, ⊤) Γ((higherDirectImage f q).obj F, ⊤) :=
  finite_sections_proper f F q


/-- Affine-local finite cohomology gives coherent higher direct images (Tag 02O5). -/
private theorem finitePresentation_higherDirectImage_proper
    {X T : Scheme.{u}} (f : X ⟶ T) [IsProper f]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    [IsLocallyNoetherian T]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsFinitePresentation := by
  have hP (V : T.Opens) (hV : IsAffineOpen V) :
      ∃ P : (((higherDirectImage f q).obj ℱ).restrict hV.fromSpec).Presentation, P.IsFinite := by
    have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : IsNoetherianRing Γ(Spec Γ(T, V), ⊤) :=
      isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso Γ(T, V)).commRingCatIsoToRingEquiv.symm
    have := isGrothendieckAbelian (Limits.pullback f hV.fromSpec)
    obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f ℱ hV.fromSpec _ _
      (IsPullback.of_hasPullback f hV.fromSpec) q
    have : ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation (Limits.pullback f hV.fromSpec).ringCatSheaf).prop_of_iso
        ((restrictFunctorIsoPullback _).app ℱ) (isFinitePresentation_restrictFunctor _ ℱ)
    have : ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Limits.pullback f hV.fromSpec).ringCatSheaf).prop_of_iso
        ((restrictFunctorIsoPullback _).app ℱ) (isQuasicoherent_restrictFunctor _ ℱ)
    have := finite_sections_proper (pullback.snd f hV.fromSpec)
      ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ) q
    let φ : Γ((higherDirectImage (pullback.snd f hV.fromSpec) q).obj
        ((Modules.pullback (pullback.fst f hV.fromSpec)).obj ℱ), ⊤) →ₗ[Γ(Spec Γ(T, V), ⊤)]
        Γ(((higherDirectImage f q).obj ℱ).restrict hV.fromSpec, ⊤) :=
      { toFun := e.hom.app ⊤, map_add' := map_add _, map_smul' := Hom.app_smul e.hom }
    have : Module.Finite Γ(Spec Γ(T, V), ⊤)
        Γ(((higherDirectImage f q).obj ℱ).restrict hV.fromSpec, ⊤) :=
      Module.Finite.of_surjective φ (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
    have := finite_sections_top_of_finite
      (((higherDirectImage f q).obj ℱ).restrict hV.fromSpec)
    have := isQuasicoherent_higherDirectImage f ℱ q
    exact exists_presentation_isFinite _
  have (V : T.affineOpens) : IsOpenImmersion (IsAffineOpen.fromSpec (U := V.1) V.2) :=
    IsAffineOpen.isOpenImmersion_fromSpec V.2
  choose P _ using fun V : T.affineOpens ↦ hP V.1 V.2
  refine isFinitePresentation_of_iSup_opensRange_eq_top _ _ ?_ P
  exact (iSup_congr fun V ↦ IsAffineOpen.opensRange_fromSpec V.2).trans
    (iSup_affineOpens_eq_top T)

end Modules

/-- A proper morphism over a Noetherian base preserves bounded coherent cohomology.
This asserts neither a finite-free representative nor pseudo-coherence or a base-change
comparison. Source: Stacks Project, Tag 08E2, Lemma 36.11.3; Tag 02O5.

Proof: Coherence makes every cohomology sheaf quasi-coherent and finite type on the
locally Noetherian source. Its nonzero-stalk locus is closed. Because p is proper, the
closed support is proper over T. Apply the hypercohomology spectral sequence for derived
pushforward. Its E2 terms are the higher direct images of these coherent sheaves, hence
coherent by proper coherence over a Noetherian base (Tag 02O5). In each total degree its
finite filtration has coherent subquotients, so the abutment is coherent. The lower
bound is the lower bound of A, since pushforward is left exact. For the upper bound,
p is quasi-compact and separated and T is quasi-compact. A finite affine cover yields a
uniform bound on the higher direct images of quasi-coherent modules; equivalently use
the derived uniform truncation bound of Tag 08D5. Shift A by its upper cohomology bound
and apply this bound, then shift back. This gives a finite interval containing all image
cohomology. The zero object gives zero image. For an empty source the image is zero.
No relative flatness, finite Tor dimension or finite-free image is used.

The existing proper-support direct-image module cannot be imported here: its current
proof dependencies reach the arbitrary-base pseudo-coherence item. This strictly
Noetherian proper case isolates the calculation needed before approximation pullback.
(blueprint: lem-pc-noetherian-proper-bounded-coherent-image). -/
theorem noetherian_proper_directImage_bounded_coherent
    {Y T : Scheme.{u}} [IsNoetherian T] (p : Y ⟶ T)
    [IsProper p]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wT}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (A : schemeDerivedCategory Y)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A))
    (hcoherent : ∀ i : ℤ, RingedSpace.IsCoherent Y.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj A)) :
    (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj
          ((schemeDerivedDirectImage p).obj A))) ∧
    (∀ i : ℤ, RingedSpace.IsCoherent T.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj
          ((schemeDerivedDirectImage p).obj A))) := by
  let f := p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  classical
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings T.toRingedSpace)
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let P : ObjectProperty B := RingedSpace.IsCoherent T.toRingedSpace
  let : Zero B := HasZeroObject.zero' B
  have hclosure := RingedSpace.coherent_kernel_cokernel_sum T.toRingedSpace
  have : P.ContainsZero := ⟨⟨(0 : SheafOfModules.{u} (moduleRings T.toRingedSpace)),
    isZero_zero _, hclosure.2.2.2.1⟩⟩
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ hclosure.2.2.2.2 _ _ e h⟩
  obtain ⟨a, b, hab⟩ := hbounded
  have : A.IsGE a := (DerivedCategory.isGE_iff A a).2
    (fun i hi ↦ hab i (Or.inl hi))
  have : Limits.PreservesFiniteLimits F := by
    change Limits.PreservesFiniteLimits (Scheme.Modules.pushforward f)
    infer_instance
  have : IsGrothendieckAbelian.{u} Y.Modules := Scheme.Modules.isGrothendieckAbelian Y
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE A a
  let Kplus : CochainComplex.Plus C := ⟨K, a, hK⟩
  have ha : ∀ q : ℤ, q < a → Limits.IsZero (Kplus.obj.homology q) := by
    intro q hq
    exact (K.exactAt_of_isGE a q hq).isZero_homology
  obtain ⟨Z, _, _, _, _, _, hsecond, hneg, _, _, _, _, _, _, _, _, _, hconv⟩ :=
    exists_truncationHypercohomology F Kplus a ha
  let eH (q : ℤ) := (DerivedCategory.homologyFunctor C q).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors C q).app K
  have hKcoh (q : ℤ) : RingedSpace.IsCoherent Y.toRingedSpace (Kplus.obj.homology q) :=
    (RingedSpace.coherent_kernel_cokernel_sum Y.toRingedSpace).2.2.2.2
      _ _ (eH q) (hcoherent q)
  have hsecondCoh : ∀ p q : ℤ, P (Z.E p q) := by
    intro p q
    by_cases hp : p < 0
    · exact P.prop_of_isZero (hneg p q hp)
    · obtain ⟨_, _, eK, _⟩ := hsecond p.toNat q
      have hRq : P ((F.rightDerived p.toNat).obj (Kplus.obj.homology q)) := by
        have : (Kplus.obj.homology q).IsFinitePresentation :=
          finitePresentation_of_coherent _ (hKcoh q)
        have : (Kplus.obj.homology q).IsQuasicoherent := inferInstance
        have : ((Scheme.Modules.higherDirectImage f p.toNat).obj
            (Kplus.obj.homology q)).IsFinitePresentation :=
          Modules.finitePresentation_higherDirectImage_proper f _ p.toNat
        change RingedSpace.IsCoherent T.toRingedSpace
          ((Scheme.Modules.higherDirectImage f p.toNat).obj (Kplus.obj.homology q))
        exact (Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType T _).2
          ⟨inferInstance, inferInstance⟩
      have hEq : P (Z.E (p.toNat : ℤ) q) := P.prop_of_iso eK.symm hRq
      simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ p)] using hEq
  have hpages : ∀ (r : ℕ) (p q : ℤ), P (Z.page r p q) := by
    have hk := (RingedSpace.coherent_kernel_cokernel_sum T.toRingedSpace).1
    suffices h : ∀ (r : ℕ) (p q : ℤ),
        RingedSpace.IsCoherent T.toRingedSpace ((Z.pageCouple r).E p q) by
      intro r p q
      exact h (r - 2) p q
    intro r
    induction r with
    | zero => exact hsecondCoh
    | succ r ih =>
      intro p q
      exact (hk _ _
        (kernel.lift ((Z.pageCouple r).d p q) ((Z.pageCouple r).dInto p q)
          ((Z.pageCouple r).dInto_comp_d p q)) (ih _ _)
        ((hk _ _ ((Z.pageCouple r).d p q) (ih _ _) (ih _ _)).1)).2
  obtain ⟨_, _, H, hH, _, _, _, FH, _, _, _, _, _, _, _, _, _, _, hFHfull, hFHzero, _,
    hnegative, hpositive, _⟩ := hconv
  have hHCoh : ∀ n : ℤ, P (H n) := by
    intro n
    apply AlgebraicGeometry.property_of_filtration P
      (fun C hC h₁ h₃ ↦ (hclosure.2.1 C hC).2.1 h₁ h₃)
      (FH n) (max 0 (n - a + 1)).toNat (hFHfull n 0 (by omega))
    · apply hFHzero
      omega
    · intro p
      by_cases hp : p < 0
      · have hz := (hnegative p (n - p) hp).1
        have heq : p + (n - p) = n := by omega
        rw [heq] at hz
        exact P.prop_of_isZero hz
      · obtain ⟨_, _, psi, grc, _, _, _, _, _⟩ :=
          hpositive p (n - p) (by omega)
        have hqc := hpages (max (p + 3) (n - p - a + 2)).toNat p (n - p)
        have hqc' : P ((FH (p + (n - p))).gradedPiece p) :=
          P.prop_of_iso (grc.symm ≪≫ psi).symm hqc
        have heq : p + (n - p) = n := by omega
        rw [heq] at hqc'
        exact hqc'
  have hcohOut : ∀ n : ℤ, P ((DerivedCategory.homologyFunctor B n).obj
      ((schemeDerivedDirectImage f).obj A)) := by
    intro n
    have hQ : P ((DerivedCategory.homologyFunctor B n).obj
        (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K))) := by
      simpa only [hH] using hHCoh n
    exact P.prop_of_iso
      ((DerivedCategory.homologyFunctor B n).mapIso
        ((schemeDerivedDirectImage f).mapIso e)).symm hQ
  have hbelow : ∀ n : ℤ, n < a → IsZero ((DerivedCategory.homologyFunctor B n).obj
      ((schemeDerivedDirectImage f).obj A)) := by
    intro n hn
    have heq : (FH n).step 0 = ⊤ := hFHfull n 0 (by omega)
    have hbot := hFHzero n 0 (by omega : n - a + 1 ≤ 0)
    have hz : IsZero (H n) := by
      have hb : IsZero ((FH n).step 0 : B) := by
        rw [hbot]
        exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
      rw [heq] at hb
      exact hb.of_iso (asIso (⊤ : Subobject (H n)).arrow).symm
    have hzQ : IsZero ((DerivedCategory.homologyFunctor B n).obj
        (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K))) := by
      simpa only [hH] using hz
    exact hzQ.of_iso ((DerivedCategory.homologyFunctor B n).mapIso
      ((schemeDerivedDirectImage f).mapIso e))
  choose N hN using fun q : ℤ ↦ by
    have : (Kplus.obj.homology q).IsQuasicoherent :=
      ((Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y _).1 (hKcoh q)).1
    exact Scheme.Modules.exists_isZero_higherDirectImage f (Kplus.obj.homology q)
  let c : ℕ := (Finset.Icc a b).sup (fun q ↦ N q + q.toNat)
  have hEabove (p q : ℤ) (hn : (c : ℤ) < p + q) : IsZero (Z.E p q) := by
    by_cases hp : p < 0
    · exact hneg p q hp
    · obtain ⟨_, _, eK, _⟩ := hsecond p.toNat q
      have hRq : IsZero ((F.rightDerived p.toNat).obj (Kplus.obj.homology q)) := by
        by_cases hq : q ∈ Finset.Icc a b
        · have hc : N q + q.toNat ≤ c := Finset.le_sup (f := fun q ↦ N q + q.toNat) hq
          exact hN q p.toNat (by
            have hq' : q ≤ (q.toNat : ℤ) := by omega
            omega)
        · have hz := (hab q (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hq))
          have hzK : IsZero (Kplus.obj.homology q) := hz.of_iso (eH q).symm
          exact (F.rightDerived p.toNat).map_isZero hzK
      have hz : IsZero (Z.E (p.toNat : ℤ) q) := hRq.of_iso eK
      simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ p)] using hz
  have habove : ∃ c : ℤ, ∀ n : ℤ, c < n →
      IsZero ((DerivedCategory.homologyFunctor B n).obj
        ((schemeDerivedDirectImage f).obj A)) := by
    refine ⟨c, ?_⟩
    intro n hn
    have hz : IsZero (H n) := by
      have : ObjectProperty.IsClosedUnderIsomorphisms (IsZero (C := B)) :=
        ⟨fun e h ↦ h.of_iso e.symm⟩
      apply AlgebraicGeometry.property_of_filtration (IsZero (C := B))
        (fun C hC h₁ h₃ ↦ hC.exact.isZero_of_both_isZero h₁ h₃)
        (FH n) (max 0 (n - a + 1)).toNat (hFHfull n 0 (by omega))
      · apply hFHzero
        omega
      · intro p
        by_cases hp : p < 0
        · have hz := (hnegative p (n - p) hp).1
          have heq : p + (n - p) = n := by omega
          rw [heq] at hz
          exact hz
        · obtain ⟨_, _, psi, grc, _, _, _, _, _⟩ := hpositive p (n - p) (by omega)
          have hz : IsZero (Z.page (max (p + 3) (n - p - a + 2)).toNat p (n - p)) :=
            BigradedExactCouple.page_zero Z p (n - p) (hEabove p (n - p) (by omega))
              ((max (p + 3) (n - p - a + 2)).toNat - 2)
          have hz' := hz.of_iso (grc.symm ≪≫ psi)
          have heq : p + (n - p) = n := by omega
          rw [heq] at hz'
          exact hz'
    have hzQ : IsZero ((DerivedCategory.homologyFunctor B n).obj
        (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K))) := by
      simpa only [hH] using hz
    exact hzQ.of_iso ((DerivedCategory.homologyFunctor B n).mapIso
      ((schemeDerivedDirectImage f).mapIso e))
  obtain ⟨c, hc⟩ := habove
  refine ⟨⟨a, c, ?_⟩, hcohOut⟩
  intro n hn
  exact hn.elim (hbelow n) (hc n)


end AlgebraicGeometry.Scheme
