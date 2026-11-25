/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import WeilConjectures.CategoryTheory.ExactCouple
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartKernelsCokernels
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleExtensions
import WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartBound
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Bounded-below proper direct image of ind-constructible complexes

Ind-constructibility is the replete small filtered-colimit closure `ObjectProperty.ind` of the
finite constant-model constructibility predicate in the module-object category, imposed on
every cohomology object. The two
statements use the canonical condensed finite subextension and algebraic-closure rings.
The standing scheme setting is that of the proper-heart theorem used in the proof.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem derived_lower_bound
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : DerivedCategory A) (a : ℤ) (hK : K.IsGE a) :
    (F.rightDerivedFunctor.obj K).IsGE a := by
  let L : DerivedCategory.Plus A := ⟨K, a, hK⟩
  have : L.IsGE a := (L.isGE_ι_obj_iff a).mp hK
  refine (DerivedCategory.isGE_iff _ a).mpr fun q hq ↦ ?_
  exact (F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE L a hq).of_iso
    ((DerivedCategory.homologyFunctor B q).mapIso
      (F.rightDerivedFunctorPlusCompatibility.app L)).symm

private theorem page_property
    {C : Type*} [Category C] [Abelian C] (P : ObjectProperty C)
    (hker : ∀ {A B : C} (f : A ⟶ B), P A → P B → P (kernel f))
    (hcoker : ∀ {A B : C} (f : A ⟶ B), P A → P B → P (cokernel f))
    (S : BigradedExactCouple C 0) (hS : ∀ p q, P (S.E p q)) :
    ∀ (r : ℕ) (p q : ℤ), P ((S.pageCouple r).E p q) := by
  intro r
  induction r with
  | zero => exact hS
  | succ r ih =>
    intro p q
    change P (cokernel (kernel.lift _ _ _))
    exact hcoker _ (ih _ _) (hker _ (ih _ _) (ih _ _))

private theorem page_zero
    {C : Type*} [Category C] [Abelian C]
    (S : BigradedExactCouple C 0) (p q : ℤ) (hS : IsZero (S.E p q)) :
    ∀ r : ℕ, IsZero ((S.pageCouple r).E p q) := by
  intro r
  induction r with
  | zero => exact hS
  | succ r ih =>
    change IsZero (cokernel (kernel.lift _ _ _))
    exact IsZero.of_epi (cokernel.π _) (IsZero.of_mono (kernel.ι _) ih)

private theorem filtration_property
    {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hzero : ∀ M : C, IsZero M → P M)
    (hext : ∀ (S : ShortComplex C), S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    {M : C} (F : PBCDecreasingFiltration M) (hfin : F.IsFinite)
    (hgraded : ∀ p : ℤ, P (F.gradedPiece p)) : P M := by
  obtain ⟨a, b, ha, hb⟩ := hfin
  have hstep : ∀ n : ℕ, P (F.step (b - n) : C) := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, sub_zero, hb]
      exact hzero _ ((isZero_zero C).of_iso Subobject.botCoeIsoZero)
    | succ n ih =>
      let i : ℤ := b - (n + 1 : ℕ)
      let f := Subobject.ofLE (F.step (i + 1)) (F.step i)
        (F.antitone_step (by omega))
      have hi : i + 1 = b - n := by dsimp [i]; omega
      have hleft : P (F.step (i + 1) : C) := by rw [hi]; exact ih
      exact hext (ShortComplex.mk f (cokernel.π f) (cokernel.condition f))
        ⟨ShortComplex.exact_cokernel f⟩ hleft (hgraded i)
  let n : ℕ := (b - min a b).toNat
  have hbn : b - (n : ℤ) = min a b := by dsimp [n]; omega
  have htop : F.step (b - n) = ⊤ := by
    apply top_unique
    rw [← ha]
    apply F.antitone_step
    rw [hbn]
    exact min_le_left _ _
  have hp : P (⊤ : Subobject M) := by simpa only [htop] using hstep n
  exact P.prop_of_iso (asIso (⊤ : Subobject M).arrow) hp

private theorem hypercohomology_property.{u₁, u₂, v₁, v₂}
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [IsGrothendieckAbelian.{v₁} A] [IsGrothendieckAbelian.{v₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (a : ℤ)
    (ha : ∀ q : ℤ, q < a → IsZero (K.obj.homology q))
    (P : ObjectProperty B) [P.IsClosedUnderIsomorphisms]
    (hzero : ∀ M : B, IsZero M → P M)
    (hker : ∀ {M N : B} (f : M ⟶ N), P M → P N → P (kernel f))
    (hcoker : ∀ {M N : B} (f : M ⟶ N), P M → P N → P (cokernel f))
    (hext : ∀ (S : ShortComplex B), S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (hR : ∀ (p : ℕ) (q : ℤ), P ((F.rightDerived p).obj (K.obj.homology q))) :
    ∀ n : ℤ, P ((DerivedCategory.homologyFunctor B n).obj
      (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K.obj))) := by
  obtain ⟨S, _, _, _, _, _, hcomp, hneg, _, _, _, _, _, _, _, _, _, hrest⟩ :=
    exists_truncationHypercohomology F K a ha
  obtain ⟨inc, L, H, hH, j, c, FA, FH, _, _, hstable, _, _, _, _, _, _, _, _, _,
    hfinite, hnegative, hgraded, _⟩ := hrest
  have hE (p q : ℤ) : P (S.E p q) := by
    by_cases hp : 0 ≤ p
    · lift p to ℕ using hp
      obtain ⟨_, _, e, _⟩ := hcomp p q
      exact P.prop_of_iso e.symm (hR p q)
    · exact hzero _ (hneg p q (by omega))
  have hpages := page_property P hker hcoker S hE
  have hinf (p q : ℤ) : P (S.pageInfinity L p q) := by
    obtain ⟨_, _, ⟨e⟩⟩ := hstable p q
    exact P.prop_of_iso e.symm (hpages _ _ _)
  have hHprop (n : ℤ) : P (H n) := by
    apply filtration_property P hzero hext (FH n) (hfinite n).1
    intro p
    by_cases hp : 0 ≤ p
    · obtain ⟨_, _, _, _, _, Theta, _⟩ := hgraded p (n - p) hp
      have hp' := P.prop_of_iso Theta.symm (hinf p (n - p))
      convert hp' using 1
      congr 2 <;> omega
    · apply hzero
      convert (hnegative p (n - p) (by omega)).1 using 1
      congr 2 <;> omega
  simpa only [hH] using hHprop

private theorem hypercohomology_zero.{u₁, u₂, v₁, v₂}
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [IsGrothendieckAbelian.{v₁} A] [IsGrothendieckAbelian.{v₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (a n : ℤ)
    (ha : ∀ q : ℤ, q < a → IsZero (K.obj.homology q))
    (hR : ∀ (p : ℕ) (q : ℤ), (p : ℤ) + q = n →
      IsZero ((F.rightDerived p).obj (K.obj.homology q))) :
    IsZero ((DerivedCategory.homologyFunctor B n).obj
      (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K.obj))) := by
  obtain ⟨S, _, _, _, _, _, hcomp, hneg, _, _, _, _, _, _, _, _, _, hrest⟩ :=
    exists_truncationHypercohomology F K a ha
  obtain ⟨inc, L, H, hH, j, c, FA, FH, _, _, hstable, _, _, _, _, _, _, _, _, _,
    hfinite, hnegative, hgraded, _⟩ := hrest
  have hE (p q : ℤ) (hpq : p + q = n) : IsZero (S.E p q) := by
    by_cases hp : 0 ≤ p
    · lift p to ℕ using hp
      obtain ⟨_, _, e, _⟩ := hcomp p q
      exact (hR p q hpq).of_iso e
    · exact hneg p q (by omega)
  have hinf (p q : ℤ) (hpq : p + q = n) : IsZero (S.pageInfinity L p q) := by
    obtain ⟨_, _, ⟨e⟩⟩ := hstable p q
    exact (page_zero S p q (hE p q hpq) _).of_iso e
  have hHprop : IsZero (H n) := by
    have : ObjectProperty.IsClosedUnderIsomorphisms (IsZero (C := B)) :=
      ⟨fun e h ↦ h.of_iso e.symm⟩
    apply filtration_property (IsZero (C := B)) (fun _ h ↦ h)
      (fun _ hS h₁ h₃ ↦ hS.exact.isZero_of_both_isZero h₁ h₃) (FH n) (hfinite n).1
    intro p
    by_cases hp : 0 ≤ p
    · obtain ⟨_, _, _, _, _, Theta, _⟩ := hgraded p (n - p) hp
      have hp' := (hinf p (n - p) (by omega)).of_iso Theta
      convert hp' using 1
      congr 2 <;> omega
    · convert (hnegative p (n - p) (by omega)).1 using 1
      congr 2 <;> omega
  simpa only [hH] using hHprop

private theorem derived_from_heart.{u₁, u₂, v₁, v₂}
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [IsGrothendieckAbelian.{v₁} A] [IsGrothendieckAbelian.{v₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (P : ObjectProperty A) (Q : ObjectProperty B)
    [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms]
    (hker : ∀ {M N : B} (f : M ⟶ N), Q M → Q N → Q (kernel f))
    (hcoker : ∀ {M N : B} (f : M ⟶ N), Q M → Q N → Q (cokernel f))
    (hext : ∀ (S : ShortComplex B), S.ShortExact → Q S.X₁ → Q S.X₃ → Q S.X₂)
    (c : ℤ)
    (hF : ∀ M : A, P M →
      (∀ q : ℤ, c < q → IsZero ((DerivedCategory.homologyFunctor B q).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A 0).obj M)))) ∧
      (∀ q : ℤ, 0 ≤ q → Q ((DerivedCategory.homologyFunctor B q).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A 0).obj M)))))
    (K : DerivedCategory A)
    (hK : ∀ q : ℤ, P ((DerivedCategory.homologyFunctor A q).obj K))
    (hbelow : ∃ a : ℤ, K.IsGE a) :
    (∀ q : ℤ, Q ((DerivedCategory.homologyFunctor B q).obj (F.rightDerivedFunctor.obj K))) ∧
    (∀ a : ℤ, K.IsGE a → (F.rightDerivedFunctor.obj K).IsGE a) ∧
    (∀ b : ℤ, K.IsLE b → (F.rightDerivedFunctor.obj K).IsLE (b + c)) := by
  classical
  obtain ⟨a, ha⟩ := hbelow
  let K₀ := DerivedCategory.Q.objPreimage K
  let e₀ : DerivedCategory.Q.obj K₀ ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have : (DerivedCategory.Q.obj K₀).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso e₀.symm a
  have : K₀.IsGE a := (DerivedCategory.isGE_Q_obj_iff K₀ a).mp inferInstance
  let L : CochainComplex.Plus A := ⟨K₀.truncGE a, a, inferInstance⟩
  let e : DerivedCategory.Q.obj L.obj ≅ K :=
    (asIso (DerivedCategory.Q.map (K₀.πTruncGE a))).symm ≪≫ e₀
  let eh (q : ℤ) : L.obj.homology q ≅ (DerivedCategory.homologyFunctor A q).obj K :=
    ((DerivedCategory.homologyFunctorFactors A q).app L.obj).symm ≪≫
      (DerivedCategory.homologyFunctor A q).mapIso e
  have hL (q : ℤ) : P (L.obj.homology q) := by
    exact P.prop_of_iso (eh q).symm (hK q)
  have hLa (q : ℤ) (hq : q < a) : IsZero (L.obj.homology q) :=
    (L.obj.exactAt_of_isGE a q hq).isZero_homology
  have hzero (M : B) (hM : IsZero M) : Q M := by
    let N := (DerivedCategory.homologyFunctor B 0).obj
      (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A 0).obj
        ((DerivedCategory.homologyFunctor A 0).obj K)))
    have hN : Q N := (hF _ (hK 0)).2 0 (by omega)
    have hZ : Q (kernel (𝟙 N)) := hker _ hN hN
    exact Q.prop_of_iso ((isZero_kernel_of_mono (𝟙 N)).isoZero ≪≫ hM.isoZero.symm) hZ
  have hR (p : ℕ) (q : ℤ) : Q ((F.rightDerived p).obj (L.obj.homology q)) :=
    Q.prop_of_iso (F.homologyRightDerivedFunctorObjSingleFunctorIso _ p)
      ((hF _ (hL q)).2 p (by omega))
  refine ⟨?_, fun a ha ↦ derived_lower_bound F K a ha, ?_⟩
  · intro q
    exact Q.prop_of_iso ((DerivedCategory.homologyFunctor B q).mapIso
      (F.rightDerivedFunctor.mapIso e))
      (hypercohomology_property F L a hLa Q hzero hker hcoker hext hR q)
  · intro b hb
    have : K.IsLE b := hb
    refine (DerivedCategory.isLE_iff _ (b + c)).mpr fun n hn ↦ ?_
    apply IsZero.of_iso (hypercohomology_zero F L a n hLa ?_)
      ((DerivedCategory.homologyFunctor B n).mapIso (F.rightDerivedFunctor.mapIso e)).symm
    intro p q hpq
    by_cases hp : c < (p : ℤ)
    · exact ((hF _ (hL q)).1 p hp).of_iso
        (F.homologyRightDerivedFunctorObjSingleFunctorIso _ p).symm
    · have hq : b < q := by omega
      exact (F.rightDerived p).map_isZero ((K.isZero_of_isLE b q hq).of_iso (eh q))

/-- Proper direct image with coefficients in a finite subextension of ℚ_ℓ preserves
ind-constructible cohomology of bounded-below complexes and has the stated amplitude.
-/
theorem proper_indConstructible_boundedBelow
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (d : ℤ)
    (hd : ∀ y : Y,
      topologicalKrullDim (pullback p
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
        if 0 ≤ d then (d.toNat : WithBot ℕ∞) else ⊥)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.continuousMapRingObj E) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj K))
    (hbelow : ∃ a₀ : ℤ, K.IsGE a₀) :
    (∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
        K))) ∧
    (∀ a : ℤ, K.IsGE a →
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
        K).IsGE a) ∧
    (∀ b : ℤ, K.IsLE b →
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
        K).IsLE
        (b + 2 * d + 1)) := by
  have hd' : ∀ y : Y, ∀ n : ℕ,
      (n : WithBot ℕ∞) ≤ topologicalKrullDim (pullback p
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d := by
    intro y n hn
    by_cases h : 0 ≤ d
    · have hdim := hd y
      rw [ite_eq_left h] at hdim
      have hn' : (n : WithBot ℕ∞) ≤ (d.toNat : WithBot ℕ∞) := hn.trans hdim
      have hn'' : n ≤ d.toNat := by exact_mod_cast hn'
      omega
    · have hdim := hd y
      rw [ite_eq_right h] at hdim
      have : ¬ ((n : WithBot ℕ∞) ≤ (⊥ : WithBot ℕ∞)) := by simp
      exact (this (hn.trans hdim)).elim
  have hheart := properHeartBound ℓ E k p₀ hp₀ hpℓ X Y p d hd'
  have hkc := (indHeart_kernelsCokernels ℓ p₀ k hp₀ hpℓ Y).1 E
  have hker {M N : pulledBackModuleObjects (Profinite.continuousMapRingObj E) Y} (f : M ⟶ N)
      (hM : ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y) M)
      (hN : ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y) N) :
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y) (kernel f) := by
    obtain ⟨_, _, _, _, _, _, _, hk, _⟩ := hkc M N f hM hN
    exact hk
  have hcoker {M N : pulledBackModuleObjects (Profinite.continuousMapRingObj E) Y} (f : M ⟶ N)
      (hM : ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y) M)
      (hN : ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y) N) :
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y) (cokernel f) := by
    obtain ⟨_, _, _, _, _, _, _, _, hc⟩ := hkc M N f hM hN
    exact hc
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have hresult := derived_from_heart (CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p)
    (ObjectProperty.ind.{u + 1} (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X))
    (ObjectProperty.ind.{u + 1} (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y))
    hker hcoker (indConstructible_of_shortExact ℓ E Y) (2 * d + 1) hheart.1 K hK hbelow
  simpa only [add_assoc] using hresult

/-- Proper direct image with coefficients in the condensed algebraic closure preserves
ind-constructible cohomology of bounded-below complexes and has the stated amplitude.
-/
theorem proper_indConstructible_boundedBelow_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (d : ℤ)
    (hd : ∀ y : Y,
      topologicalKrullDim (pullback p
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
        if 0 ≤ d then (d.toNat : WithBot ℕ∞) else ⊥)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj K))
    (hbelow : ∃ a₀ : ℤ, K.IsGE a₀) :
    (∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
        K))) ∧
    (∀ a : ℤ, K.IsGE a →
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
        K).IsGE a) ∧
    (∀ b : ℤ, K.IsLE b →
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
        K).IsLE
        (b + 2 * d + 1)) := by
  have hd' : ∀ y : Y, ∀ n : ℕ,
      (n : WithBot ℕ∞) ≤ topologicalKrullDim (pullback p
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d := by
    intro y n hn
    by_cases h : 0 ≤ d
    · have hdim := hd y
      rw [ite_eq_left h] at hdim
      have hn' : (n : WithBot ℕ∞) ≤ (d.toNat : WithBot ℕ∞) := hn.trans hdim
      have hn'' : n ≤ d.toNat := by exact_mod_cast hn'
      omega
    · have hdim := hd y
      rw [ite_eq_right h] at hdim
      have : ¬ ((n : WithBot ℕ∞) ≤ (⊥ : WithBot ℕ∞)) := by simp
      exact (this (hn.trans hdim)).elim
  have hheart := properHeartBound_padicAlgCl ℓ k p₀ hp₀ hpℓ X Y p d hd'
  have hkc := (indHeart_kernelsCokernels ℓ p₀ k hp₀ hpℓ Y).2
  have hker {M N : pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) Y} (f : M ⟶ N)
      (hM : ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y) M)
      (hN : ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y) N) :
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y) (kernel f) := by
    obtain ⟨_, _, _, _, _, _, _, hk, _⟩ := hkc M N f hM hN
    exact hk
  have hcoker {M N : pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) Y} (f : M ⟶ N)
      (hM : ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y) M)
      (hN : ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y) N) :
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y) (cokernel f) := by
    obtain ⟨_, _, _, _, _, _, _, _, hc⟩ := hkc M N f hM hN
    exact hc
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have hresult := derived_from_heart (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p)
    (ObjectProperty.ind.{u + 1} (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X))
    (ObjectProperty.ind.{u + 1} (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y))
    hker hcoker (indConstructible_of_shortExact_padicAlgCl ℓ Y) (2 * d + 1) hheart.1 K hK hbelow
  simpa only [add_assoc] using hresult

end AlgebraicGeometry.ProEtale
