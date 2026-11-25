/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.CoherentSupportProperHigherDirectImage
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.ProperSupportHigherDirectImageBound
import Mathlib.Data.Int.Interval
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import all WeilConjectures.CategoryTheory.HalfPlaneWeakConvergence
import all WeilConjectures.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh

/-! # Proper-support direct image preserves bounded coherent complexes

Source: literature/stacks-project/perfect.tex, Derived Categories of Schemes,
Lemma 36.11.3 (Tag 08E2; label lemma-direct-image-coherent)
(blueprint: lem-pc-direct-image-bounded-coherent).
-/

@[expose] public section

universe u wX wS

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Coherence passes to the kernel modulo the incoming differential on every page. -/
private theorem coherent_pages {S : Scheme.{u}}
    (X : BigradedExactCouple (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0)
    (hX : ∀ p q : ℤ, RingedSpace.IsCoherent S.toRingedSpace (X.E p q)) :
    ∀ (r : ℕ) (p q : ℤ), RingedSpace.IsCoherent S.toRingedSpace (X.page r p q) := by
  have hk := (RingedSpace.coherent_kernel_cokernel_sum S.toRingedSpace).1
  suffices h : ∀ (r : ℕ) (p q : ℤ),
      RingedSpace.IsCoherent S.toRingedSpace ((X.pageCouple r).E p q) by
    intro r p q
    exact h (r - 2) p q
  intro r
  induction r with
  | zero => exact hX
  | succ r ih =>
    intro p q
    exact (hk _ _
      (kernel.lift ((X.pageCouple r).d p q) ((X.pageCouple r).dInto p q)
        ((X.pageCouple r).dInto_comp_d p q)) (ih _ _)
      ((hk _ _ ((X.pageCouple r).d p q) (ih _ _) (ih _ _)).1)).2

/-- If `S` is Noetherian and `f : X ⟶ S` is locally of finite type, then the derived
 direct image of a bounded complex with coherent cohomology and proper support has
 bounded coherent cohomology. Source: Stacks Project, Tag 08E2, Lemma 36.11.3
 (blueprint: lem-pc-direct-image-bounded-coherent).

Proof:
1. Represent `E` by a bounded complex and apply `lemma-uniform-bound-proper-direct-image--1` to the
   left exact module direct-image functor. This gives the convergent spectral sequence
   `Rᵖf_* Hᑫ(E) ⇒ Hᵖ⁺ᑫ(Rf_*E)` and finite filtrations on its abutment.
2. By `lem-pc-coherent-support-proper-higher-direct-image`, each term of its
   second page is coherent, since each source cohomology sheaf has proper support.
3. The filtration pieces are subquotients of these terms; coherence on the locally
   Noetherian target is closed under subquotients and finite extensions. Thus every
   cohomology sheaf of the direct image is coherent.
4. The lower bound follows from the vanishing quadrant of
`lemma-uniform-bound-proper-direct-image--1`.
5. For each cohomology module of the bounded-below representative, apply
   `lem-pc-proper-support-module-higher-direct-image-bound`. Take the maximum of
   N(q) + max(q,0) over the finite interval [a,b]. Above this maximum every E2 term
   vanishes: outside [a,b] its coefficient is zero, and inside [a,b] its first index
   exceeds N(q). Each later page is a subquotient of the corresponding E2 term, so
   all graded pieces of the finite abutment filtration vanish. The abutment is zero. -/
theorem directImage_isBounded_coherent
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ,
      i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hcoherent : ∀ i : ℤ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hsupport : ∀ i : ℤ,
      Scheme.Modules.HasSupportProperOver f
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)) :
    (∃ a b : ℤ, ∀ i : ℤ,
      i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i).obj
          ((schemeDerivedDirectImage f).obj E))) ∧
    (∀ i : ℤ,
      RingedSpace.IsCoherent S.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i).obj
          ((schemeDerivedDirectImage f).obj E))) := by
  classical
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let P : ObjectProperty B := RingedSpace.IsCoherent S.toRingedSpace
  let : Zero B := HasZeroObject.zero' B
  have hclosure := RingedSpace.coherent_kernel_cokernel_sum S.toRingedSpace
  have : P.ContainsZero := ⟨⟨(0 : SheafOfModules.{u} (moduleRings S.toRingedSpace)),
    isZero_zero _, hclosure.2.2.2.1⟩⟩
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ hclosure.2.2.2.2 _ _ e h⟩
  obtain ⟨a, b, hab⟩ := hbounded
  have : E.IsGE a := (DerivedCategory.isGE_iff E a).2
    (fun i hi ↦ hab i (Or.inl hi))
  have : Limits.PreservesFiniteLimits F := by
    change Limits.PreservesFiniteLimits (Scheme.Modules.pushforward f)
    infer_instance
  have : IsGrothendieckAbelian.{u} X.Modules := Scheme.Modules.isGrothendieckAbelian X
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE E a
  let Kplus : CochainComplex.Plus A := ⟨K, a, hK⟩
  have ha : ∀ q : ℤ, q < a → Limits.IsZero (Kplus.obj.homology q) := by
    intro q hq
    exact (K.exactAt_of_isGE a q hq).isZero_homology
  obtain ⟨T, _, _, _, _, _, hsecond, hneg, _, _, _, _, _, _, _, _, _, hconv⟩ :=
    exists_truncationHypercohomology F Kplus a ha
  let eH (q : ℤ) := (DerivedCategory.homologyFunctor A q).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors A q).app K
  have hKcoh (q : ℤ) : RingedSpace.IsCoherent X.toRingedSpace (Kplus.obj.homology q) :=
    (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).2.2.2.2
      _ _ (eH q) (hcoherent q)
  have hKsupport (q : ℤ) : Scheme.Modules.HasSupportProperOver f (Kplus.obj.homology q) := by
    obtain ⟨Z, hZ, hproper⟩ := hsupport q
    refine ⟨Z, hZ.trans ?_, hproper⟩
    ext x
    let G := SheafOfModules.toSheaf.{u} (moduleRings X.toRingedSpace) ⋙
      TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    exact not_congr (G.mapIso (eH q)).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr
  have hsecondCoh : ∀ p q : ℤ, P (T.E p q) := by
    intro p q
    by_cases hp : p < 0
    · exact P.prop_of_isZero (hneg p q hp)
    · obtain ⟨_, _, eK, _⟩ := hsecond p.toNat q
      have hRq : P ((F.rightDerived p.toNat).obj (Kplus.obj.homology q)) := by
        have h := isCoherent_schemeModuleHigherDirectImage_of_support_proper
          f (Kplus.obj.homology q) (hKcoh q) (hKsupport q) (p.toNat : ℤ) (by omega)
        exact P.prop_of_iso
          (F.homologyRightDerivedFunctorObjSingleFunctorIso (Kplus.obj.homology q) p.toNat) h
      have hEq : P (T.E (p.toNat : ℤ) q) := P.prop_of_iso eK.symm hRq
      simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ p)] using hEq
  have hpages := coherent_pages T hsecondCoh
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
      ((schemeDerivedDirectImage f).obj E)) := by
    intro n
    have hQ : P ((DerivedCategory.homologyFunctor B n).obj
        (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K))) := by
      simpa only [hH] using hHCoh n
    exact P.prop_of_iso
      ((DerivedCategory.homologyFunctor B n).mapIso
        ((schemeDerivedDirectImage f).mapIso e)).symm hQ
  have hbelow : ∀ n : ℤ, n < a → IsZero ((DerivedCategory.homologyFunctor B n).obj
      ((schemeDerivedDirectImage f).obj E)) := by
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
  choose N hN using fun q : ℤ ↦
    Scheme.moduleHigherDirectImage_eventually_isZero f (Kplus.obj.homology q)
      (hKcoh q) (hKsupport q)
  let c : ℕ := (Finset.Icc a b).sup (fun q ↦ N q + q.toNat)
  have hEabove (p q : ℤ) (hn : (c : ℤ) < p + q) : IsZero (T.E p q) := by
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
      have hz : IsZero (T.E (p.toNat : ℤ) q) := hRq.of_iso eK
      simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ p)] using hz
  have habove : ∃ c : ℤ, ∀ n : ℤ, c < n →
      IsZero ((DerivedCategory.homologyFunctor B n).obj
        ((schemeDerivedDirectImage f).obj E)) := by
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
          have hz : IsZero (T.page (max (p + 3) (n - p - a + 2)).toNat p (n - p)) :=
            BigradedExactCouple.page_zero T p (n - p) (hEabove p (n - p) (by omega))
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
