/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange

import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralIndConstructibleHeartClosure
import all WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartBound
import all WeilConjectures.AlgebraicGeometry.Proper.ProperIndConstructibleBoundedBelow
import all WeilConjectures.AlgebraicGeometry.Proper.ProperIndConstructibleUnbounded
import WeilConjectures.AlgebraicGeometry.Integral.Proper.IntegralProperConstructibleHeartBound
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Compactification.Defs

/-!
# Integral proper cohomological estimates

## References

* Stacks Project, Tags 095U, 099B, 0A0E, 08TB, 08TC and 07KC
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
private theorem bounded_transport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Λ ≅ Λ') [IsMonHom e.hom] (X : Scheme.{u})
    (K : DerivedCategory (pulledBackModuleObjects Λ X))
    (hK : constantModelBoundedConstructible Λ X K) :
    constantModelBoundedConstructible Λ' X
      ((Mod.comap (coefficientMap e.inv X)).mapDerivedCategory.obj K) := by
  let F : pulledBackModuleObjects Λ X ⥤ pulledBackModuleObjects Λ' X :=
      Mod.comap (coefficientMap e.inv X)
  refine ⟨F.bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  have h := (constantModel_comap_iff e.inv X _).2 (hK.2 n)
  exact constructible_iso
    ((F.mapDerivedCategoryHomologyFunctorIso n).app K) h

private theorem bounded_transport_iff
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Λ ≅ Λ') [IsMonHom e.hom] (X : Scheme.{u})
    (K : DerivedCategory (pulledBackModuleObjects Λ X)) :
    constantModelBoundedConstructible Λ' X
      ((Mod.comap (coefficientMap e.inv X)).mapDerivedCategory.obj K) ↔
      constantModelBoundedConstructible Λ X K := by
  constructor
  · intro h
    let F : pulledBackModuleObjects Λ X ⥤ pulledBackModuleObjects Λ' X :=
      Mod.comap (coefficientMap e.inv X)
    refine ⟨F.bounded_of_bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
    apply (constantModel_comap_iff e.inv X _).1
    exact constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K).symm (h.2 n)
  · exact bounded_transport e X K

private theorem proper_integral_constructible
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.padicIntegersRingObj ℓ E) X))
    (hK : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X K) :
    constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Y
      ((CondensedRing.lowerStar (Profinite.padicIntegersRingObj ℓ E) p).rightDerivedFunctor.obj
        K) := by
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.val)).symm.finiteDimensional
  let eR := integerRingSheafIso.{u} ℓ ⟨E.val, E.property⟩
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom e.hom := by dsimp [e]; infer_instance
  have : IsMonHom e.inv := by dsimp [e]; infer_instance
  let T : pulledBackModuleObjects (Profinite.padicIntegersRingObj ℓ E) X ⥤
      pulledBackModuleObjects (DerivedNakayama.integerRing ℓ (ULift.{u} E.val)) X :=
    Mod.comap (coefficientMap e.inv X)
  have h := ((CondensedRing.integralProperDirectImageAndFormulas ℓ (ULift.{u} E.val) k p).1
    (T.mapDerivedCategory.obj K) (bounded_transport e X K hK)).2.2
  apply (bounded_transport_iff e Y _).1
  have (Z : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv Z)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  let i := (CondensedRing.derivedComapLowerStarIso e.inv p).app K
  refine ⟨?_, fun n ↦ ?_⟩
  · exact DerivedCategory.TStructure.t.bounded.prop_of_iso i.symm h.1
  · exact constructible_iso ((DerivedCategory.homologyFunctor _ n).mapIso i.symm) (h.2 n)

private theorem integral_upper_from_heart
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P : ObjectProperty (pulledBackModuleObjects Λ X))
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    (c : ℤ)
    (hheart : ∀ N, P N →
      ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE c)
    (K : DerivedCategory (pulledBackModuleObjects Λ X))
    (hK : ∀ n : ℤ, P ((DerivedCategory.homologyFunctor _ n).obj K))
    (b : ℤ) (hb : K.IsLE b) :
    ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj K).IsLE (b + c) := by
  let S := DerivedCategory.homologyProperty P
  let Q : ObjectProperty (pulledBackModuleObjects Λ Y) := ⊤
  have htrunc (L) (hL : S L) (j : ℤ) :
      S ((DerivedCategory.TStructure.t.truncLE j).obj L) ∧
      S ((DerivedCategory.TStructure.t.truncGE j).obj L) :=
    ⟨DerivedCategory.homologyProperty_truncLE hL j,
      DerivedCategory.homologyProperty_truncGE hL j⟩
  have hbounded (L) (hL : S L) (hlower : ∃ a : ℤ, L.IsGE a) :=
    derived_from_heart (CondensedRing.lowerStar Λ p) P Q
      (fun _ _ _ ↦ trivial) (fun _ _ _ ↦ trivial) (fun _ _ _ _ ↦ trivial) c
      (fun N hN ↦ ⟨(DerivedCategory.isLE_iff _ c).1 (hheart N hN),
        fun _ _ ↦ trivial⟩) L hL hlower
  exact (coefficient_unbounded Λ p S Q htrunc c hbounded K hK).2.2.2 b hb

/-- Cohomological bounds for derived proper pushforward along `p` with fibres of dimension
at most `d`: it preserves (ind-)constructibility on the heart and bounded constructibility,
and has cohomological amplitude at most `2d + 1`. -/
theorem integralProperCohomologicalBounds
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞)) :
    let Λ := Profinite.padicIntegersRingObj ℓ E
    let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
    let B := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)
    let F := (CondensedRing.lowerStar Λ p).rightDerivedFunctor
    (∀ N : A, IsConstantModelConstructible Λ X N →
      constantModelBoundedConstructible Λ Y (F.obj ((DerivedCategory.singleFunctor A 0).obj N)) ∧
      (F.obj ((DerivedCategory.singleFunctor A 0).obj N)).IsLE (2 * (d : ℤ) + 1)) ∧
    (∀ N : A, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) N →
      (∀ q : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
        ((DerivedCategory.homologyFunctor B q).obj
          (F.obj ((DerivedCategory.singleFunctor A 0).obj N)))) ∧
      (F.obj ((DerivedCategory.singleFunctor A 0).obj N)).IsLE (2 * (d : ℤ) + 1)) ∧
    (∀ K : DerivedCategory A, constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ Y (F.obj K)) ∧
    (∀ (K : DerivedCategory A) (b : ℤ),
      (∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor A n).obj K)) →
      K.IsLE b → (F.obj K).IsLE (b + (2 * (d : ℤ) + 1))) := by
  let Λ := Profinite.padicIntegersRingObj ℓ E
  let A := pulledBackModuleObjects Λ X
  let B := pulledBackModuleObjects Λ Y
  let H₁ : ObjectProperty A := IsConstantModelConstructible Λ X
  let H₂ : ObjectProperty B := IsConstantModelConstructible Λ Y
  let P := H₁.ind.{u + 1}
  let F := (CondensedRing.lowerStar Λ p).rightDerivedFunctor
  have : Fact (ringChar k).Prime := ⟨by
    rw [ringChar.eq k p₀]
    exact (CharP.char_is_prime_or_zero k p₀).resolve_right hp₀.ne'⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by rw [ringChar.eq k p₀]; exact hpℓ⟩
  have hgen (K : DerivedCategory A) (hK : constantModelBoundedConstructible Λ X K) :
      constantModelBoundedConstructible Λ Y (F.obj K) :=
    proper_integral_constructible ℓ E k X Y p K hK
  have hC (N : A) (hN : H₁ N) :
      constantModelBoundedConstructible Λ Y (F.obj ((DerivedCategory.singleFunctor A 0).obj N)) :=
    hgen _ (constantModelConstructible_single Λ X N hN)
  have hb := integralProperConstructibleHeartBound ℓ E k p₀ hp₀ hpℓ X Y p d hd
  have hI (N : A) (hN : P N) :
      (∀ q : ℤ, H₂.ind.{u + 1} ((DerivedCategory.homologyFunctor B q).obj
        (F.obj ((DerivedCategory.singleFunctor A 0).obj N)))) ∧
      (F.obj ((DerivedCategory.singleFunctor A 0).obj N)).IsLE (2 * (d : ℤ) + 1) := by
    obtain ⟨I, hI, hfI, pres, hpres⟩ := hN
    have hv (q : ℤ) : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
        (properHeartHigherDirectImage Λ p q) :=
      properHeartHigherDirectImage_preservesFilteredColimits Λ p q
    constructor
    · intro q
      let := hv q
      exact ⟨I, hI, hfI, pres.map (properHeartHigherDirectImage Λ p q),
        fun i ↦ (hC _ (hpres i)).2 q⟩
    · apply (DerivedCategory.isLE_iff _ _).2
      intro q hq
      let := hv q
      exact (pres.map (properHeartHigherDirectImage Λ p q)).isColimit.isZero_pt
        (Functor.isZero _ fun i ↦ (DerivedCategory.isLE_iff _ _).1
          (hb _ (hpres i)) q hq)
  obtain ⟨hzero, hker, hcoker, hext, _⟩ :=
    integralIndConstructibleHeartClosure ℓ E k p₀ hp₀ hpℓ X
  let := hzero
  let := hker
  let := hcoker
  let := hext
  refine ⟨fun N hN ↦ ⟨hC N hN, hb N hN⟩, hI, hgen, ?_⟩
  intro K b hK hbK
  exact integral_upper_from_heart Λ p P (2 * (d : ℤ) + 1)
    (fun N hN ↦ (hI N hN).2) K hK b hbK

end AlgebraicGeometry.ProEtale
