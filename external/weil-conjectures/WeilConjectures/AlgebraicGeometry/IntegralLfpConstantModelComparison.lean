/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
public import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
public import WeilConjectures.Topology.ContinuousMapCondensedRing
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import WeilConjectures.AlgebraicGeometry.ContinuousPresentationFiberCompatibility
import WeilConjectures.AlgebraicGeometry.IntegralContinuousCokernelLocalModel
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

/-!
# Integral local finite presentation and constant models

Source: Hemo--Richarz--Scholbach, Example 3.1 and Theorems 4.13, 6.2 and 6.12
(auxiliary; not a blueprint node).

The coefficient ring is the valuation-topology ring of integers in a finite extension of
`Q_l`.  The two predicates in the equivalence are the canonical general local-finite-
presentation and finite-constant-model predicates from the pro-etale framework.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The condensed ring `A̲` with sections `C(S, O_E)`, for the valuation ring `O_E` of the
finite extension `E / Q_l` with its valuation topology. The universe-polymorphic
continuous-map construction is used because the ring of integers has the same universe as
the base scheme. Source: Hemo--Richarz--Scholbach, Example 3.1; item statement, "Give `A` its
valuation topology" [sk-def-sfb-condensed-ring]
(auxiliary; not a blueprint node). -/
noncomputable def integralCondensedRing (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (ℚ_[l]) E]
    [FiniteDimensional (ℚ_[l]) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.continuousMapRingObjOfUniverse
    (latticeCoefficientIntegers l E)

/-- The canonical ring-object structure of `A̲`, from the continuous-map condensed ring.
Source: Hemo--Richarz--Scholbach, Example 3.1 [sk-def-sfb-condensed-ring]
(auxiliary; not a blueprint node). -/
noncomputable instance integralCondensedRingMonObj (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (ℚ_[l]) E]
    [FiniteDimensional (ℚ_[l]) E] :
    MonObj (integralCondensedRing l E) :=
  Profinite.continuousMapRingObjOfUniverseMonObj
    (latticeCoefficientIntegers l E)

/-- The ring object `A̲` is commutative, since `O_E` is commutative.
Source: Hemo--Richarz--Scholbach, Example 3.1 [sk-def-sfb-condensed-ring]
(auxiliary; not a blueprint node). -/
noncomputable instance integralCondensedRingComm (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (ℚ_[l]) E]
    [FiniteDimensional (ℚ_[l]) E] :
    IsCommMonObj (integralCondensedRing l E) :=
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse
    (latticeCoefficientIntegers l E)

/-- The integral coefficient ring `B_X = p_X^* A̲` on the small pro-etale site of `X`.
Source: Hemo--Richarz--Scholbach, Example 3.1; item statement, "put `B_X = p_X^* A̲`"
[sk-def-sfb-pulled-back-coefficients]
(auxiliary; not a blueprint node). -/
noncomputable def integralCoefficientRing (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (ℚ_[l]) E]
    [FiniteDimensional (ℚ_[l]) E] (X : Scheme.{u}) :
    Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  AlgebraicGeometry.ProEtale.coefficientRing X (Mon.mk (integralCondensedRing l E))

/-- The ring-object structure of `B_X`, carried by the bundled pulled-back ring object.
Source: item statement, [sk-def-sfb-pulled-back-coefficients]
(auxiliary; not a blueprint node). -/
noncomputable instance integralCoefficientRingMonObj (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (ℚ_[l]) E]
    [FiniteDimensional (ℚ_[l]) E] (X : Scheme.{u}) :
    MonObj ((integralCoefficientRing l E X).X) :=
  (integralCoefficientRing l E X).mon

private theorem transport_iso_model
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M N : C} {P : D} (e : M ≅ N) (h : Nonempty (F.obj N ≅ P)) :
    Nonempty (F.obj M ≅ P) :=
  ⟨F.mapIso e ≪≫ h.some⟩

private theorem exists_model_transport
    {C D : Type*} [Category C] [Category D] {A : Type*}
    (F : C ⥤ D) (G : A → D) (P : A → Prop)
    {M N : C} (e : M ≅ N)
    (h : ∃ a, P a ∧ Nonempty (F.obj N ≅ G a)) :
    ∃ a, P a ∧ Nonempty (F.obj M ≅ G a) := by
  obtain ⟨a, ha, he⟩ := h
  exact ⟨a, ha, transport_iso_model F e he⟩

private instance point_colimits (X : Scheme.{u}) :
    Limits.PreservesColimitsOfSize.{u + 1, u + 1} (upperStarFromPoint X) :=
  (pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).leftAdjoint_preservesColimits

private instance point_additive (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  have : Limits.PreservesBinaryBiproducts (upperStarFromPoint X) :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private theorem finiteConstantModel_isLocallyFinitelyPresented
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ X M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M := by
  obtain ⟨C, hC⟩ := hM
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC i
  let α := condensedPullbackHom Λ (C.f i)
  have hmodel := finitePresentation_mapMod (upperStarFromPoint (C.X i)) hP
  have hlocal := finitePresentation_of_iso eP.symm hmodel
  have e := (Mod.extendScalarsIsoComapInv α).app
    (((upperStar Ab.{u + 1} (C.f i)).mapMod (condensedRingObj Λ X)).obj M)
  exact finitePresentation_of_comap (inv α) (finitePresentation_of_iso e hlocal)

private theorem constructible_of_finiteConstantStratified
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsFiniteConstantStratified Λ X M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  let α := condensedPullbackHom Λ (S.immersion a)
  apply localFinitePresentation_of_comap (inv α)
  have h := finiteConstantModel_isLocallyFinitelyPresented Λ _ _ (hS a)
  have e := (Mod.extendScalarsIsoComapInv α).app
    (((upperStar Ab.{u + 1} (S.immersion a)).mapMod (condensedRingObj Λ X)).obj M)
  exact localFinitePresentation_of_iso e h

set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteConstantModel_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ X N) :
    HasFiniteConstantLocalModel Λ X M := by
  rcases h with ⟨C, hC⟩
  refine ⟨C, fun i ↦ ?_⟩
  exact exists_model_transport (CondensedRing.upperStar Λ (C.f i))
    (((upperStarFromPoint (C.X i)).mapMod Λ).obj)
    (Mod.IsFinitelyPresented Λ) e (hC i)

@[irreducible] private noncomputable def modelPullbackCompIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (f : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (CondensedRing.upperStar Λ (g ≫ f)).obj M ≅
      (CondensedRing.upperStar Λ g).obj ((CondensedRing.upperStar Λ f).obj M) :=
  (CondensedRing.upperStarComp Λ g f).app M

private theorem exists_cover_of_composite_models {X : Scheme.{u}}
    (P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (D : ∀ i, Scheme.Cover.{u} Scheme.proetalePrecoverage (C.X i))
    (h : ∀ i j, P ((D i).f j ≫ C.f i)) :
    ∃ K : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k, P (K.f k) :=
  ⟨C.bind D, fun ij ↦ h ij.1 ij.2⟩

private theorem exists_cover_of_local_models {X : Scheme.{u}}
    (P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage (C.X i),
      ∀ j, P (D.f j ≫ C.f i)) :
    ∃ K : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k, P (K.f k) := by
  choose D hD using h
  exact exists_cover_of_composite_models P C D hD

private theorem finiteConstantModel_of_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, HasFiniteConstantLocalModel Λ (C.X i)
      ((CondensedRing.upperStar Λ (C.f i)).obj M)) :
    HasFiniteConstantLocalModel Λ X M := by
  apply exists_cover_of_local_models
    (fun {Y} f ↦ ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ P ∧
        Nonempty ((CondensedRing.upperStar Λ f).obj M ≅
          ((upperStarFromPoint Y).mapMod Λ).obj P)) C
  intro i
  obtain ⟨D, hD⟩ := h i
  refine ⟨D, fun j ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hD j
  exact ⟨P, hP, ⟨modelPullbackCompIso Λ (D.f j) (C.f i) M ≪≫ e⟩⟩

attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj
attribute [local instance] Profinite.isCommMonObj_continuousMapRingObjOfUniverse

private theorem lfp_hasFiniteConstantLocalModel
    (T : Type u) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [T2Space T] [TotallyDisconnectedSpace T]
    (hmodel : ∀ {X Y : Scheme.{u}} (p : Y ⟶ X) {m n : ℕ}
      (f : Mod.finiteFree ((upperStar Ab.{u + 1} p).obj
        (ContinuousRingUniverse.baseCoeff T X)) m ⟶
        Mod.finiteFree ((upperStar Ab.{u + 1} p).obj
        (ContinuousRingUniverse.baseCoeff T X)) n),
      IsLocallyConstant (ContinuousRingUniverse.presentationFiberType T p f) →
      HasFiniteConstantLocalModel (ContinuousRingUniverse.baseRing T) Y
        ((Mod.extendScalars (condensedPullbackHom
          (ContinuousRingUniverse.baseRing T) p)).obj (Limits.cokernel f)))
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ContinuousRingUniverse.baseCoeff T X))
    (hM : IsLocallyFinitelyPresented (ContinuousRingUniverse.baseCoeff T X) M) :
    HasFiniteConstantLocalModel (ContinuousRingUniverse.baseRing T) X M := by
  classical
  obtain ⟨C, hC⟩ := hM
  choose n m f e using hC
  let r (i : C.I₀) := ContinuousRingUniverse.presentationFiberType
    T (C.f i) (f i)
  have hcompat (i j : C.I₀) (v : C.X i) (w : C.X j)
      (h : C.f i v = C.f j w) : r i v = r j w :=
    ContinuousRingUniverse.presentationFiberType_eq
      T X M C n m f e i j v w h
  have hspec (i : C.I₀) {v w : C.X i} (h : v ⤳ w) : r i v = r i w :=
    ContinuousRingUniverse.presentationFiberType_specializes
      T (C.f i) (f i) h
  obtain ⟨d, hd, hdc⟩ := exists_locallyConstant_descent_of_specializes C.X C.f
    (fun i ↦ by
      have : WeaklyEtale (C.f i) :=
        Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk i)
      infer_instance)
    (fun x ↦ by
      have hsurj := ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
        (Scheme.propQCPrecoverage_le_precoverage _ C.mem₀)).1
      exact hsurj x)
    r hcompat (fun i _ _ h ↦ hspec i h)
  have hr (i : C.I₀) : IsLocallyConstant (r i) := by
    have he : r i = d ∘ C.f i := funext fun v ↦ (hdc i v).symm
    rw [he]
    exact hd.comp_continuous (C.f i).continuous
  apply finiteConstantModel_of_cover (ContinuousRingUniverse.baseRing T) M C
  intro i
  have hc := hmodel (C.f i) (f i) (hr i)
  exact finiteConstantModel_of_iso (ContinuousRingUniverse.baseRing T)
    ((Mod.extendScalars (condensedPullbackHom (ContinuousRingUniverse.baseRing T) (C.f i))).mapIso
      (e i).some) hc

private theorem integral_lfp_hasFiniteConstantLocalModel
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCondensedRing l E) X))
    (hM : IsLocallyFinitelyPresented (condensedRingObj (integralCondensedRing l E) X) M) :
    HasFiniteConstantLocalModel (integralCondensedRing l E) X M := by
  classical
  let K := WithAbs (Padic.coefficientExtensionAbsoluteValue l E)
  have : IsUltrametricDist K :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (by
      intro x y
      exact isNonarchimedean_spectralNorm (K := ℚ_[l]) (L := E) x.ofAbs y.ofAbs)
  have : TotallyDisconnectedSpace (latticeCoefficientIntegers l E) := inferInstance
  exact lfp_hasFiniteConstantLocalModel (latticeCoefficientIntegers l E)
    (ContinuousRingUniverse.integral_cokernel_hasFiniteConstantLocalModel l E) X M hM

private theorem comparison_of_local_models
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hloc : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) N →
      HasFiniteConstantLocalModel Λ Y N)
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M ↔
      IsConstantModelConstructible Λ X M := by
  classical
  have hqcqs : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  change IsConstructibleModuleObject (condensedRingObj Λ X) M ↔ _
  rw [IsConstantModelConstructible, ite_eq_left hqcqs]
  constructor
  · intro hM
    obtain ⟨S, hS⟩ := hM
    refine ⟨S, fun a ↦ ?_⟩
    have : TopologicalSpace.NoetherianSpace (S.domain a) :=
      (S.immersion a).isEmbedding.isInducing.noetherianSpace
    let α := condensedPullbackHom Λ (S.immersion a)
    have h := localFinitePresentation_comap (inv α) (hS a)
    have e := (Mod.extendScalarsIsoComapInv α).app
      (((upperStar Ab (S.immersion a)).mapMod (condensedRingObj Λ X)).obj M)
    apply hloc (S.domain a)
    exact localFinitePresentation_of_iso e.symm h
  · exact constructible_of_finiteConstantStratified Λ X M

/-- For integral continuous coefficients on a Noetherian scheme, general local finite
presentations are equivalent to finite constant scalar local models.

Source: Hemo--Richarz--Scholbach, Example 3.1, Theorems 4.13, 6.2(2)--(3), Lemma 6.10,
Corollary 6.11(1), and Theorem 6.12(2); compare Bhatt--Scholze Definition 6.8.10 and
Proposition 6.8.11(3).

Proof (node steps):
1. `|X|` is Noetherian (minimal closed subsets), hence so is every stratum `|T|`. Given (i),
   fix a stratum `T` and a pro-etale cover `V_i → T` with presentations
   `B_{V_i}^{m_i} → B_{V_i}^{n_i} → M|_{V_i} → 0`; pullback preserves them (Cartesian
   coefficients), and the cover is flat and jointly surjective.
2. `O_E` is totally disconnected, so `B_{V_i}(U) = C(|U|, O_E)`; the entries of `F_i` are
   continuous. The class `r_i(v)` of `A^{n_i} / F_i(v) A^{m_i}` in the set of isomorphism
   classes of finite scalar cokernels is specialization invariant, as `A` is Hausdorff.
3. Over a common point `x ∈ T`, a common algebraically closed field `Ω` gives
   `Spec Ω → V_i ×_T V_j`; geometric-field evaluation, point coefficients and the
   integral regular-coefficient pullback give `r_i(v) = r_j(w)`.
4. Flat descent of specialization-invariant functions on Noetherian `|T|` makes `r_i`
   locally constant.
5. `O_E` is a DVR; continuous local Smith elimination gives an open cover with
   `L F_i R = D` for a fixed scalar diagonal `D`, so `M` is locally
   `coker D = B ⊗_A P` with `P = coker(D)` finitely presented; this gives (ii).
6. Conversely, a scalar presentation `A^u → A^v → P → 0` gives the presentation
   `B^u → B^v → B ⊗_A P → 0` by the relative-tensor universal property, so (ii) gives (i);
   this direction does not use Noetherianity.
Torsion, zero matrices, empty strata, and rank-zero presentations are included.
(auxiliary; not a blueprint node). -/
theorem integralLfpConstantModelComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (ℚ_[l]) E]
    [FiniteDimensional (ℚ_[l]) E]
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (M : Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientRing l E X).X) :
    IsConstructibleModuleObject
        (integralCoefficientRing l E X).X M ↔
      IsConstantModelConstructible
        (integralCondensedRing l E) X M := by
  let : IsNoetherian X := ⟨⟩
  exact comparison_of_local_models (integralCondensedRing l E)
    (integral_lfp_hasFiniteConstantLocalModel l E) X M

end AlgebraicGeometry.ProEtale
