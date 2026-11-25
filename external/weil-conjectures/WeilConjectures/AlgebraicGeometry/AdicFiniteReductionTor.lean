/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import all WeilConjectures.Algebra.Homology.NilpotentCoefficientTensorAcyclic
import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # AdicFiniteReductionTor
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion
open CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme

-- A bounded flat model computes the normalized inverse image in the same interval.
private theorem pullback_tor (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (C : D (constant (smallModelComparisonEtaleTopology.{u, v} X) A))
    (a b : ℤ) (hab : a ≤ b)
    (hC : HasCoefficientModelTorAmplitude _ C a b) :
    HasCoefficientProEtaleTorAmplitude X A ((adicFinitePullback X A).obj C) a b := by
  let R := constant (smallModelComparisonEtaleTopology.{u, v} X) A
  let S := constant (coefficientProEtaleModelTopology.{u, v} X) A
  obtain ⟨P, hge, hle, hf, ⟨eP⟩⟩ :=
    (coefficientModelTorAmplitude_iff_flatModel R C a b hab).mp hC
  let F := adicFiniteOrdinaryPullback.{u, v} X A
  let T : Cx S := (F.mapHomologicalComplex (.up ℤ)).obj P
  have hp : P.IsKFlatTensor :=
    CochainComplex.isKFlat_of_boundedAbove_flat P
      ⟨b, fun i hi ↦ P.isZero_of_isStrictlyLE b i hi⟩ hf
  have hflat := (pull_flat_kFlat (adicFiniteComparisonData.{u, v} X)
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
    (constantMap (adicFiniteComparisonData.{u, v} X) A) P hp hf).2
  have htge : T.IsStrictlyGE a := (T.isStrictlyGE_iff a).mpr
    (fun i hi ↦ F.map_isZero (P.isZero_of_isStrictlyGE a i hi))
  have htle : T.IsStrictlyLE b := (T.isStrictlyLE_iff b).mpr
    (fun i hi ↦ F.map_isZero (P.isZero_of_isStrictlyLE b i hi))
  have hc : IsIso ((adicFinitePullbackComparison X A).app P) :=
    (adicFinitePullbackData X A).computation P hp hf
  apply (coefficientModelTorAmplitude_iff_flatModel S _ a b hab).mpr
  exact ⟨T, htge, htle, hflat,
    ⟨(asIso ((adicFinitePullbackComparison X A).app P)).symm ≪≫
      (adicFinitePullback X A).mapIso eP⟩⟩

-- Balanced scalar extension identifies the two ordinary single-module tensor tests.
private theorem tensorTest_change {D₀ : Type v} [SmallCategory D₀]
    {T₀ : GrothendieckTopology D₀} {R S : Sheaf T₀ CommRingCat.{v}}
    (f : R ⟶ S) (P : Cx R) (M : Mod S) (q : ℤ) :
    IsZero (coefficientModelTensorTest R P ((res f).obj M) q) ↔
      IsZero (coefficientModelTensorTest S
        (((change f).mapHomologicalComplex (.up ℤ)).obj P) M q) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.symmetricCategory R
  let E := change f
  let U := res f
  let EP : Cx S := (E.mapHomologicalComplex (.up ℤ)).obj P
  have hu := SheafOfModules.restrictScalars_exact_kflat
    ((sheafCompose T₀ (forget₂ CommRingCat RingCat)).map f)
  have : PreservesFiniteLimits U := hu.1
  have : PreservesFiniteColimits U := hu.2
  obtain ⟨e, he⟩ :=
    SheafOfModules.exists_changeOfRings_tensorCancellation_independentCoefficients f
  let c : E ⋙ tensorLeft M ⋙ U ≅ tensorLeft (U.obj M) :=
    NatIso.ofComponents (e M) (by
      intro X Y g
      have hh := he (𝟙 M) g
      change U.map ((𝟙 M) ⊗ₘ E.map g) ≫ (e M Y).hom =
        (e M X).hom ≫ (U.map (𝟙 M) ⊗ₘ g) at hh
      rw [U.map_id, id_tensorHom, id_tensorHom] at hh
      exact hh)
  let W : Cx S := ((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj EP
  let cP : (U.mapHomologicalComplex (.up ℤ)).obj W ≅
      ((tensorRight (U.obj M)).mapHomologicalComplex (.up ℤ)).obj P :=
    (Functor.mapHomologicalComplexCompIso c (.up ℤ)).app P ≪≫
      (NatIso.mapHomologicalComplex
        (BraidedCategory.tensorLeftIsoTensorRight (U.obj M)) (.up ℤ)).app P
  let eR := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) (U.obj M) P
  let eS := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) M EP ≪≫
    (NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight M).symm (.up ℤ)).app EP
  have hz : IsZero (((U.mapHomologicalComplex (.up ℤ)).obj W).homology q) ↔
      IsZero (W.homology q) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology,
      ← HomologicalComplex.exactAt_iff_isZero_homology]
    constructor
    · intro h
      apply ((W.sc q).exact_map_iff_of_faithful (SheafOfModules.toSheaf _)).mp
      exact h.map (SheafOfModules.toSheaf _)
    · exact fun h ↦ h.map U
  exact ((HomologicalComplex.homologyFunctor _ _ q).mapIso
    (eR ≪≫ cP.symm)).isZero_iff.trans
      (hz.trans ((HomologicalComplex.homologyFunctor _ _ q).mapIso eS).isZero_iff.symm)

-- Stacks 0942 (2): propagate one homology vanishing through the finite ideal filtration.
private theorem tensorTest_devissage {D₀ : Type v} [SmallCategory D₀]
    {T₀ : GrothendieckTopology D₀} {R S : Sheaf T₀ CommRingCat.{v}}
    (f : R ⟶ S) (r : ℕ)
    (b : Fin r → (R.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (hq : ∀ U : D₀, Function.Surjective (f.hom.app (op U)))
    (hker : ∀ U : D₀, RingHom.ker (f.hom.app (op U)).hom =
      Ideal.span (Set.range (fun i ↦ (b i).val (op U))))
    (P : Cx R) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) (q : ℤ)
    (hbase : ∀ M : Mod S, IsZero (coefficientModelTensorTest R P ((res f).obj M) q))
    (N : Mod R) (m : ℕ)
    (hN : ∀ U : D₀ᵒᵖ, ∀ a ∈
      (Ideal.span (Set.range (fun j : Fin r ↦ (b j).val U))) ^ m,
      ∀ x : N.val.obj U, a • x = 0) :
    IsZero (coefficientModelTensorTest R P N q) := by
  let A := Mod R
  let G := RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)
  let : CommRing G := (RingCat.sectionsSubring
    (R.obj ⋙ forget₂ CommRingCat RingCat)).toCommRing
  let : Linear G A := SheafOfModules.homLinear R.obj _
  let v : Fin r → G := b
  let := HasDerivedCategory.standard A
  have hPf (i : ℤ) : SheafOfModules.IsFlatOnSite (J := T₀) (R := R) (P.X i) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X i)).symm (hf i)
  obtain ⟨s, hs⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
  let := s
  obtain ⟨_, _, htri, ⟨c, _, _⟩, _⟩ := hs P hp hPf
  let F := (SheafOfModules.KFlatFixedTensor.derivedTensor R).obj (DerivedCategory.Q.obj P)
  let : F.CommShift ℤ := s.commShiftObj _
  have : F.IsTriangulated := htri.1
  let H := DerivedCategory.homologyFunctor A q
  have he (M : A) : coefficientModelTensorTest R P M q ≅
      H.obj (F.obj ((DerivedCategory.singleFunctor A 0).obj M)) :=
    ((DerivedCategory.homologyFunctorFactors A q).app _).symm ≪≫ H.mapIso (c.app _)
  have key : ∀ (e : ℕ) (M : A),
      (∀ a ∈ Ideal.span (Set.range v) ^ e, a • 𝟙 M = 0) →
      IsZero (H.obj (F.obj ((DerivedCategory.singleFunctor A 0).obj M))) := by
    intro e
    induction e with
    | zero =>
      intro M hM
      have hz : IsZero M := (IsZero.iff_id_eq_zero M).2 (by
        simpa only [one_smul] using hM 1 (by simp))
      exact H.map_isZero (F.map_isZero ((DerivedCategory.singleFunctor A 0).map_isZero hz))
    | succ e ih =>
      intro M hM
      obtain ⟨D, hD, rfl, h₁, h₃⟩ :=
        exists_shortExact_of_smul_eq_zero_of_mem_pow_succ v hM
      have hann : ∀ U : D₀ᵒᵖ, ∀ a ∈ RingHom.ker (f.hom.app U).hom,
          ∀ x : D.X₃.val.obj U, a • x = 0 := by
        intro U a ha
        rw [hker U.unop] at ha
        have hg (j : Fin r) (x : D.X₃.val.obj U) : (b j).val U • x = 0 := by
          have hh := h₃ (v j) (Ideal.subset_span ⟨j, rfl⟩)
          exact congrArg (fun f : D.X₃ ⟶ D.X₃ ↦ f.val.app U x) hh
        induction ha using Submodule.span_induction with
        | mem a ha => obtain ⟨j, rfl⟩ := ha; exact hg j
        | zero => intro x; exact zero_smul _ _
        | add a z ha hz iha ihz => intro x; rw [add_smul, iha, ihz, add_zero]
        | smul a z hz ihz => intro x; rw [smul_eq_mul, mul_smul, ihz, smul_zero]
      obtain ⟨M₃, ⟨e₃⟩⟩ :=
        CategoryTheory.NilpotentCoefficientProof.exists_quotient_module f hq D.X₃ hann
      have hz₃ := ((hbase M₃).of_iso (he _).symm).of_iso
        (H.mapIso (F.mapIso ((DerivedCategory.singleFunctor A 0).mapIso e₃))).symm
      have hT := F.map_distinguished _ hD.singleTriangle_distinguished
      exact (DerivedCategory.HomologySequence.exact₂ _ hT q).isZero_X₂
        ((ih _ h₁).eq_of_src _ _) (hz₃.eq_of_tgt _ _)
  have hglob : ∀ a ∈ Ideal.span (Set.range v) ^ m, a • 𝟙 N = 0 := by
    intro a ha
    ext U x
    change a.val U • x = 0
    let ev : G →+* R.obj.obj U := (Pi.evalRingHom _ U).comp
      (RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)).subtype
    have hle : Ideal.map ev (Ideal.span (Set.range v)) ≤
        Ideal.span (Set.range (fun j : Fin r ↦ (b j).val U)) := by
      rw [Ideal.map_span]
      apply Ideal.span_mono
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    have hm := Ideal.mem_map_of_mem ev ha
    rw [Ideal.map_pow] at hm
    exact hN U _ ((pow_le_pow_left' hle m) hm) x
  exact (key m N hglob).of_iso (he N)

/-- The residue Tor interval controls every positive-power reduction.
Source: Stacks Project, proetale.tex, Tag 09C2 (2), and sites-cohomology.tex,
lemma-bounded; finite-Tor comparison over discrete Noetherian coefficients.
(auxiliary; not a blueprint node).

Proof: The finite-Tor comparison transfers the given interval from C to its
comparison pullback, hence through e to the residue reduction. Resolve N by one
K-flat complex P with flat terms. Its scalar extensions represent all reductions
and remain K-flat with flat terms. For an A/J^(n+1)-module sheaf F, filter F by
J^i F for 0 <= i <= n+1. Each successive quotient G is annihilated by J.
Balancing identifies the tensor of the nth reduction with G with the tensor of
the residue reduction with G. The residue Tor bound gives vanishing outside
[a,b]. Tensoring the short exact filtration sequences with P is degreewise
exact because its terms are flat. Their long exact homology sequences and
induction from the zero last term give the bound for F. Changing K-flat
representatives preserves the tests, giving the stated universal predicate.
For n=0 this is just comparison; J=0 gives a constant filtration and J=A gives
the zero quotient category. No completeness of N is needed. -/
theorem adicFiniteReduction_tor
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A)
    (C : adicFiniteEtale.{u, v} X J 0)
    (hC : IsCoefficientBoundedConstructibleEtale.{u, v} X (adicFiniteCoeff J 0) C)
    (e : (adicFinitePullback.{u, v} X (adicFiniteCoeff J 0)).obj C ≅
      adicFiniteReduction.{u, v} X J N 0)
    (a b : ℤ) (hab : a ≤ b)
    (hTor : HasCoefficientModelTorAmplitude
      (constant (smallModelComparisonEtaleTopology.{u, v} X) (adicFiniteCoeff J 0)) C a b) :
    ∀ n : ℕ, HasCoefficientProEtaleTorAmplitude.{u, v} X (adicFiniteCoeff J n)
      (adicFiniteReduction.{u, v} X J N n) a b := by
  have _hConstructible := hC
  let T₀ := coefficientProEtaleModelTopology.{u, v} X
  let R := constant T₀ A
  let f (n : ℕ) := adicFiniteConstantMap (adicFiniteQuotient J n) T₀
  have hzero : HasCoefficientModelTorAmplitude _ (adicFiniteReduction X J N 0) a b := by
    have h := pullback_tor X (adicFiniteCoeff J 0) C a b hab hTor
    exact ⟨hab, fun P hp ⟨eP⟩ ↦ h.2 P hp ⟨eP ≪≫ e.symm⟩⟩
  obtain ⟨P, hp, hf, ⟨eP⟩⟩ := exists_coefficientModelFlatKFlatRepresentative R N
  have hp' : P.IsKFlatTensor :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hp
  let Pn (n : ℕ) : Cx (constant T₀ (adicFiniteCoeff J n)) :=
    ((change (f n)).mapHomologicalComplex (.up ℤ)).obj P
  have hpn (n : ℕ) : (Pn n).IsKFlatIndependentCoefficients :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat (Pn n)).mpr
      (change_flat_kFlat (f n) P hp' hf).1
  have en (n : ℕ) : (Q (constant T₀ (adicFiniteCoeff J n))).obj (Pn n) ≅
      adicFiniteReduction X J N n := by
    have hc : IsIso ((extendComparison (f n)).app P) :=
      (derivedExtension (f n)).computation P hp'
    exact (asIso ((extendComparison (f n)).app P)).symm ≪≫ (extend (f n)).mapIso eP
  obtain ⟨r, gs, hgs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    J.fg_of_isNoetherianRing
  let bs (i : Fin r) := constantSection (J := T₀) (gs i)
  have hquot (n : ℕ) (U : (coefficientProEtaleSiteModel.{u, v} X)) :
      Function.Surjective ((f n).hom.app (op U)) ∧
      RingHom.ker ((f n).hom.app (op U)).hom =
        Ideal.span (Set.range (fun z : ↥(J ^ (n + 1)) ↦
          (constantSection (J := T₀) (z : A)).val (op U))) :=
    (flat_and_quotients T₀ A J).2.2 n U
  have hk (U : (coefficientProEtaleSiteModel.{u, v} X)) :
      RingHom.ker ((f 0).hom.app (op U)).hom =
        Ideal.span (Set.range (fun i ↦ (bs i).val (op U))) := by
    rw [(hquot 0 U).2]
    let ev : A →+* R.obj.obj (op U) :=
      ((toSheafify T₀ ((Functor.const _).obj (CommRingCat.of A))).app (op U)).hom
    exact span_subtype_images ev (J ^ (0 + 1)) gs (by simpa using hgs)
  intro n
  refine ⟨hab, ?_⟩
  intro P' hp₁ ⟨eP'⟩ M q hq
  have hbase (M₀ : Mod (constant T₀ (adicFiniteCoeff J 0))) :
      IsZero (coefficientModelTensorTest R P ((res (f 0)).obj M₀) q) :=
    (tensorTest_change (f 0) P M₀ q).mpr (hzero.2 (Pn 0) (hpn 0) ⟨en 0⟩ M₀ q hq)
  have hann : ∀ U, ∀ z ∈
      (Ideal.span (Set.range (fun i : Fin r ↦ (bs i).val U))) ^ (n + 1),
      ∀ x : ((res (f n)).obj M).val.obj U, z • x = 0 := by
    intro U z hz x
    let ev : A →+* R.obj.obj U :=
      ((toSheafify T₀ ((Functor.const _).obj (CommRingCat.of A))).app U).hom
    have hspan : Ideal.span (Set.range (fun i : Fin r ↦ (bs i).val U)) =
        Ideal.map ev J := by
      rw [← hgs, Ideal.map_span]
      congr 1
      ext z
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨gs i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    have hle : Ideal.map ev (J ^ (n + 1)) ≤ RingHom.ker ((f n).hom.app U).hom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro t ht
      change ev t ∈ RingHom.ker ((f n).hom.app U).hom
      rw [(hquot n U.unop).2]
      exact Ideal.subset_span ⟨⟨t, ht⟩, rfl⟩
    have hmem : z ∈ RingHom.ker ((f n).hom.app U).hom := by
      rw [hspan, ← Ideal.map_pow] at hz
      exact hle hz
    change (f n).hom.app U z • (show M.val.obj U from x) = 0
    rw [show (f n).hom.app U z = 0 from hmem, zero_smul]
  have hz := tensorTest_devissage (f 0) r bs (fun U ↦ (hquot 0 U).1) hk
    P hp hf q hbase ((res (f n)).obj M) (n + 1) hann
  have hz' := (tensorTest_change (f n) P M q).mp hz
  obtain ⟨et⟩ := coefficientModelTensorTest_iso _ P' (Pn n) hp₁ (hpn n)
    (eP' ≪≫ (en n).symm) M q
  exact hz'.of_iso et

end AlgebraicGeometry.Scheme
