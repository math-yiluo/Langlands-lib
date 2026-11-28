import Langlands.Representation.CuspidalSupport.SupercuspidalInductionLengthStatement
import Langlands.Representation.CuspidalSupport.RationalSummandInductionMembership
import Langlands.Representation.CuspidalSupport.BernsteinCuspFunctorProperties
import Langlands.Representation.CuspidalSupport.BernsteinInducedProgeneratorReduction
import Langlands.Representation.CuspidalSupport.InducedProgeneratorEndBasis
import Langlands.Representation.CuspidalSupport.InducedProgeneratorEndFreeReduction
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.CuspidalSupport.RestrictionConstituentExistence
import Langlands.Representation.Exponents.LeviJacquetInductionSupercuspidalFiltrationProof
import Langlands.Representation.Exponents.LeviJacquetNonSupercuspidalReduction
import Langlands.Representation.Exponents.LeviParabolicFunctorsExactProof
import Langlands.Representation.Exponents.LeviSupercuspidalInductionDetection
import Langlands.Representation.Exponents.MaximalLeviSupercuspidalLengthTwoReduction
import Langlands.BruhatTits.SpecialCompact.JointBasisProof
import Langlands.Representation.Aubert.General.RationalRootAssociationCuspidalityTransport
import Langlands.Representation.Category.CoproductSize
import Langlands.Representation.Category.ExactFunctor
import Langlands.Representation.Filtration.ActualGradedExtraction
import Langlands.Representation.Filtration.ExactFamilyLengthProof
import Mathlib.CategoryTheory.Abelian.Projective.Basic

/-! # The supercuspidal induction length bound via the Jacquet module -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.CuspidalSupport

universe uG uV uR uW

section Length

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {R : Type uR} [Ring R]
  (F : SmoothRep.{0, uG, uV} ℂ G ⥤ ModuleCat.{uW} R)
  [F.Additive] [F.PreservesHomology]

open ExactFamilyLength (inclusion inclusion_injective inclusion_range quotient_nontrivial)
open JacquetDetectingFamilyLengthProof (lower)

private theorem moduleLength_add_of_shortExact {S : ShortComplex (ModuleCat.{uW} R)}
    (hS : S.ShortExact) :
    Module.length R S.X₂ = Module.length R S.X₁ + Module.length R S.X₃ :=
  Module.length_eq_add_of_exact S.f.hom S.g.hom hS.moduleCat_injective_f
    hS.moduleCat_surjective_g (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _ |>.mp hS.exact)

private theorem shortExact_of_intertwiners
    {A B C : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) (g : B ⟶ C)
    (h : SmoothRep.IsShortExact (SmoothRep.hom f) (SmoothRep.hom g)) :
    ∃ w : f ≫ g = 0, (ShortComplex.mk f g w).ShortExact := by
  have w : f ≫ g = 0 := by
    ext x
    change SmoothRep.hom g (SmoothRep.hom f x) = 0
    apply LinearMap.mem_ker.mp
    rw [← h.2.2]
    exact LinearMap.mem_range_self _ _
  exact ⟨w, (smoothShortComplex_shortExact_iff _).mpr h⟩

/-- An exact functor to modules that detects the irreducible subquotients of `A`
bounds the length of `A` by the length of its image. -/
theorem repLength_le_of_exactModuleFunctor (A : SmoothRep.{0, uG, uV} ℂ G)
    (hdetect : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → SmoothRep.IsSubquotient D A → Nontrivial (F.obj D)) :
    repLength A.representation ≤ Module.length R (F.obj A) := by
  have := F.preservesFiniteLimits_of_preservesHomology
  have := F.preservesFiniteColimits_of_preservesHomology
  let image (S : Subrepresentation A.representation) : Submodule R (F.obj A) :=
    LinearMap.range (F.map (A.subtype S)).hom
  have hcomp (S T : Subrepresentation A.representation) (hST : S ≤ T) :
      inclusion A S T hST ≫ A.subtype T = A.subtype S := by
    ext x
    rfl
  have hstrict : StrictMono image := by
    intro S T hST
    let f := inclusion A S T hST.le
    let Q := A.subquotient T (lower A S T)
    let g : A.subrepresentation T ⟶ Q := SmoothRep.mkQ _ _
    obtain ⟨w, hw⟩ := shortExact_of_intertwiners f g
      ⟨inclusion_injective A S T hST.le, SmoothRep.mkQ_surjective _ _,
        inclusion_range A S T hST.le⟩
    have hQ : Nontrivial (F.obj Q) := by
      have : Nontrivial Q := quotient_nontrivial A hST
      obtain ⟨D, hD, hDQ⟩ := SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial Q
      have hQA : SmoothRep.IsSubquotient Q A := ⟨T, lower A S T, ⟨Iso.refl _⟩⟩
      have hDA := smoothSubquotientTransitivity ℂ G A Q D hDQ hQA
      obtain ⟨B, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDQ
      have : Mono i := (SmoothRep.mono_iff_injective i).mpr hi
      have : Epi q := (SmoothRep.epi_iff_surjective q).mpr hq
      have := hdetect D hD hDA
      have : Nontrivial (F.obj B) := (ModuleCat.epi_iff_surjective (F.map q)).mp
        inferInstance |>.nontrivial
      exact ((ModuleCat.mono_iff_injective (F.map i)).mp inferInstance).nontrivial
    have hmap : F.map f ≫ F.map (A.subtype T) = F.map (A.subtype S) := by
      rw [← F.map_comp, hcomp]
    refine lt_of_le_of_ne (fun _ ⟨x, hx⟩ => ⟨F.map f x, ?_⟩) ?_
    · rwa [← ModuleCat.comp_apply, hmap]
    · intro heq
      obtain ⟨q, hq⟩ := @exists_ne _ hQ 0
      have hx := hw.map_of_exact F
      obtain ⟨x, rfl⟩ := hx.moduleCat_surjective_g q
      have hxmem : F.map (A.subtype T) x ∈ image S :=
        heq.symm ▸ LinearMap.mem_range_self (F.map (A.subtype T)).hom x
      obtain ⟨y, hy⟩ := hxmem
      have : Mono (A.subtype T) := (SmoothRep.mono_iff_injective _).mpr (A.subtype_injective T)
      have he : F.map f y = x := (ModuleCat.mono_iff_injective (F.map (A.subtype T))).mp
        inferInstance (by rwa [← ModuleCat.comp_apply, hmap])
      apply hq
      change F.map g x = 0
      rw [← he, ← ModuleCat.comp_apply, ← F.map_comp, w, F.map_zero]
      rfl
  rw [repLength, ← WithBot.coe_le_coe, Module.coe_length, Module.coe_length, Order.krullDim]
  refine sSup_le ?_
  rintro _ ⟨p, rfl⟩
  let o := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := A.representation)
  let q : LTSeries (Submodule R (F.obj A)) :=
    ⟨p.length, fun j => image (o.symm (p j)), fun i => hstrict (o.symm.strictMono (p.step i))⟩
  exact Order.LTSeries.length_le_krullDim q

/-- The length after applying an exact module-valued functor is the sum of the
lengths of the images of the finite filtration's actual smooth graded objects. -/
theorem moduleLength_obj_eq_sum_of_filtration {A : SmoothRep.{0, uG, uV} ℂ G} {n : ℕ}
    (s : ObjectRepFiltration A.obj n) :
    Module.length R (F.obj A) = ∑ i : Fin n, Module.length R (F.obj (s.smoothGradedObject i)) := by
  have := F.preservesFiniteLimits_of_preservesHomology
  have := F.preservesFiniteColimits_of_preservesHomology
  let len (j : Fin (n + 1)) := Module.length R (F.obj (A.subrepresentation (s.subrepresentation j)))
  have hstep (i : Fin n) :
      len i.succ = len i.castSucc + Module.length R (F.obj (s.smoothGradedObject i)) := by
    let X := s.subrepresentation i.castSucc
    let Y := s.subrepresentation i.succ
    have hXY : X ≤ Y := s.monotone_subrepresentation (Fin.castSucc_le_succ i)
    let f := inclusion A X Y hXY
    let g : A.subrepresentation Y ⟶ s.smoothGradedObject i := SmoothRep.ofHom (s.gradedProjection i).hom
    have hex : LinearMap.range (SmoothRep.hom f).toLinearMap =
        LinearMap.ker (SmoothRep.hom g).toLinearMap := by
      ext x
      change Y.toSubmodule at x
      change (∃ y : X.toSubmodule, Submodule.inclusion hXY y = x) ↔ (s.gradedProjection i).hom x = 0
      have hzero := s.gradedProjection_eq_zero_iff i x
      exact ⟨fun ⟨y, hy⟩ => hzero.mpr (hy ▸ y.property),
        fun h => ⟨⟨x.val, hzero.mp h⟩, rfl⟩⟩
    obtain ⟨w, hw⟩ := shortExact_of_intertwiners f g
      ⟨inclusion_injective A X Y hXY, s.gradedProjection_surjective i, hex⟩
    exact moduleLength_add_of_shortExact (hw.map_of_exact F)
  have hzero : len 0 = 0 := by
    dsimp only [len]
    rw [s.subrepresentation_zero, Module.length_eq_zero_iff, ← ModuleCat.isZero_iff_subsingleton]
    apply F.map_isZero
    apply (SmoothRep.isZero_iff_subsingleton _).mpr
    exact ⟨fun a b => Subtype.ext (a.property.trans b.property.symm)⟩
  have htop : len (Fin.last n) = Module.length R (F.obj A) := by
    dsimp only [len]
    rw [s.subrepresentation_last]
    let e : A.subrepresentation ⊤ ≅ A := SmoothRep.mkIso
      { toLinearMap := (⊤ : Subrepresentation A.representation).toSubmodule.subtype
        isIntertwining' := fun _ => rfl
        invFun := fun x => ⟨x, trivial⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (F.mapIso e).toLinearEquiv.length_eq
  rw [← htop]
  have key : ∀ j : ℕ, (hj : j ≤ n) → len ⟨j, Nat.lt_succ_of_le hj⟩ =
      ∑ i : Fin j, Module.length R (F.obj (s.smoothGradedObject ⟨i, lt_of_lt_of_le i.isLt hj⟩)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simpa using hzero
    | succ j ih =>
      intro hj
      have hjn : j < n := hj
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [← ih hjn.le]
      exact hstep ⟨j, hjn⟩
  exact key n le_rfl

end Length

section Projective

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {P D : SmoothRep.{0, uG, uV} ℂ G}

/-- Applying `Hom(P, -)` for a projective `P` to an irreducible object gives
an endomorphism-ring module of length at most one. -/
theorem moduleLength_coyonedaObj_le_one [Projective P] (hD : D.IsIrreducible) :
    Module.length (End P)ᵐᵒᵖ ((preadditiveCoyonedaObj P).obj D) ≤ 1 := by
  classical
  by_cases he : ∃ f : P ⟶ D, f ≠ 0
  · obtain ⟨f, hf⟩ := he
    let M := (preadditiveCoyonedaObj P).obj D
    have hnon : Nontrivial M := ⟨⟨f, 0, hf⟩⟩
    apply le_of_eq
    rw [Module.length_eq_one_iff, isSimpleModule_iff]
    apply IsSimpleOrder.of_forall_eq_top
    intro S hS
    rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨g, hg, hg0⟩ : ∃ g ∈ S, g ≠ 0 := by
      by_contra! h
      exact hS ((Submodule.eq_bot_iff _).mpr h)
    have hgs : Function.Surjective (SmoothRep.hom (g : P ⟶ D)) :=
      (Representation.IsIrreducible.surjective_or_eq_zero
        (SmoothRep.hom (g : P ⟶ D))).resolve_right (fun h => hg0 (SmoothRep.hom_ext' h))
    have : Epi (g : P ⟶ D) := (SmoothRep.epi_iff_surjective _).mpr hgs
    let a := MulOpposite.op (End.of (Projective.factorThru (x : P ⟶ D) g))
    have heq : a • g = x := Projective.factorThru_comp (x : P ⟶ D) g
    exact heq ▸ S.smul_mem a hg
  · have : Subsingleton ((preadditiveCoyonedaObj P).obj D) := ⟨fun f g =>
      (not_ne_iff.mp (fun hf => he ⟨f, hf⟩)).trans (not_ne_iff.mp (fun hg => he ⟨g, hg⟩)).symm⟩
    simp

end Projective

end Langlands.CuspidalSupport

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme CuspidalSupport Plancherel
open scoped CategoryTheory.MonObj

universe u v

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M N : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (hl : IsRationalLeviSubgroup l) (hp : IsParabolicSubgroup p)

variable (hG : IsConnectedReductive G) (r : N ⟶ P)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hmul : IsIso (subgroupMultiplication l r))

/-- The normalized Jacquet functor followed by the Hom functor from `B`, with
action of the opposite endomorphism ring of `B` by precomposition. -/
def leviJacquetCoyoneda
    (B : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M)) :
    SmoothRep.{0, u, max u v} ℂ (rationalPoints G) ⥤ ModuleCat.{max u v} (End B)ᵐᵒᵖ :=
  letI := leviPointTopology l hl
  leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul ⋙ preadditiveCoyonedaObj B

include hG in
set_option maxHeartbeats 800000 in
/-- The VI.5.3 (iii) filtration bounds the length of `Hom(Π, r_P i_P ρ)` by
the number of double cosets preserving the inertia class of `ρ`, for a
projective `Π` whose irreducible subquotients lie in that class. -/
theorem leviJacquetInduction_coyoneda_length_le
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hρ : letI := leviPointTopology l hl; ρ.IsIrreducible)
    (hρsc : letI := leviPointTopology l hl
      haveI := hl.isConnectedReductive.isAffineHom
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsSupercuspidal ρ) :
    letI := leviPointTopology l hl
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    ∀ (B : SmoothRep.{0, u, max u v} ℂ (rationalPoints M)) [Projective B],
      rationalInertiaBlockProperty M (rationalInertiaBaseLift M ρ) B →
      Module.length (End B)ᵐᵒᵖ ((preadditiveCoyonedaObj B).obj
        ((leviJacquetFunctor p l r hp hr hl hmul).obj
          ((leviInductionFunctor p l r hp hr hl hmul).obj ρ))) ≤
        (twistStabilizerDoubleCosets p l hp hl ρ).encard := by
  classical
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  intro B _ hB
  let F := preadditiveCoyonedaObj B
  have hconj : ∃ (g : rationalPoints G) (φ : M ≅ M),
      φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom := by
    refine ⟨1, Iso.refl _, ?_⟩
    simp only [Iso.refl_hom, Category.id_comp, innerIso_one_hom, Category.comp_id]
  obtain ⟨⟨m, c, z, φ, e, hc, hφ, he, s, hs⟩, -⟩ :=
    leviJacquetInductionSupercuspidalFiltration.{u, v} k G hG P M N P M N
      p l r hp hl hr hmul p l r hp hl hr hmul hconj ρ hρsc
  let W := twistStabilizerDoubleCosets p l hp hl ρ
  let T : Finset (Fin m) := Finset.univ.filter (fun i => (c i).val ∈ W)
  have hgrade (i : Fin m) :
      (s.smoothGradedObject i).IsIrreducible := by
    exact (Langlands.isIrreducible_iff_of_equiv (hs i).some).mpr
      ((SmoothRep.isIrreducible_pullbackFunctor_obj_iff (e i) ρ).mpr hρ)
  have hcounts (i : Fin m) (f : B ⟶ s.smoothGradedObject i) (hf : f ≠ 0) :
      (c i).val ∈ W := by
    have : (s.smoothGradedObject i).representation.IsIrreducible := hgrade i
    have hsurj : Function.Surjective (SmoothRep.hom f) :=
      (Representation.IsIrreducible.surjective_or_eq_zero (SmoothRep.hom f)).resolve_right
        (fun h => hf (SmoothRep.hom_ext' h))
    have hsub : SmoothRep.IsSubquotient (s.smoothGradedObject i) B :=
      SmoothRep.isSubquotient_iff_exists.mpr
        ⟨B, 𝟙 B, f, fun _ _ h => h, hsurj⟩
    obtain ⟨χ, ⟨iso⟩⟩ := hB (s.smoothGradedObject i) (hgrade i) hsub
    have elift : (rationalUnramifiedTwist M χ ρ).representation.Equiv
        (rationalUnramifiedTwist M χ (rationalInertiaBaseLift M ρ)).representation :=
      Representation.Equiv.mk ULift.moduleEquiv.symm (fun _ => LinearMap.ext fun _ => rfl)
    let E := (hs i).some.symm.trans ((SmoothRep.equivOfIso iso).trans elift.symm)
    exact ⟨z i, φ i, e i, χ, hc i, hφ i, he i, ⟨SmoothRep.mkIso E⟩⟩
  rw [moduleLength_obj_eq_sum_of_filtration F s]
  calc
    _ ≤ ∑ i : Fin m, (if (c i).val ∈ W then 1 else 0 : ℕ∞) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : (c i).val ∈ W
      · rw [ite_eq_left h]
        exact moduleLength_coyonedaObj_le_one (hgrade i)
      · rw [ite_eq_right h, nonpos_iff_eq_zero, Module.length_eq_zero_iff]
        have key (f : B ⟶ s.smoothGradedObject i) : f = 0 :=
          not_ne_iff.mp (fun hf => h (hcounts i f hf))
        exact ⟨fun f g => (key f).trans (key g).symm⟩
    _ = (T.card : ℕ∞) := by
      rw [Finset.card_filter]
      push_cast
      rfl
    _ ≤ W.encard := by
      rw [← Set.encard_coe_eq_coe_finsetCard]
      exact Set.encard_le_encard_of_injOn
        (fun i hi => (Finset.mem_filter.mp hi).2)
        (fun _ _ _ _ hij => c.injective (Subtype.ext hij))

include hG in
set_option maxHeartbeats 1200000 in
/-- The Jacquet Hom functor from the norm-kernel summand induction detects every
irreducible subquotient of `i_P^G ρ`, given VI.5.3 (ii), second adjointness and
independence of the induced progenerator. -/
theorem nontrivial_leviJacquetCoyoneda_of_isSubquotient
    (hns : LeviJacquetInductionNoSupercuspidalStatement.{u, v})
    (hIndep : InducedProgeneratorIndependenceStatement.{u, v})
    (hAdj : LeviSecondAdjointnessStatement.{u, v}) :
    haveI := hl.isConnectedReductive.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    haveI := hl.isConnectedReductive.smooth
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)), ρ.IsIrreducible → IsSupercuspidal ρ →
    ∀ (ρ₀ : SmoothRep.{0, u, v} ℂ (rationalCommonNormKernel M)), ρ₀.IsIrreducible →
    ∀ (j : ρ₀ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel M) ρ),
      Function.Injective (SmoothRep.hom j) →
      Projective (rationalNormKernelSummandInduction M ρ₀) →
    ∀ (A : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)), A.IsIrreducible →
      SmoothRep.IsSubquotient A ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) →
      Nontrivial ((leviJacquetCoyoneda p l hl hp r hr hmul
        (rationalNormKernelSummandInduction M ρ₀)).obj A) := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hρ hsc ρ₀ hρ₀ j hj hproj A hA hsub
  let B := rationalNormKernelSummandInduction M ρ₀
  obtain ⟨Q, L, U, q, lQ, rQ, hq, hlQ, hrQ, hmulQ, hconj, -, σ, hσ, -, hquot, hσsub⟩ :=
    exists_conjugateLevi_supercuspidal_jacquetQuotient hns hG p l r hp hl hr hmul ρ hsc A hA hsub
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology lQ hlQ
  obtain ⟨⟨m, _, z, φ, e, _, hφ, he, filtration, hgrade⟩, -⟩ :=
    leviJacquetInductionSupercuspidalFiltration.{u, v} k G hG P M N Q L U
      p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hconj ρ hsc
  obtain ⟨i, hi⟩ := filtration.exists_smoothGradedObject_subquotient hσ hσsub
  have hirr : (filtration.smoothGradedObject i).IsIrreducible :=
    (Langlands.isIrreducible_iff_of_equiv (hgrade i).some).mpr
      ((SmoothRep.isIrreducible_pullbackFunctor_obj_iff (e i) ρ).mpr hρ)
  obtain ⟨isoGrade⟩ := NormalHecke.nonempty_iso_of_isSubquotient hirr hσ hi
  have liftEquiv : (SmoothRep.pullback (e i) ρ).representation.Equiv
      (SmoothRep.pullback (e i) (rationalInertiaBaseLift M ρ)).representation :=
    Representation.Equiv.mk ULift.moduleEquiv.symm (fun _ => LinearMap.ext fun _ => rfl)
  let isoσ := isoGrade ≪≫ SmoothRep.mkIso ((hgrade i).some.trans liftEquiv)
  obtain ⟨f, hf⟩ := exists_nonzero_rationalNormKernelSummandInduction M ρ ρ₀ j hρ₀ hj
    (rationalInertiaBaseLift M ρ) (IsRationalInertiaRelated.refl _)
  let T := SmoothRep.pullbackFunctor (e i)
  have hf' : T.map f ≠ 0 := by
    obtain ⟨x, hx⟩ := (smoothRep_ne_zero_iff_exists_apply_ne_zero f).mp hf
    exact (smoothRep_ne_zero_iff_exists_apply_ne_zero (T.map f)).mpr ⟨x, hx⟩
  let s : T.obj B ⟶ σ := T.map f ≫ isoσ.inv
  have hs : s ≠ 0 := fun h ↦ hf'
    ((@Preadditive.IsIso.comp_right_eq_zero _ _ _ _ _ _ (T.map f) isoσ.inv
      isoσ.isIso_inv).mp h)
  obtain ⟨t, ht⟩ := hquot
  have : Epi t := (SmoothRep.epi_iff_surjective _).mpr ht
  have : Projective (T.obj B) :=
    ((SmoothRep.pullbackEquivalence (e i)).map_projective_iff B).mpr hproj
  let lift := Projective.factorThru s t
  have hlift : lift ≠ 0 := by
    intro h
    apply hs
    rw [← Projective.factorThru_comp s t, ← show lift = Projective.factorThru s t from rfl,
      h, Limits.zero_comp]
  let pop := oppositeLeviParabolic hG p l hp hl
  let qop := oppositeLeviParabolic hG q lQ hq hlQ
  have hOpp : (φ i).inv ≫ qop.levi ≫ qop.inclusion =
      pop.levi ≫ pop.inclusion ≫ (G.innerIso (z i)⁻¹).hom := by
    rw [qop.levi_comp, ← Category.assoc pop.levi pop.inclusion, pop.levi_comp, Category.assoc]
    have h := congrArg (fun a : L ⟶ G =>
      (φ i).inv ≫ a ≫ (G.innerIso (z i)⁻¹).hom) (hφ i)
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, G.innerIso_inv_hom, Iso.hom_inv_id,
      Category.comp_id] using h.symm
  obtain ⟨independence⟩ := hIndep k G hG pop.parabolic M pop.radical qop.parabolic L qop.radical
    pop.inclusion pop.levi pop.unipotent pop.isParabolic pop.isLevi pop.isRadical pop.multiplication
    qop.inclusion qop.levi qop.unipotent qop.isParabolic qop.isLevi qop.isRadical qop.multiplication
    (z i)⁻¹ (φ i).symm hOpp (e i) (he i) ρ hρ hsc ρ₀ hρ₀ j hj
  have hP : pointImage pop.inclusion ⊓ pointImage p = pointImage (pop.levi ≫ pop.inclusion) := by
    rw [inf_comm, pop.intersection, pop.levi_comp]
  have hQ : pointImage qop.inclusion ⊓ pointImage q = pointImage (qop.levi ≫ qop.inclusion) := by
    rw [inf_comm, qop.intersection, qop.levi_comp]
  obtain ⟨adjP⟩ := hAdj k G hG pop.parabolic P M pop.radical N
    pop.inclusion pop.levi pop.unipotent pop.isParabolic pop.isLevi pop.isRadical pop.multiplication
    p l r hp hl hr hmul pop.levi_comp.symm hP
  obtain ⟨adjQ⟩ := hAdj k G hG qop.parabolic Q L qop.radical U
    qop.inclusion qop.levi qop.unipotent qop.isParabolic qop.isLevi qop.isRadical qop.multiplication
    q lQ rQ hq hlQ hrQ hmulQ qop.levi_comp.symm hQ
  let := leviInductionFunctor_additive.{u, max u v} pop.inclusion pop.levi pop.unipotent
    pop.isParabolic pop.isRadical pop.isLevi pop.multiplication
  let := leviInductionFunctor_additive.{u, max u v} qop.inclusion qop.levi qop.unipotent
    qop.isParabolic qop.isRadical qop.isLevi qop.multiplication
  let g := (adjQ.homAddEquiv (T.obj B) A).symm lift
  have hg : g ≠ 0 := by
    intro h
    apply hlift
    exact (adjQ.homAddEquiv (T.obj B) A).symm.injective
      (h.trans (map_zero _).symm)
  let a := adjP.homAddEquiv B A (independence.hom ≫ g)
  refine ⟨⟨a, 0, ?_⟩⟩
  intro ha
  apply hg
  have hcomp : independence.hom ≫ g = 0 :=
    (adjP.homAddEquiv B A).injective (ha.trans (map_zero _).symm)
  exact (@Preadditive.IsIso.comp_left_eq_zero _ _ _ _ _ _ independence.hom g
    independence.isIso_hom).mp hcomp

set_option maxHeartbeats 1200000 in
/-- Renard VI.10.3, Corollary, given independence of the induced progenerator,
second adjointness and the VI.5.2 lemma on proper parabolic induction. -/
theorem supercuspidalInductionLength_of_structuralInputs
    (hIndep : InducedProgeneratorIndependenceStatement.{u, v})
    (hAdj : LeviSecondAdjointnessStatement.{u, v})
    (hproper : LeviInductionNoSupercuspidalSubquotientStatement.{u, v}) :
    SupercuspidalInductionLengthStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hρ hsc
  obtain ⟨S, hS⟩ := rationalNormKernelConstituent_of_finiteRestriction
    rationalNormKernelFiniteRestriction.{u, v} k M hl.isConnectedReductive ρ hρ
  let A := SmoothRep.restrictSubgroup (rationalCommonNormKernel M) ρ
  let ρ₀ := A.subrepresentation S
  let j : ρ₀ ⟶ A := A.subtype S
  have hj : Function.Injective (SmoothRep.hom j) := A.subtype_injective S
  let B := rationalNormKernelSummandInduction M ρ₀
  have : Projective B := projective_rationalNormKernelSummandInduction_of_jointSpecialCompact
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence p l hp hl ρ hsc ρ₀ j hj
  have hB : rationalInertiaBlockProperty M (rationalInertiaBaseLift M ρ) B :=
    rationalSummandInduction_mem_block M hl.isConnectedReductive ρ hρ ρ₀ hS j hj
  let J := leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul
  let F := leviJacquetCoyoneda p l hl hp r hr hmul B
  let := leviInductionFunctor_additive.{u, max u v} p l r hp hr hl hmul
  have : J.Additive := (leviFirstAdjunction p l r hp hr hl hmul).left_adjoint_additive
  have : F.Additive := show (J ⋙ preadditiveCoyonedaObj B).Additive from inferInstance
  have : (preadditiveCoyonedaObj B).PreservesHomology :=
    preservesHomology_preadditiveCoyonedaObj_of_projective B
  have : F.PreservesHomology := by
    apply ((Functor.exact_tfae F).out 1 3).mp
    intro C hC
    have hJC : (C.map J).ShortExact := (smoothShortComplex_shortExact_iff _).mpr
      ((leviParabolicFunctorsExact.{u, max u v} k G hG P M N p l r hp hl hr hmul).2 _ _
        ((smoothShortComplex_shortExact_iff C).mp hC))
    have := (preadditiveCoyonedaObj B).preservesFiniteLimits_of_preservesHomology
    have := (preadditiveCoyonedaObj B).preservesFiniteColimits_of_preservesHomology
    exact hJC.map_of_exact (preadditiveCoyonedaObj B)
  let π := (leviInductionFunctor p l r hp hr hl hmul).obj ρ
  let W := twistStabilizerDoubleCosets p l hp hl ρ
  have hns := leviJacquetInductionNoSupercuspidal_of_geometricLemma
    representedGeometricLemma hproper
  have hle : repLength π.representation ≤ W.encard :=
    (repLength_le_of_exactModuleFunctor F π
      (nontrivial_leviJacquetCoyoneda_of_isSubquotient p l hl hp hG r hr hmul hns hIndep hAdj
        ρ hρ hsc ρ₀ hS j hj ‹Projective B›)).trans
      (leviJacquetInduction_coyoneda_length_le p l hl hp hG r hr hmul ρ hρ hsc B hB)
  change repLength π.representation ≤ W.encard ∧ (W.encard ≤ 1 → π.IsIrreducible)
  refine ⟨hle, fun hW => repLength_eq_one_iff.mp (le_antisymm (hle.trans hW) ?_)⟩
  have : Nontrivial ρ := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints M))
    ρ.representation.asModule
  exact Order.one_le_iff_pos.mpr (repLength_pos_iff.mpr
    (leviInduction_nontrivial p l r hp hl hr hmul ρ))

end Langlands.Aubert.General.RepresentedParabolic
