/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
import all WeilConjectures.AlgebraicGeometry.SixFunctors.BrownHypothesesSmall
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesStructural
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.StratifiedTorIntervalDevissage
import WeilConjectures.AlgebraicGeometry.CohomologyTorInterval
import WeilConjectures.AlgebraicGeometry.Integral.IntegralConstructibleCompactness
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import WeilConjectures.CategoryTheory.CompactObjectsThick
import WeilConjectures.CategoryTheory.DerivedCategory.Products
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi

/-!
# Criteria and obstructions for Brown hypotheses

Source: blueprint latest, sec-six-functors-basics/sk-lem-brown-hypotheses,
proof paragraphs 1--2, and the sources cited at the individual declarations.

These proved formal criteria, generation arguments, and compactness obstructions are
separate from the unresolved arbitrary-field assertion in `BrownHypotheses`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.all false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

attribute [local instance 30000] brownHypothesesCondensedMonoidal
  brownHypothesesCondensedBraided brownHypothesesSheafMonoidal
  brownHypothesesSheafBraided brownHypothesesCoefficientMonObj
  brownHypothesesModuleMonoidalClosed
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar

/-- Cache the canonical tensor structure on pro-etale module objects. -/
noncomputable abbrev brownCriteriaModuleMonoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  inferInstance

attribute [local instance 30000] brownCriteriaModuleMonoidal

/-- Cache the canonical derived tensor structure on pro-etale module objects. -/
noncomputable abbrev brownCriteriaDerivedMonoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    MonoidalCategory (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :=
  inferInstance

attribute [local instance 30000] brownCriteriaDerivedMonoidal

/-- Exact countable products follow directly from repleteness and the exact forgetful
functor on module objects. Keep this proof local to avoid importing proper direct images. -/
private theorem brownHypotheses_countableAB4Star
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    CountableAB4Star (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
    Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)

attribute [local instance] brownHypotheses_countableAB4Star

private theorem isZero_of_shifted_orthogonal
    {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : ObjectProperty C) (K : C) (hK : localizingClosure S K)
    (horth : ∀ n : ℤ, S.rightOrthogonal (K⟦n⟧)) : IsZero K := by
  let P := (ObjectProperty.singleton K).shiftClosure ℤ
  have hP : IsLocalizingSubcategory P.leftOrthogonal := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I F hF hFP
    let := hF
    change P.leftOrthogonal (colimit F)
    intro Y f hY
    apply colimit.hom_ext
    intro j
    simpa using hFP j.as (colimit.ι F j ≫ f) hY
  have hSP : S ≤ P.leftOrthogonal := by
    intro M hM Y f hY
    obtain ⟨Z, n, e, hZ⟩ := hY
    have hZK : K = Z := (ObjectProperty.singleton_iff K Z).mp hZ
    subst Z
    apply (cancel_mono e.hom).mp
    simpa using horth n (f ≫ e.hom) hM
  have hid : (𝟙 K : K ⟶ K) = 0 :=
    hK P.leftOrthogonal hP hSP (𝟙 K)
      ((ObjectProperty.singleton K).le_shiftClosure K (by simp))
  exact (IsZero.iff_id_eq_zero K).mpr hid

/-- Any family representing every object of `S` up to isomorphism generates the
localizing closure of `S`. The property `S` need not be thick or shift-stable, and
the representatives need not be compact or pairwise nonisomorphic.

Source: blueprint latest, sec-six-functors-basics/sk-lem-brown-hypotheses,
proof paragraph 2 (blueprint: lem-sfb-localizing-closure-generators).

Proof: suppose all morphisms from the coproduct into every shift of `K` vanish.
Every map from one representative to a shift of `K` extends to the coproduct by
zero on the other summands. Thus every map from an object of `S` into a shift
of `K` vanishes. The left orthogonal of all shifts of `K` is replete,
triangulated, and closed under coproducts, since maps out of a coproduct are
determined by their components. It contains `S`, hence its localizing closure.
In particular it contains `K`, so the identity of `K` vanishes and `K` is zero.
Contraposition gives the stated nonzero-map generation criterion. -/
theorem localizingClosure_generatingFamily
    {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (S : ObjectProperty C) [hL : (localizingClosure S).IsTriangulated]
    {I : Type*} (E : I → (localizingClosure S).FullSubcategory) [HasCoproduct E]
    (hE : ∀ X : C, S X → ∃ i : I, Nonempty (X ≅ (E i).obj)) :
    IsTriangulatedGeneratingFamily E := by
  classical
  intro K hK
  by_contra! hn
  have horth : ∀ n : ℤ, S.rightOrthogonal (K.obj⟦n⟧) := by
    intro n X f hX
    obtain ⟨i, ⟨e⟩⟩ := hE X hX
    let q := ((localizingClosure S).ι.commShiftIso n).app K
    let a : E i ⟶ K⟦n⟧ := ObjectProperty.homMk (e.inv ≫ f ≫ q.inv)
    have ha : a = 0 := by
      have h := congrArg (fun g ↦ Sigma.ι E i ≫ g)
        (hn n (Limits.Sigma.desc (Pi.single (M := fun j ↦ E j ⟶ K⟦n⟧) i a)))
      simpa using h
    have h := congrArg (fun g ↦ e.hom ≫ g.hom ≫ q.hom) ha
    simpa [a] using h
  exact hK (IsZero.of_full_of_faithful_of_isZero (localizingClosure S).ι K
    (isZero_of_shifted_orthogonal S K.obj K.property horth))

/-- Compactness transports by precomposition with an isomorphism. -/
private theorem compact_of_iso
    {C : Type*} [Category.{u} C] [Preadditive C] [HasCoproducts.{u} C]
    {K L : C} (e : K ≅ L) (hL : IsCompactObject L) : IsCompactObject K := by
  exact (isCompactObject_iff_isCompactObj K).mpr
    (((isCompactObject_iff_isCompactObj L).mp hL).of_iso e)

/-- Brown's hypotheses reduce to thickness, essential smallness, and compactness of the
constructible finite-Tor objects. The ambient structures and generation follow formally
from the definition of the localizing closure, for every commutative condensed coefficient.

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraphs 1--2
(blueprint: lem-sfb-brown-hypotheses-criterion).

Proof: the forward direction uses essential smallness to choose a small equivalent
category of the constructible finite-Tor subcategory. Its representatives belong to the
localizing closure by minimality. The bundle makes them compact. Every constructible
finite-Tor object is isomorphic to a representative, so compactness transports to it.
For the reverse direction use the coefficient-independent structural theorem for local
smallness and split idempotents. The localizing intersection inherits its triangulation.
For any small presentation, compactness holds by the supplied objectwise assumption,
and the orthogonal/minimality argument proves generation. No assumption on a base field,
no skeletal condition, and no coefficient classification is used. -/
theorem brownHypothesesFor_iff
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    BrownHypothesesFor Λ X ↔
      let S := constantModelBoundedConstructible Λ X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K
      S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
        ObjectProperty.EssentiallySmall.{u + 1} S ∧
        ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
          letI := hSums
          ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
            S K.obj → IsCompactObject K := by
  classical
  let S := constantModelBoundedConstructible Λ X ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosureProEtale Λ X
  constructor
  · rintro ⟨hsmall, htri, hiso, hS, hSiso, hret, hess, hid, hcop, hgen⟩
    let _ := hsmall
    let _ := htri
    let _ := hcop
    refine ⟨hS, hSiso, hret, hess, hcop, ?_⟩
    obtain ⟨J, hJ, ⟨e⟩⟩ := (ObjectProperty.exists_equivalence_iff S).mpr hess
    let _ := hJ
    have hL (j : J) : L (e.inverse.obj j).obj :=
      fun _ _ hSP ↦ hSP _ (e.inverse.obj j).property
    have hc := (hgen J e.symm hL).1
    intro K hK
    let B : S.FullSubcategory := ⟨K.obj, hK⟩
    let K' : L.FullSubcategory :=
      ⟨(e.inverse.obj (e.functor.obj B)).obj, hL (e.functor.obj B)⟩
    let eK : K ≅ K' := L.isoMk (S.ι.mapIso (e.unitIso.app B))
    exact compact_of_iso eK (hc (e.functor.obj B))
  · rintro ⟨hS, hSiso, hret, hess, hcop, hc⟩
    obtain ⟨hsmall, htri, hiso, hid, _⟩ := brownHypotheses_structural Λ X
    let _ := hsmall
    let _ := htri
    let _ : (localizingClosure S).IsTriangulated := htri
    let _ : HasCoproducts.{u + 1} (localizingClosure S).FullSubcategory := hcop
    let _ := hid
    let _ := hcop
    refine ⟨hsmall, htri, hiso, hS, hSiso, hret, hess, hid, hcop, ?_⟩
    intro G _ e hL
    refine ⟨fun g ↦ hc _ (e.functor.obj g).property, ?_⟩
    have hsum : HasCoproduct (fun g : G ↦
        (⟨(e.functor.obj g).obj, hL g⟩ : L.FullSubcategory)) := inferInstance
    let _ := hsum
    apply localizingClosure_generatingFamily (E := fun g : G ↦
      (⟨(e.functor.obj g).obj, hL g⟩ : L.FullSubcategory)) S
    intro Y hY
    let B : S.FullSubcategory := ⟨Y, hY⟩
    exact ⟨e.inverse.obj B, ⟨(S.ι.mapIso (e.counitIso.app B)).symm⟩⟩

-- Later proofs use the criterion API; keep the large bundle folded.
attribute [local irreducible] BrownHypothesesFor

open scoped CategoryTheory.Obj in
open scoped CategoryTheory.Obj in
open scoped CategoryTheory.Obj in
open scoped CategoryTheory.Obj in
open scoped CategoryTheory.Obj in
open scoped CategoryTheory.Obj in
open scoped CategoryTheory.Obj in
open scoped CategoryTheory.Obj in
open scoped CategoryTheory.Obj in
/-- Lifting a finite discrete coefficient carrier preserves its condensed ring object. -/
private theorem finiteCoefficientLiftIso (A : Type) [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] :
    Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj (ULift.{u} A))) := by
  let ei : A ≃+* ULift.{u} A := ULift.ringEquiv.symm
  have hc : Continuous ei := continuous_of_discreteTopology
  have hc' : Continuous ei.symm := continuous_of_discreteTopology
  let er : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} A) :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hc).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop hc').comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply (f.down x)
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply (f.down x) }
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
  exact ⟨Mon.mkIso ea⟩

/-- Admissibility supplies the thickness and size clauses independently of compactness. -/
private theorem brownHypotheses_admissible_small
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X] :
    let S := constantModelBoundedConstructible Λ X ⊓
      fun K ↦ DerivedCategory.finiteTorAmplitude _ K
    S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
      ObjectProperty.EssentiallySmall.{u + 1} S := by
  classical
  let A₀ := ULift.{u} (ZMod 1)
  let _ : TopologicalSpace A₀ := ⊥
  have hA₀ : ∃ n : ℕ, (ℓ ^ n : A₀) = 0 := ⟨0, Subsingleton.elim _ _⟩
  let F₀ : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  rcases hΛ with h | h | h | h | h | h
  · obtain ⟨A, _, _, _, _, hA, ⟨r, hr⟩, ⟨e⟩⟩ := h
    let _ := hA
    have hpow : ∃ n : ℕ, (ℓ ^ n : ULift.{u} A) = 0 := by
      refine ⟨r, ?_⟩
      apply ULift.ext
      simpa using hr 1
    obtain ⟨ea⟩ := finiteCoefficientLiftIso.{u} A
    exact det_brown_hypotheses_small ℓ (ULift.{u} A) hpow F₀ Λ
      (Or.inl ⟨e ≪≫ ea⟩) X
  · exact det_brown_hypotheses_small ℓ A₀ hA₀ F₀ Λ (Or.inr (Or.inl h)) X
  · exact det_brown_hypotheses_small ℓ A₀ hA₀ F₀ Λ
      (Or.inr (Or.inr (Or.inr (Or.inl h)))) X
  · obtain ⟨F, h⟩ := h
    exact det_brown_hypotheses_small ℓ A₀ hA₀ F Λ
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) X
  · obtain ⟨F, h⟩ := h
    exact det_brown_hypotheses_small ℓ A₀ hA₀ F Λ
      (Or.inr (Or.inr (Or.inl h))) X
  · exact det_brown_hypotheses_small ℓ A₀ hA₀ F₀ Λ
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))) X

/-- For a Noetherian scheme, admissibility leaves only compactness to check.
No field, characteristic, or separatedness hypothesis is required for this equivalence.

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraphs 1--2,
and lemma-hypotheses-brown-representability--5, whose hypothesis is that X is Noetherian.
(blueprint: lem-sfb-brown-noetherian-compactness-criterion).

Proof: apply brownHypotheses_admissible_small to the actual admissibility predicate.
This supplies thickness and essential smallness
on any compact locally Noetherian scheme. The formal Brown criterion then extracts
compactness in one direction and assembles the bundle in the other direction.
The structural and generation clauses need no additional geometric hypothesis. -/
theorem brownHypothesesFor_iff_compact_of_noetherian
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    BrownHypothesesFor Λ X ↔
      ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
        letI := hSums
        ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
          (constantModelBoundedConstructible Λ X K.obj ∧
            DerivedCategory.finiteTorAmplitude _ K.obj) → IsCompactObject K := by
  have hsmall := brownHypotheses_admissible_small ℓ Λ hΛ X
  constructor
  · intro hB
    exact ((brownHypothesesFor_iff Λ X).mp hB).2.2.2.2
  · intro hc
    exact (brownHypothesesFor_iff Λ X).mpr
      ⟨hsmall.1, hsmall.2.1, hsmall.2.2.1, hsmall.2.2.2, hc⟩

end CategoryTheory
