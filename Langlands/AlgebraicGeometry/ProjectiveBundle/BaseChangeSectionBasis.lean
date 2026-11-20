import Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishingProof
import Langlands.AlgebraicGeometry.Modules.SectionResidueStalkProof
import Langlands.AlgebraicGeometry.Modules.TensorSections
import Langlands.AlgebraicGeometry.LinearSystemMorphismProof
import Langlands.AlgebraicGeometry.ProperRationalImmersionClosedImmersionProof
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationFibreBasis
import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationRestriction
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Pulled-back section bases, generation, and closed immersions after base change

Tools for passing between a field and an extension field: a basis of the complete linear
system transported along the canonical direct-image comparison, an epimorphism criterion for
morphisms onto a line bundle, the closed-immersion criterion for linear systems over an
algebraically closed field, and fpqc descent of monomorphisms and closed immersions.
-/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.SchemeModule

open Langlands.AlgebraicGeometry.Picard

/-- A morphism onto a line bundle is an epimorphism when every point lies in the
nonvanishing locus of the image of some global section. -/
lemma epi_of_forall_mem_nonvanishingLocus {X : Scheme.{u}} {N : X.Modules}
    {L : LineBundle X} (φ : N ⟶ L.obj)
    (h : ∀ x : X, ∃ t : GlobalSections N, x ∈ nonvanishingLocus L.obj (φ.app ⊤ t)) :
    Epi φ := by
  apply Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishing.epi_of_isLocallySurjective
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x
  obtain ⟨t, ht⟩ := h x
  have hframe : IsStalkFrame L.obj (φ.app ⊤ t) x :=
    (lineBundleResidueStalkCriterion X L _ x).mp ht
  unfold IsStalkFrame at hframe
  rw [sectionHom_naturality, Functor.map_comp, Functor.map_comp] at hframe
  intro y
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor Ab x).map
        ((Scheme.Modules.toPresheaf X).map (sectionHom N t)) ≫
      (TopCat.Presheaf.stalkFunctor Ab x).map
        ((Scheme.Modules.toPresheaf X).map φ))).2 y
  rw [ConcreteCategory.comp_apply] at hz
  exact ⟨_, hz⟩

end Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.LinearSystem

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

/-- Over an algebraically closed field, base-point-free sections of a line bundle on a
proper scheme whose `K`-span is the complete linear system define a closed immersion as soon
as the complete linear system separates rational points and rational tangent vectors. -/
theorem isClosedImmersion_linearSystemMap_of_separates {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    {L : LineBundle X} {n : ℕ} {s : Fin (n + 1) → GlobalSections L.obj}
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i))
    (hsep : SeparatesPointsAndTangents p L)
    (hspan : ∀ σ : GlobalSections L.obj, ∃ c : Fin (n + 1) → K, σ = linComb p s c) :
    IsClosedImmersion (linearSystemMap p hs) := by
  have hφ : linearSystemMap p hs ≫ projectiveSpaceToSpec K n = p := linearSystemMap_toSpec p hs
  have : IsProper (linearSystemMap p hs ≫ projectiveSpaceToSpec K n) := by rw [hφ]; infer_instance
  have : IsProper (linearSystemMap p hs) :=
    IsProper.of_comp (linearSystemMap p hs) (projectiveSpaceToSpec K n)
  have : LocallyOfFiniteType p := inferInstance
  refine properRationalImmersion_isClosedImmersion K X (ProjectiveSpace K n) p
    (projectiveSpaceToSpec K n) (linearSystemMap p hs) hφ ?_ ?_
  · intro x y hx hy H
    by_contra hne
    obtain ⟨σ, hσx, hσy⟩ := hsep.2.1 x y hx hy hne
    obtain ⟨c, rfl⟩ := hspan σ
    apply hσy
    obtain ⟨j, hj⟩ := exists_mem_trivializationOpen hs (x (IsLocalRing.closedPoint K))
    have hxj := forall_mem_of_mem hj
    have hyj : ∀ τ, y τ ∈ trivializationOpen L.obj (s j) := by
      apply forall_mem_of_mem
      apply mem_trivializationOpen_of_comp_mem p hs y j
      rw [← H]
      exact comp_mem_coordinateOpen p hs hxj _
    exact (vanishesAlong_linComb_iff_of_comp_eq p hs hxj hyj H c).mp hσx
  · intro x hx t ht H
    by_contra hne
    obtain ⟨σ, hσx, hσt⟩ := hsep.2.2 x hx t ⟨ht, hne⟩
    obtain ⟨c, rfl⟩ := hspan σ
    apply hσt
    obtain ⟨j, hj⟩ := exists_mem_trivializationOpen hs (x (IsLocalRing.closedPoint K))
    have hxj := forall_mem_of_mem hj
    have htj := forall_mem_of_augmentation_comp ht.2 hj
    have hx'j : ∀ τ, (dualNumberProjection K ≫ x) τ ∈ trivializationOpen L.obj (s j) :=
      fun τ ↦ by rw [Scheme.Hom.comp_apply]; exact hxj _
    exact (vanishesAlong_linComb_iff_of_comp_eq p hs htj hx'j H c).mpr
      (vanishesAlong_comp _ hσx)

end Langlands.AlgebraicGeometry.LinearSystem

namespace Langlands.AlgebraicGeometry

/-- Monomorphisms of schemes descend along fpqc coverings. -/
lemma mono_of_isPullback_of_fpqc {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    [Surjective f] [Flat f] [QuasiCompact f] [Mono fst] : Mono g := by
  have : MorphismProperty.IsStableUnderBaseChange
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
    @MorphismProperty.IsStableUnderBaseChange.inf _ _ (@Surjective ⊓ @Flat) @QuasiCompact
      (@MorphismProperty.IsStableUnderBaseChange.inf _ _ @Surjective @Flat
        inferInstance inferInstance) inferInstance
  have hD : (MorphismProperty.isomorphisms Scheme.{u}).diagonal.DescendsAlong
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := inferInstance
  rw [MorphismProperty.diagonal_isomorphisms] at hD
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.monomorphisms Scheme.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h ⟨⟨‹Surjective f›, ‹Flat f›⟩, ‹QuasiCompact f›⟩
    (MorphismProperty.monomorphisms.infer_property fst)

/-- A proper morphism whose base change along an fpqc covering is a closed immersion is a
closed immersion. -/
lemma isClosedImmersion_of_isPullback_of_fpqc {A X Y Z : Scheme.{u}} {fst : A ⟶ X}
    {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    [Surjective f] [Flat f] [QuasiCompact f] [IsClosedImmersion fst] [IsProper g] :
    IsClosedImmersion g := by
  have : Mono g := mono_of_isPullback_of_fpqc h
  exact (IsClosedImmersion.iff_isProper_and_mono g).mpr ⟨‹_›, ‹_›⟩

end Langlands.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open scoped TensorProduct ChangeOfRings

variable {R R' : CommRingCat.{u}} {X X' : Scheme.{u}} (p : X ⟶ Spec R) (L : LineBundle X)
  (β : Spec R' ⟶ Spec R) (p' : X' ⟶ Spec R') (q : X' ⟶ X) (w : q ≫ p = p' ≫ β)
  [((Scheme.Modules.pushforward p).obj L.obj).IsQuasicoherent]
  [IsIso (baseChangeEvaluation p L (𝟙 _) β p' q w)]

/-- A basis of the global sections of a module on `Spec R` over `R`, read as a basis over
`Γ(Spec R, ⊤)` through the canonical identification. -/
def specGlobalSectionsBasis {R : CommRingCat.{u}} {N : (Spec R).Modules} {I : Type*}
    (b : Module.Basis I R (moduleSpecΓFunctor.obj N)) :
    Module.Basis I Γ(Spec R, ⊤) (GlobalSections N) :=
  letI : Module Γ(Spec R, ⊤) (moduleSpecΓFunctor.obj N) :=
    inferInstanceAs (Module Γ(Spec R, ⊤) (GlobalSections N))
  b.mapCoeffs (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm
    (fun c x ↦ (moduleSpecΓFunctor_smul N c x).symm)

lemma specGlobalSectionsBasis_apply {R : CommRingCat.{u}} {N : (Spec R).Modules} {I : Type*}
    (b : Module.Basis I R (moduleSpecΓFunctor.obj N)) (i : I) :
    specGlobalSectionsBasis b i = b i := by
  unfold specGlobalSectionsBasis
  let : Module Γ(Spec R, ⊤) (moduleSpecΓFunctor.obj N) :=
    inferInstanceAs (Module Γ(Spec R, ⊤) (GlobalSections N))
  exact Module.Basis.mapCoeffs_apply (M := moduleSpecΓFunctor.obj N) _ _ _ i

/-- A basis of the complete linear system over the affine base, transported to the
base change through the canonical comparison of direct images. -/
def baseChangeSectionBasis {I : Type*}
    (b : Module.Basis I R ((relativeGlobalSections p).obj L.obj)) :
    Module.Basis I R'
      ((relativeGlobalSections p').obj ((LineBundle.pullback q).obj L).obj) := by
  let b₀ : Module.Basis I Γ(Spec R, ⊤)
      (GlobalSections ((Scheme.Modules.pushforward p).obj L.obj)) :=
    specGlobalSectionsBasis b
  have h : (⊤ : (Spec R').Opens) ≤ β ⁻¹ᵁ ⊤ := le_top
  letI : Algebra Γ(Spec R, ⊤) Γ(Spec R', ⊤) := (β.appLE ⊤ ⊤ h).hom.toAlgebra
  let b₁ : Module.Basis I Γ(Spec R', ⊤)
      Γ((Scheme.Modules.pullback β).obj ((Scheme.Modules.pushforward p).obj L.obj), ⊤) :=
    (b₀.baseChange Γ(Spec R', ⊤)).map
      (LinearEquiv.ofBijective
        (pullbackTensorMap β ((Scheme.Modules.pushforward p).obj L.obj) h).hom
        (pullbackTensorMap_bijective β _ h (isAffineOpen_top _) (isAffineOpen_top _)))
  let b₂ : Module.Basis I Γ(Spec R', ⊤)
      (GlobalSections ((Scheme.Modules.pushforward p').obj
        ((LineBundle.pullback q).obj L).obj)) :=
    b₁.map ((globalSections (Spec R')).mapIso
      (asIso (baseChangeEvaluation p L (𝟙 _) β p' q w))).toLinearEquiv
  exact b₂.mapCoeffs (Scheme.ΓSpecIso R').commRingCatIsoToRingEquiv (by
    intro c x
    change (Scheme.ΓSpecIso R').inv ((Scheme.ΓSpecIso R').hom c) • x = c • x
    rw [Iso.hom_inv_id_apply])

/-- The transported basis consists of the actual pullbacks of the original sections. -/
lemma baseChangeSectionBasis_apply {I : Type*}
    (b : Module.Basis I R ((relativeGlobalSections p).obj L.obj)) (i : I) :
    (baseChangeSectionBasis p L β p' q w b i : GlobalSections
        ((LineBundle.pullback q).obj L).obj) =
      pullbackSection q L.obj (b i) := by
  have h : (⊤ : (Spec R').Opens) ≤ β ⁻¹ᵁ ⊤ := le_top
  have h1 : (baseChangeSectionBasis p L β p' q w b i : GlobalSections
        ((LineBundle.pullback q).obj L).obj) =
      (baseChangeEvaluation p L (𝟙 _) β p' q w).app ⊤
        (pullbackTensorMap β ((Scheme.Modules.pushforward p).obj L.obj) h
          ((1 : Γ(Spec R', ⊤)) ⊗ₜ[Γ(Spec R, ⊤), (β.appLE ⊤ ⊤ h).hom]
            (b i : GlobalSections ((Scheme.Modules.pushforward p).obj L.obj)))) := by
    unfold baseChangeSectionBasis
    erw [Module.Basis.mapCoeffs_apply, Module.Basis.map_apply, Module.Basis.map_apply]
    let : Algebra Γ(Spec R, ⊤) Γ(Spec R', ⊤) := (β.appLE ⊤ ⊤ h).hom.toAlgebra
    erw [Module.Basis.baseChange_apply, specGlobalSectionsBasis_apply]
    rfl
  rw [h1]
  erw [pullbackTensorMap_one_tmul β ((Scheme.Modules.pushforward p).obj L.obj) h]
  erw [baseChangeEvaluation_sectionPullbackLE p L (𝟙 _) β p' q w ⊤ h]
  exact (pullbackSection_eq_sectionPullbackLE q L.obj (b i)).symm

/-- After base change, every global section is a linear combination, with coefficients from
the new base ring, of the pullbacks of the members of a basis of the original complete linear
system. -/
lemma exists_eq_linComb_pullbackSection {K' : Type u} [CommRing K']
    (p'' : X' ⟶ Spec (CommRingCat.of K')) (β' : Spec (CommRingCat.of K') ⟶ Spec R)
    (w' : q ≫ p = p'' ≫ β') [IsIso (baseChangeEvaluation p L (𝟙 _) β' p'' q w')] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) R ((relativeGlobalSections p).obj L.obj))
    (σ : GlobalSections ((LineBundle.pullback q).obj L).obj) :
    ∃ c : Fin (n + 1) → K', σ = LinearSystem.linComb p''
      (fun i ↦ pullbackSection q L.obj (b i)) c := by
  let b' := baseChangeSectionBasis p L β' p'' q w' b
  let σ' : (relativeGlobalSections p'').obj ((LineBundle.pullback q).obj L).obj := σ
  refine ⟨fun i ↦ b'.repr σ' i, ?_⟩
  have hsum := b'.sum_repr σ'
  refine hsum.symm.trans ?_
  unfold LinearSystem.linComb
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine (moduleSpecΓFunctor_smul _ (b'.repr σ' i) (b' i)).trans ?_
  have h2 := baseChangeSectionBasis_apply p L β' p'' q w' b i
  dsimp only
  erw [h2]
  rfl

/-- After base change, every global section is a finite linear combination of the pullbacks
of the members of a basis (with any index type) of the original complete linear system. -/
lemma exists_eq_sum_pullbackSection {K' : Type u} [CommRing K']
    (p'' : X' ⟶ Spec (CommRingCat.of K')) (β' : Spec (CommRingCat.of K') ⟶ Spec R)
    (w' : q ≫ p = p'' ≫ β') [IsIso (baseChangeEvaluation p L (𝟙 _) β' p'' q w')] {I : Type*}
    (b : Module.Basis I R ((relativeGlobalSections p).obj L.obj))
    (σ : GlobalSections ((LineBundle.pullback q).obj L).obj) :
    ∃ (S : Finset I) (c : I → K'), σ = ∑ i ∈ S,
      Scheme.Modules.scalarsFromBase p'' (c i) • pullbackSection q L.obj (b i) := by
  let b' := baseChangeSectionBasis p L β' p'' q w' b
  let σ' : (relativeGlobalSections p'').obj ((LineBundle.pullback q).obj L).obj := σ
  refine ⟨(b'.repr σ').support, fun i ↦ b'.repr σ' i, ?_⟩
  have hsum := b'.linearCombination_repr σ'
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hsum
  refine hsum.symm.trans ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine (moduleSpecΓFunctor_smul _ (b'.repr σ' i) (b' i)).trans ?_
  have h2 := baseChangeSectionBasis_apply p L β' p'' q w' b i
  dsimp only
  erw [h2]
  rfl

/-- A section after base change vanishes along every morphism along which all pulled-back
basis sections vanish. -/
lemma vanishesAlong_of_forall_pullbackSection {K' : Type u} [CommRing K']
    (p'' : X' ⟶ Spec (CommRingCat.of K')) (β' : Spec (CommRingCat.of K') ⟶ Spec R)
    (w' : q ≫ p = p'' ≫ β') [IsIso (baseChangeEvaluation p L (𝟙 _) β' p'' q w')] {I : Type*}
    (b : Module.Basis I R ((relativeGlobalSections p).obj L.obj)) {T : Scheme.{u}} (y : T ⟶ X')
    (hy : ∀ i, VanishesAlong ((LineBundle.pullback q).obj L) y (pullbackSection q L.obj (b i)))
    (σ : GlobalSections ((LineBundle.pullback q).obj L).obj) :
    VanishesAlong ((LineBundle.pullback q).obj L) y σ := by
  obtain ⟨S, c, rfl⟩ := exists_eq_sum_pullbackSection p L q p'' β' w' b σ
  unfold VanishesAlong
  refine (LinearSystem.pullbackSection_sum (f := y) (S := S) _ _).trans
    (Finset.sum_eq_zero fun i _ ↦ ?_)
  refine (LinearSystem.pullbackSection_smul (f := y) _ _ _).trans ?_
  have h0 : pullbackSection y ((LineBundle.pullback q).obj L).obj
      (pullbackSection q L.obj (b i)) = 0 := hy i
  erw [h0, smul_zero]

end Langlands.AlgebraicGeometry.ProjectiveBundle
