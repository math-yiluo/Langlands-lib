import Langlands.AlgebraicGeometry.Picard.TwoAxisClassMurreConditionsStatement
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassProductBaseChange
import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedNoetherianOfSeesawProof
import Langlands.AlgebraicGeometry.Picard.ProperFormalLineBundleEffectivityProof
import Langlands.AlgebraicGeometry.Picard.TwoAxisBundleNormalization

/-! # Proof of Murre's (F3) for the two-axis class presheaf -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

namespace TwoAxisClassAdicLimits

open Langlands.AbelianScheme TwoAxisFamily TwoAxisRigidifiedLineBundle UnramifiedFunctor
open Langlands.AbelianScheme.MumfordPicardZero (pullbackCompIso)

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

/-- Over a noetherian local base, two line bundles on the self-product of the abelian scheme
whose restrictions to all infinitesimal neighbourhoods of the closed point are isomorphic are
isomorphic. -/
theorem nonempty_carrierIso_of_forall_adic (B : Type u) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] (f : Spec (CommRingCat.of B) ⟶ S) (L M : relative A (Over.mk f))
    (H : ∀ n : ℕ, Nonempty
      ((Scheme.Modules.pullback
          (productMap A (algebraOverBase f (B ⧸ IsLocalRing.maximalIdeal B ^ n)))).obj
          L.obj.carrier ≅
        (Scheme.Modules.pullback
          (productMap A (algebraOverBase f (B ⧸ IsLocalRing.maximalIdeal B ^ n)))).obj
          M.obj.carrier)) :
    Nonempty (L.obj.carrier ≅ M.obj.carrier) := by
  let A' := abelian A (Over.mk f)
  let P := (mumfordProduct A').left
  let c : P ⟶ Spec (CommRingCat.of B) := (mumfordProduct A').hom
  let fst₀ := pullback.fst c (𝟙 (Spec (CommRingCat.of B)))
  obtain ⟨Z, ι, hι, hZ⟩ := noetherianLineBundleSeesaw (R := B) c
    (fun B' _ _ ↦ mumfordProduct_appTop_bijective A' B') (𝟙 (Spec (CommRingCat.of B)))
    ((Scheme.Modules.pullback fst₀).obj L.obj.carrier)
    ((Scheme.Modules.pullback fst₀).obj M.obj.carrier)
    (L.property.pullback _) (M.property.pullback _)
  -- every infinitesimal neighbourhood of the closed point factors through `ι`
  have hfac : ∀ n : ℕ, ∃ z : Spec (CommRingCat.of (B ⧸ IsLocalRing.maximalIdeal B ^ n)) ⟶ Z,
      z ≫ ι = Spec.map (CommRingCat.ofHom
        (algebraMap B (B ⧸ IsLocalRing.maximalIdeal B ^ n))) := by
    intro n
    let h := algebraOverBase f (B ⧸ IsLocalRing.maximalIdeal B ^ n)
    let ψ : Spec (CommRingCat.of (B ⧸ IsLocalRing.maximalIdeal B ^ n)) ⟶
        Spec (CommRingCat.of B) :=
      Spec.map (CommRingCat.ofHom (algebraMap B (B ⧸ IsLocalRing.maximalIdeal B ^ n)))
    let g := pullback.fst (pullback.snd c (𝟙 _)) ψ ≫ fst₀
    have hg : g ≫ (mumfordProduct A').hom =
        pullback.snd (pullback.snd c (𝟙 _)) ψ ≫ h.left := by
      simp only [g, fst₀, Category.assoc]
      rw [pullback.condition (f := c), Category.comp_id, pullback.condition]
      rfl
    let φ := (productMap_isPullback A h).lift g _ hg
    have hφ : φ ≫ productMap A h = g := (productMap_isPullback A h).lift_fst _ _ _
    let e₁ := fun N : P.Modules ↦
      (pullbackCompIso (pullback.fst (pullback.snd c (𝟙 _)) ψ) fst₀ g rfl N).symm ≪≫
        pullbackCompIso φ (productMap A h) g hφ N
    obtain ⟨e⟩ := H n
    exact (hZ ψ).2 (LocallyIsoOver.of_iso _
      (e₁ L.obj.carrier ≪≫ (Scheme.Modules.pullback φ).mapIso e ≪≫ (e₁ M.obj.carrier).symm))
  -- by Krull's intersection theorem the closed subscheme is everything
  have hinj : Function.Injective ι.appTop := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hmem : ∀ n : ℕ,
        (Scheme.ΓSpecIso (CommRingCat.of B)).hom b ∈ IsLocalRing.maximalIdeal B ^ n := by
      intro n
      obtain ⟨z, hz⟩ := hfac n
      have h0 : (Spec.map (CommRingCat.ofHom
          (algebraMap B (B ⧸ IsLocalRing.maximalIdeal B ^ n)))).appTop b = 0 := by
        rw [← hz, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hb, map_zero]
      have h1 := congrArg (Scheme.ΓSpecIso (CommRingCat.of
        (B ⧸ IsLocalRing.maximalIdeal B ^ n))).hom h0
      rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, map_zero,
        CommRingCat.comp_apply] at h1
      exact Ideal.Quotient.eq_zero_iff_mem.1 h1
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal B)
      (IsLocalRing.maximalIdeal.isMaximal B).ne_top
    have h0 : (Scheme.ΓSpecIso (CommRingCat.of B)).hom b = 0 := by
      rw [← Ideal.mem_bot, ← hbot]
      exact Ideal.mem_iInf.2 hmem
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).inv h0
  have : IsIso ι := IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  obtain ⟨V, hV, ⟨e⟩⟩ := (hZ (𝟙 _)).1 ⟨inv ι, by simp⟩ (IsLocalRing.closedPoint B)
  let a₀ : P ⟶ pullback c (𝟙 _) := pullback.lift (𝟙 P) c (by simp)
  let a : P ⟶ pullback (pullback.snd c (𝟙 _)) (𝟙 _) :=
    pullback.lift a₀ (a₀ ≫ pullback.snd c (𝟙 _)) (by simp)
  have ha : a ≫ pullback.fst _ _ ≫ fst₀ = 𝟙 P := by
    simp [a, a₀, fst₀]
  obtain ⟨E⟩ := nonempty_pullback_iso_of_restrict_iso _ e a (fun x ↦
    (IsLocalRing.specializes_closedPoint
      ((a ≫ pullback.snd (pullback.snd c (𝟙 _)) (𝟙 _)) x)).mem_open V.2 hV)
  let e₂ := fun N : P.Modules ↦
    ((Scheme.Modules.pullbackId P).app N).symm ≪≫
      pullbackCompIso a (pullback.fst _ _ ≫ fst₀) (𝟙 P) ha N ≪≫
      (Scheme.Modules.pullback a).mapIso
        (pullbackCompIso (pullback.fst (pullback.snd c (𝟙 _)) (𝟙 _)) fst₀ _ rfl N)
  exact ⟨e₂ L.obj.carrier ≪≫ E ≪≫ (e₂ M.obj.carrier).symm⟩

/-- Restriction along an algebra map followed by the structure map is the structure map. -/
lemma algHomOver_comp_algebraOverBase {B : Type u} [CommRing B] (f : Spec (CommRingCat.of B) ⟶ S)
    {C D : Type u} [CommRing C] [Algebra B C] [CommRing D] [Algebra B D] (φ : C →ₐ[B] D) :
    algHomOver f φ ≫ algebraOverBase f C = algebraOverBase f D := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, algHomOver, algebraOverBase, Over.homMk_left]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]

section Existence

open FormalLineBundle

variable (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  (f : Spec (CommRingCat.of B) ⟶ S)

/-- The `n`-th adic test object `Spec (B / m^n)`. -/
abbrev adicTest (n : ℕ) : Over S :=
  algebraOver f (B ⧸ IsLocalRing.maximalIdeal B ^ n)

/-- The structure map of the `n`-th adic test object. -/
abbrev adicTestBase (n : ℕ) : adicTest B f n ⟶ Over.mk f :=
  algebraOverBase f (B ⧸ IsLocalRing.maximalIdeal B ^ n)

/-- The transition map from the `n`-th to the `(n+1)`-st adic test object. -/
abbrev adicTestTransition (n : ℕ) : adicTest B f n ⟶ adicTest B f (n + 1) :=
  algHomOver f (Ideal.Quotient.factorₐ B
    (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal B) n.le_succ))

omit [IsNoetherianRing B] in
lemma adicTestTransition_comp (n : ℕ) :
    adicTestTransition B f n ≫ adicTestBase B f (n + 1) = adicTestBase B f n :=
  algHomOver_comp_algebraOverBase f _

omit [IsNoetherianRing B] in
lemma adicBaseProjection_eq (n : ℕ) :
    adicBaseProjection (IsLocalRing.maximalIdeal B) n = (adicTestBase B f (n + 1)).left := by
  simp only [adicBaseProjection, algebraOverBase, Over.homMk_left, Ideal.Quotient.algebraMap_eq]

omit [IsNoetherianRing B] in
lemma adicBaseTransition_eq (n : ℕ) :
    adicBaseTransition (IsLocalRing.maximalIdeal B) n = (adicTestTransition B f (n + 1)).left :=
  rfl

/-- The `n`-th adic thickening of the self-product is the self-product over `B / m^(n+1)`. -/
def adicComparison (n : ℕ) :
    adicSpace (mumfordProduct (abelian A (Over.mk f))).hom (IsLocalRing.maximalIdeal B) n ⟶
      (mumfordProduct (abelian A (adicTest B f (n + 1)))).left :=
  (productMap_isPullback A (adicTestBase B f (n + 1))).lift (pullback.fst _ _) (pullback.snd _ _)
    (pullback.condition.trans
      (congrArg (pullback.snd _ _ ≫ ·) (adicBaseProjection_eq B f n)))

omit [IsNoetherianRing B] in
@[reassoc (attr := simp)]
lemma adicComparison_productMap (n : ℕ) :
    adicComparison A B f n ≫ productMap A (adicTestBase B f (n + 1)) =
      adicProjection (mumfordProduct (abelian A (Over.mk f))).hom
        (IsLocalRing.maximalIdeal B) n :=
  (productMap_isPullback A (adicTestBase B f (n + 1))).lift_fst _ _ _

omit [IsNoetherianRing B] in
@[reassoc (attr := simp)]
lemma adicComparison_hom (n : ℕ) :
    adicComparison A B f n ≫ (mumfordProduct (abelian A (adicTest B f (n + 1)))).hom =
      pullback.snd _ _ :=
  (productMap_isPullback A (adicTestBase B f (n + 1))).lift_snd _ _ _

/-- The inverse of the adic comparison. -/
def adicComparisonInv (n : ℕ) :
    (mumfordProduct (abelian A (adicTest B f (n + 1)))).left ⟶
      adicSpace (mumfordProduct (abelian A (Over.mk f))).hom (IsLocalRing.maximalIdeal B) n :=
  pullback.lift (productMap A (adicTestBase B f (n + 1)))
    (mumfordProduct (abelian A (adicTest B f (n + 1)))).hom (by
      rw [(productMap_isPullback A (adicTestBase B f (n + 1))).w, adicBaseProjection_eq B f n])

/-- The adic comparison is an isomorphism. -/
def adicComparisonIso (n : ℕ) :
    adicSpace (mumfordProduct (abelian A (Over.mk f))).hom (IsLocalRing.maximalIdeal B) n ≅
      (mumfordProduct (abelian A (adicTest B f (n + 1)))).left where
  hom := adicComparison A B f n
  inv := adicComparisonInv A B f n
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [adicComparisonInv, Category.assoc, pullback.lift_fst, Category.id_comp]
      exact adicComparison_productMap A B f n
    · simp only [adicComparisonInv, Category.assoc, pullback.lift_snd, Category.id_comp]
      exact adicComparison_hom A B f n
  inv_hom_id := by
    apply (productMap_isPullback A (adicTestBase B f (n + 1))).hom_ext
    · simp only [adicComparisonInv, Category.assoc, adicComparison_productMap,
        Category.id_comp]
      exact pullback.lift_fst _ _ _
    · simp only [adicComparisonInv, Category.assoc, adicComparison_hom, Category.id_comp]
      exact pullback.lift_snd _ _ _

omit [IsNoetherianRing B] in
lemma adicTransition_comparison (n : ℕ) :
    adicTransition (mumfordProduct (abelian A (Over.mk f))).hom
        (IsLocalRing.maximalIdeal B) n ≫ adicComparison A B f (n + 1) =
      adicComparison A B f n ≫ productMap A (adicTestTransition B f (n + 1)) := by
  apply (productMap_isPullback A (adicTestBase B f (n + 2))).hom_ext
  · rw [Category.assoc, adicComparison_productMap, adicTransition_projection, Category.assoc,
      ← productMap_comp, adicTestTransition_comp, adicComparison_productMap]
  · rw [Category.assoc, adicComparison_hom, Category.assoc,
      (productMap_isPullback A (adicTestTransition B f (n + 1))).w, adicComparison_hom_assoc,
      adicTransition, pullback.lift_snd, adicBaseTransition_eq B f n]

/-- The actual line bundle of the chosen representative of a class over the `n`-th adic test
object. -/
abbrev repBundle (s : ∀ n, Classes A (adicTest B f n)) (n : ℕ) :
    LineBundle (mumfordProduct (abelian A (adicTest B f n))).left :=
  ⟨(s n).out.obj.carrier, (s n).out.property⟩

/-- The formal system on the adic thickenings of the self-product determined by a compatible
family of classes on the adic test objects. -/
def formalSystem (s : ∀ n, Classes A (adicTest B f n))
    (hs : ∀ n, classesPullback A (adicTestTransition B f n) (s (n + 1)) = s n) :
    FormalLineBundleSystem (mumfordProduct (abelian A (Over.mk f))).hom
      (IsLocalRing.maximalIdeal B) where
  obj n := (LineBundle.pullback (adicComparison A B f n)).obj (repBundle A B f s (n + 1))
  transition n := ObjectProperty.isoMk _
    ((pullbackCompIso (adicTransition _ _ n) (adicComparison A B f (n + 1)) _ rfl _).symm ≪≫
      pullbackCompIso (adicComparison A B f n) (productMap A (adicTestTransition B f (n + 1))) _
        (adicTransition_comparison A B f n).symm _ ≪≫
      (Scheme.Modules.pullback (adicComparison A B f n)).mapIso
        (Classical.choice ((TwoAxisRigidifiedLineBundle.classesPullback_mk_eq_iff A (adicTestTransition B f (n + 1))
          (s (n + 2)).out (s (n + 1)).out).1
          (by rw [Quotient.out_eq, Quotient.out_eq]; exact hs (n + 1)))))

/-- A compatible family of classes on the adic test objects comes from a class over the base. -/
theorem exists_classesPullback_eq [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (s : ∀ n, Classes A (adicTest B f n))
    (hs : ∀ n, classesPullback A (adicTestTransition B f n) (s (n + 1)) = s n) :
    ∃ x : Classes A (Over.mk f), ∀ n, classesPullback A (adicTestBase B f n) x = s n := by
  let A' := abelian A (Over.mk f)
  obtain ⟨E, ⟨φ⟩⟩ := properFormalLineBundleEffectivity B (mumfordProduct A').left
    (mumfordProduct A').hom inferInstance (formalSystem A B f s hs)
  have key : ∀ n, classesPullback A (adicTestBase B f (n + 1))
      ⟦ofLineBundle (LineBundle.twoAxisNormalizedBundle
          Langlands.Scheme.Modules.pullbackTensorComparisonIsIso A' E)
        (LineBundle.twoAxisNormalizedBundleRigidification
          Langlands.Scheme.Modules.pullbackTensorComparisonIsIso A' E)⟧ = s (n + 1) := by
    intro n
    let h := adicTestBase B f (n + 1)
    let L := (s (n + 1)).out
    let D : LineBundle (mumfordProduct (abelian A (adicTest B f (n + 1)))).left :=
      ⟨L.obj.carrier, L.property⟩
    have hq : (adicComparisonIso A B f n).inv ≫
        adicProjection (mumfordProduct A').hom (IsLocalRing.maximalIdeal B) n =
          productMap A h := by
      rw [Iso.inv_comp_eq]
      exact (adicComparison_productMap A B f n).symm
    let c : (Scheme.Modules.pullback
        (adicProjection (mumfordProduct A').hom (IsLocalRing.maximalIdeal B) n)).obj E.obj ≅
          (Scheme.Modules.pullback (adicComparison A B f n)).obj D.obj :=
      (LineBundle.forget _).mapIso (φ.component n)
    let e : (Scheme.Modules.pullback (productMap A h)).obj E.obj ≅ D.obj :=
      pullbackCompIso (adicComparisonIso A B f n).inv _ _ hq E.obj ≪≫
        (Scheme.Modules.pullback (adicComparisonIso A B f n).inv).mapIso c ≪≫
        (pullbackCompIso (adicComparisonIso A B f n).inv (adicComparison A B f n) (𝟙 _)
          (adicComparisonIso A B f n).inv_hom_id D.obj).symm ≪≫
        (Scheme.Modules.pullbackId _).app D.obj
    rw [← Quotient.out_eq (s (n + 1)), classesPullback_mk]
    apply mk_eq_mk_of_carrierIso
    exact LineBundle.twoAxisNormalizedBundleRestrictionIso
      Langlands.Scheme.Modules.pullbackTensorComparisonIsIso A'
      (abelian A (adicTest B f (n + 1))) (productMap A h) (carrierMap A h)
      (productMap_fst A h) (productMap_snd A h) (first_naturality A h) (second_naturality A h)
      E D e L.obj.rigidification.first.symm L.obj.rigidification.second.symm
  refine ⟨⟦ofLineBundle (LineBundle.twoAxisNormalizedBundle
      Langlands.Scheme.Modules.pullbackTensorComparisonIsIso A' E)
    (LineBundle.twoAxisNormalizedBundleRigidification
      Langlands.Scheme.Modules.pullbackTensorComparisonIsIso A' E)⟧, fun n ↦ ?_⟩
  rw [← hs n, ← key n, ← classesPullback_comp, adicTestTransition_comp]

end Existence

end TwoAxisClassAdicLimits

open Langlands.AbelianScheme TwoAxisRigidifiedLineBundle TwoAxisClassAdicLimits UnramifiedFunctor in
/-- Murre's condition (F3) holds for the two-axis class presheaf of every abelian scheme over the
spectrum of a noetherian ring. -/
theorem noetherianTwoAxisClassAdicLimits : NoetherianTwoAxisClassAdicLimitsStatement.{u} := by
  intro R _ _ A B _ _ _ _ f
  refine ⟨fun x y hxy ↦ ?_, fun s hs ↦ exists_classesPullback_eq A B f s hs⟩
  induction x using Quotient.inductionOn with | h L => ?_
  induction y using Quotient.inductionOn with | h M => ?_
  apply mk_eq_mk_of_carrierIso A
  refine Classical.choice (nonempty_carrierIso_of_forall_adic A B f L M fun n ↦ ?_)
  have hn : classesPullback A (algebraOverBase f (B ⧸ IsLocalRing.maximalIdeal B ^ n)) ⟦L⟧ =
      classesPullback A (algebraOverBase f (B ⧸ IsLocalRing.maximalIdeal B ^ n)) ⟦M⟧ :=
    hxy n
  rw [classesPullback_mk, classesPullback_mk] at hn
  exact nonempty_carrierIso_of_mk_eq_mk A hn

end Langlands.AlgebraicGeometry.Picard
