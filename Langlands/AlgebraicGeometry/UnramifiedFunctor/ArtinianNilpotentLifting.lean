import Langlands.Algebra.AdicCompleteSurjection
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreGenericLiftMaps
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepReduction

/-! # Nilpotent lifting on Artinian and complete local tests -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

open GenericLift (rhom spec_comp₁₂)

variable {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v)

/-- A presheaf is infinitesimally étale on local Artinian affine tests if
restriction along every surjection with nilpotent kernel is bijective. -/
def ArtinianNilpotentBijective : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsArtinianRing A]
    (q : A →+* B), Function.Surjective q → IsNilpotent (RingHom.ker q) →
    ∀ (f : Spec (CommRingCat.of A) ⟶ S) (g : Spec (CommRingCat.of B) ⟶ S)
      (w : Spec.map (CommRingCat.ofHom q) ≫ f = g),
      Function.Bijective (F.map (rhom q w).op)

variable {F}

/-- The canonical quotient restriction on a local Artinian test. -/
theorem ArtinianNilpotentBijective.quotient (h : ArtinianNilpotentBijective F)
    {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (I : Ideal A) (hI : IsNilpotent I) (f : Spec (CommRingCat.of A) ⟶ S) :
    Function.Bijective (F.map (algebraOverBase f (A ⧸ I)).op) :=
  h A (A ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]) f _ rfl

private lemma map_op_comp {T U V : Over S} (a : T ⟶ U) (b : U ⟶ V) (x : F.obj (op V)) :
    F.map (a ≫ b).op x = F.map a.op (F.map b.op x) := by
  rw [op_comp, Functor.map_comp_apply]

private lemma ker_quotientMap_mk_of_eq {A : Type u} [CommRing A] {I J : Ideal A}
    {J' : Ideal (A ⧸ I)} (h : J' = J.map (Ideal.Quotient.mk I))
    (w : J ≤ J'.comap (Ideal.Quotient.mk I)) :
    RingHom.ker (Ideal.quotientMap J' (Ideal.Quotient.mk I) w) = I.map (Ideal.Quotient.mk J) := by
  subst J'
  exact Ideal.ker_quotientMap_mk

private abbrev truncation (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :=
  A ⧸ maximalIdeal A ^ n

private abbrev step {A : Type u} [CommRing A] [IsLocalRing A]
    (f : Spec (CommRingCat.of A) ⟶ S) (n : ℕ) :
    algebraOver f (truncation A n) ⟶ algebraOver f (truncation A (n + 1)) :=
  algHomOver f (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right n.le_succ))

private lemma step_base {A : Type u} [CommRing A] [IsLocalRing A]
    (f : Spec (CommRingCat.of A) ⟶ S) (n : ℕ) :
    step f n ≫ algebraOverBase f (truncation A (n + 1)) =
      algebraOverBase f (truncation A n) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right
    (I := maximalIdeal A) n.le_succ))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
  rfl

set_option maxHeartbeats 1200000 in
/-- Adic effectivity extends Artinian infinitesimal lifting to nilpotent
quotients of complete noetherian local rings. -/
theorem surjective_completeLocalQuotient_of_adicLimits
    (hN : ArtinianNilpotentBijective F) (hA : AdicLimits F)
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (I : Ideal A) (hI : IsNilpotent I) (f : Spec (CommRingCat.of A) ⟶ S) :
    Function.Surjective (F.map (algebraOverBase f (A ⧸ I)).op) := by
  classical
  let B := A ⧸ I
  let q : A →+* B := Ideal.Quotient.mk I
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hIproper : I ≠ ⊤ := by
    rintro rfl
    obtain ⟨n, hn⟩ := hI
    exact top_ne_bot (by simpa only [Ideal.top_pow, Ideal.zero_eq_bot] using hn)
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hIproper
  have : IsLocalRing B := IsLocalRing.of_surjective' q hq
  have : IsAdicComplete (maximalIdeal B) B :=
    Langlands.Algebra.AdicCompleteSurjection.complete_of_surjective q hq
  let b : Spec (CommRingCat.of B) ⟶ S := Spec.map (CommRingCat.ofHom q) ≫ f
  have hm (n : ℕ) : (maximalIdeal A ^ n).map q = maximalIdeal B ^ n := by
    rw [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective q hq]
  let qₙ (n : ℕ) : truncation A n →+* truncation B n :=
    Ideal.quotientMap (maximalIdeal B ^ n) q (Ideal.map_le_iff_le_comap.mp (hm n).le)
  have hqₙ (n : ℕ) : Function.Surjective (qₙ n) := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, rfl⟩ := hq x
    exact ⟨Ideal.Quotient.mk _ a, Ideal.quotientMap_mk⟩
  have hnil (n : ℕ) : IsNilpotent (RingHom.ker (qₙ n)) := by
    change IsNilpotent (RingHom.ker (Ideal.quotientMap _ _ _))
    rw [ker_quotientMap_mk_of_eq (hm n).symm]
    obtain ⟨r, hr⟩ := hI
    exact ⟨r, by simp only [← Ideal.map_pow, hr, Ideal.zero_eq_bot, Ideal.map_bot]⟩
  let d (n : ℕ) : algebraOver b (truncation B n) ⟶ algebraOver f (truncation A n) :=
    rhom (qₙ n) (spec_comp₁₂ (Ideal.quotientMap_comp_mk _))
  have hbase (n : ℕ) :
      d n ≫ algebraOverBase f (truncation A n) =
      algebraOverBase b (truncation B n) ≫ algebraOverBase f B := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (qₙ n)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ n))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal B ^ n))) ≫
        Spec.map (CommRingCat.ofHom q)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]
  have hstep (n : ℕ) : step b n ≫ d (n + 1) = d n ≫ step f n := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := maximalIdeal B) n.le_succ))) ≫
        Spec.map (CommRingCat.ofHom (qₙ (n + 1))) =
      Spec.map (CommRingCat.ofHom (qₙ n)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := maximalIdeal A) n.le_succ)))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    rfl
  have hbij (n : ℕ) : Function.Bijective (F.map (d n).op) := by
    cases n with
    | zero =>
      have : Subsingleton (truncation A 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
      have : IsIso (CommRingCat.ofHom (qₙ 0)) := (ConcreteCategory.isIso_iff_bijective _).mpr
        ⟨Function.injective_of_subsingleton _, hqₙ 0⟩
      have : IsIso ((Over.forget S).map (d 0)) := by
        change IsIso (Spec.map (CommRingCat.ofHom (qₙ 0)))
        infer_instance
      have : IsIso (d 0) := isIso_of_reflects_iso (d 0) (Over.forget S)
      exact (isIso_iff_bijective _).mp inferInstance
    | succ n =>
      have hproper : maximalIdeal A ^ (n + 1) ≠ ⊤ := ne_top_of_le_ne_top
        (maximalIdeal.isMaximal A).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero n))
      have : Nontrivial (truncation A (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr hproper
      have : IsLocalRing (truncation A (n + 1)) := IsLocalRing.of_surjective'
        (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) Ideal.Quotient.mk_surjective
      have : IsArtinianRing (truncation A (n + 1)) :=
        isArtinianRing_quotient_maximalIdeal_pow A n
      exact hN _ _ (qₙ (n + 1)) (hqₙ _) (hnil _) _ _ _
  intro x
  choose z hz using fun n => (hbij n).2 (F.map (algebraOverBase b (truncation B n)).op x)
  have hc (n : ℕ) : F.map (step f n).op (z (n + 1)) = z n := by
    apply (hbij n).1
    rw [← map_op_comp, ← hstep, map_op_comp, hz (n + 1), ← map_op_comp, step_base, hz n]
  obtain ⟨y, hy⟩ := (hA A f).2 z hc
  refine ⟨y, (hA B b).1 _ _ fun n => ?_⟩
  change F.map (algebraOverBase b (truncation B n)).op
      (F.map (algebraOverBase f B).op y) = _
  calc
    _ = F.map (algebraOverBase b (truncation B n) ≫ algebraOverBase f B).op y :=
      (map_op_comp _ _ _).symm
    _ = F.map (d n ≫ algebraOverBase f (truncation A n)).op y :=
      congrArg (fun a : algebraOver b (truncation B n) ⟶ Over.mk f => F.map a.op y) (hbase n).symm
    _ = F.map (d n).op (F.map (algebraOverBase f (truncation A n)).op y) :=
      map_op_comp _ _ _
    _ = _ := (congrArg (fun a => F.map (d n).op a) (hy n)).trans (hz n)

end Langlands.AlgebraicGeometry.UnramifiedFunctor
