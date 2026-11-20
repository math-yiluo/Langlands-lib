import Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.Completion
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreArtinianDetectionLimits
import Langlands.AlgebraicGeometry.Deformation.AdicCompletionNoetherian
import Langlands.CommutativeAlgebra.MaximalLocalizationCompletion

/-! # Artinian detection of a representing scheme -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

universe u v

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace ArtinianDetection

open ChartGluing Charts

section ArbitraryBase

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
  {U : Over S} (ξ : F.obj (op U))

private lemma injective_of_iso {T T' : Over S} (e : T ≅ T')
    (h : Function.Injective fun g : T' ⟶ U ↦ F.map g.op ξ) :
    Function.Injective fun g : T ⟶ U ↦ F.map g.op ξ := by
  intro a b hab
  have he : e.inv ≫ a = e.inv ≫ b := h (by
    simpa only [op_comp, Functor.map_comp_apply] using congrArg (F.map e.inv.op) hab)
  exact (cancel_epi e.inv).mp he

private lemma surjective_of_iso {T T' : Over S} (e : T ≅ T')
    (h : Function.Surjective fun g : T' ⟶ U ↦ F.map g.op ξ) :
    Function.Surjective fun g : T ⟶ U ↦ F.map g.op ξ := by
  intro x
  obtain ⟨a, ha⟩ := h (F.map e.inv.op x)
  change F.map a.op ξ = F.map e.inv.op x at ha
  refine ⟨e.hom ≫ a, ?_⟩
  change F.map (e.hom ≫ a).op ξ = x
  rw [op_comp, Functor.map_comp_apply, ha, ← Functor.map_comp_apply, ← op_comp]
  simp

private abbrev AdicQuotient (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :=
  R ⧸ maximalIdeal R ^ (n + 1)

private abbrev LocalCompletion (R : Type u) [CommRing R] [IsLocalRing R] :=
  AdicCompletion (maximalIdeal R) R

section Complete

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R] (f : Spec (CommRingCat.of R) ⟶ S)

private lemma bijective_of_complete (hA : AdicLimits F)
    (hquot : ∀ n, Function.Bijective
      fun g : algebraOver f (AdicQuotient R n) ⟶ U ↦ F.map g.op ξ) :
    Function.Bijective fun g : Over.mk f ⟶ U ↦ F.map g.op ξ := by
  constructor
  · intro a b hab
    apply Over.OverMorphism.ext
    apply specMap_adic_ext
    intro n
    have he : algebraOverBase f (AdicQuotient R n) ≫ a =
        algebraOverBase f (AdicQuotient R n) ≫ b := (hquot n).1 (by
      simpa only [op_comp, Functor.map_comp_apply] using
        congrArg (F.map (algebraOverBase f (AdicQuotient R n)).op) hab)
    exact congrArg CommaMorphism.left he
  · intro η
    choose a ha using fun n ↦ (hquot n).2 (F.map (algebraOverBase f (AdicQuotient R n)).op η)
    change ∀ n, F.map (a n).op ξ = F.map (algebraOverBase f (AdicQuotient R n)).op η at ha
    have hcompat (n : ℕ) : algHomOver f (Ideal.Quotient.factorₐ R
        (Ideal.pow_le_pow_right (I := maximalIdeal R) (n + 1).le_succ)) ≫ a (n + 1) = a n := by
      apply (hquot n).1
      change F.map (_ ≫ a (n + 1)).op ξ = F.map (a n).op ξ
      rw [op_comp, Functor.map_comp_apply, ha, ha, ← Functor.map_comp_apply, ← op_comp,
        algHomOver_comp_algebraOverBase]
    obtain ⟨g, hg⟩ := exists_specMap_adic_lift (fun n ↦ (a n).left)
      (fun n ↦ congrArg CommaMorphism.left (hcompat n))
    have hw : g ≫ U.hom = f := by
      apply specMap_adic_ext
      intro n
      rw [← Category.assoc, hg n, Over.w (a n)]
      rfl
    let G : Over.mk f ⟶ U := Over.homMk g hw
    refine ⟨G, (hA R f).1 _ _ ?_⟩
    have hpositive (n : ℕ) : F.map (algebraOverBase f (AdicQuotient R n)).op (F.map G.op ξ) =
        F.map (algebraOverBase f (AdicQuotient R n)).op η := by
      have he : algebraOverBase f (AdicQuotient R n) ≫ G = a n :=
        Over.OverMorphism.ext (hg n)
      rw [← Functor.map_comp_apply, ← op_comp, he, ha]
    intro n
    cases n with
    | zero =>
      rw [← algHomOver_comp_algebraOverBase f (Ideal.Quotient.factorₐ R
        (Ideal.pow_le_pow_right (I := maximalIdeal R) (Nat.zero_le 1))), op_comp,
        Functor.map_comp_apply, Functor.map_comp_apply, hpositive 0]
    | succ n => exact hpositive n

end Complete

end ArbitraryBase

private lemma isArtinianRing_adicQuotient (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (n : ℕ) : IsArtinianRing (AdicQuotient R n) := by
  have : IsNoetherianRing (AdicQuotient R n) :=
    isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  apply (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr
  refine ⟨n + 1, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
  exact Ideal.map_mk_eq_bot_of_le le_rfl

section MaximalStalk

open Langlands.CommutativeAlgebra.MaximalLocalizationCompletion

variable {B : Type u} [CommRing B] (m : Ideal B) [m.IsMaximal]

private abbrev maximalPoint : PrimeSpectrum B := ⟨m, inferInstance⟩

private abbrev maximalCompletion := LocalCompletion (Localization.AtPrime m)

private def completedStalkMap : Spec (CommRingCat.of (maximalCompletion m)) ⟶
    Spec ((Spec (CommRingCat.of B)).presheaf.stalk (maximalPoint m)) :=
  completionMap (CommRingCat.of (Localization.AtPrime m)) ≫
    Spec.map (Spec.stalkIso (CommRingCat.of B) (maximalPoint m)).hom

set_option backward.isDefEq.respectTransparency false in
private lemma completedStalkMap_fromSpecStalk :
    completedStalkMap m ≫ (Spec (CommRingCat.of B)).fromSpecStalk (maximalPoint m) =
      Spec.map (CommRingCat.ofHom (algebraMap B (maximalCompletion m))) := by
  rw [completedStalkMap, Spec.fromSpecStalk_eq', completionMap, ← Spec.map_comp,
    ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  exact congrArg (algebraMap (Localization.AtPrime m) (maximalCompletion m))
    ((StructureSheaf.stalkIso (CommRingCat.of B) (maximalPoint m)).symm.commutes b)

variable [IsNoetherianRing B]

private instance : Flat (completedStalkMap m) := by
  rw [completedStalkMap]
  infer_instance

private instance : Surjective (completedStalkMap m) := by
  rw [completedStalkMap]
  infer_instance

private instance : QuasiCompact (completedStalkMap m) := by
  rw [completedStalkMap]
  infer_instance

variable (A : CommRingCat.{u}) [Algebra A B]

private abbrev completedStalkOver : Over (Spec A) :=
  Over.mk (completedStalkMap m ≫ (stalkPt (ovR A B) (maximalPoint m)).left ≫ (ovR A B).hom)

private def completedStalkOverHom :
    completedStalkOver m A ⟶ Over.mk ((ovR A B).left.fromSpecStalk (maximalPoint m) ≫
      (ovR A B).hom) :=
  Over.homMk (completedStalkMap m)

variable {F : (Over (Spec A))ᵒᵖ ⥤ Type v} {U : Over (Spec A)} (ξ : F.obj (op U))
  [Algebra.FiniteType A B]

private lemma bijective_of_completedStalk (hA : AdicLimits F)
    (htest : ∀ (Q : Type u) [CommRing Q] [Algebra A Q] [IsLocalRing Q] [IsArtinianRing Q]
      [Algebra.QuasiFinite A Q],
      Function.Bijective fun g : algebraOver (𝟙 (Spec A)) Q ⟶ U ↦ F.map g.op ξ) :
    Function.Bijective fun g : completedStalkOver m A ⟶ U ↦ F.map g.op ξ := by
  let R := Localization.AtPrime m
  let C := maximalCompletion m
  let : IsAdicComplete (maximalIdeal C) C := by
    change IsAdicComplete (maximalIdeal (LocalCompletion R)) (LocalCompletion R)
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact AdicCompletion.isAdicComplete_self _ (maximalIdeal R).fg_of_isNoetherianRing
  let f : Spec (CommRingCat.of C) ⟶ Spec A := (completedStalkOver m A).hom
  change Function.Bijective fun g : Over.mk f ⟶ U ↦ F.map g.op ξ
  apply bijective_of_complete ξ (R := C) f hA
  intro n
  let Q := AdicQuotient C n
  let φ : B →+* Q := (Ideal.Quotient.mk _).comp (algebraMap B C)
  let : Algebra A Q := (φ.comp (algebraMap A B)).toAlgebra
  let ψ : B →ₐ[A] Q := { toRingHom := φ, commutes' := fun _ ↦ rfl }
  have hsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, hb⟩ := exists_sub_algebraMap_mem_pow_completion m c (n + 1)
    exact ⟨b, (Ideal.Quotient.eq.mpr hb).symm⟩
  let : Algebra.FiniteType A Q := Algebra.FiniteType.of_surjective ψ hsurj
  let : Subsingleton (PrimeSpectrum Q) := ⟨eq_of_quotient_pow n⟩
  let : Algebra.QuasiFinite A Q :=
    Algebra.QuasiFinite.iff_finite_comap_preimage_singleton.mpr fun _ ↦ Set.toFinite _
  let : IsArtinianRing Q := isArtinianRing_adicQuotient C n
  let e : algebraOver f Q ≅ algebraOver (𝟙 (Spec A)) Q := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap A Q)) ≫ 𝟙 _) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫
        completedStalkMap m ≫ (Spec (CommRingCat.of B)).fromSpecStalk (maximalPoint m) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A B))
    rw [Category.id_comp, Category.comp_id, ← Category.assoc (completedStalkMap m),
      completedStalkMap_fromSpecStalk, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp])
  exact ⟨injective_of_iso ξ e (htest Q).1, surjective_of_iso ξ e (htest Q).2⟩

variable (hA : AdicLimits F)
  (htest : ∀ (Q : Type u) [CommRing Q] [Algebra A Q] [IsLocalRing Q] [IsArtinianRing Q]
    [Algebra.QuasiFinite A Q],
    Function.Bijective fun g : algebraOver (𝟙 (Spec A)) Q ⟶ U ↦ F.map g.op ξ)

include hA htest

private lemma injective_at_maximalStalk :
    Function.Injective fun g : Over.mk ((ovR A B).left.fromSpecStalk (maximalPoint m) ≫
      (ovR A B).hom) ⟶ U ↦ F.map g.op ξ := by
  intro a b hab
  let φ := completedStalkOverHom m A
  have he : φ ≫ a = φ ≫ b := (bijective_of_completedStalk m A ξ hA htest).1 (by
    simpa only [op_comp, Functor.map_comp_apply] using congrArg (F.map φ.op) hab)
  have : Epi φ.left := inferInstanceAs (Epi (completedStalkMap m))
  exact Over.OverMorphism.ext ((cancel_epi φ.left).mp (congrArg CommaMorphism.left he))

private lemma fac_at_maximalStalk (hmono : IsMonoElement F ξ) (hF : FaithfullyFlatSheaf F)
    (η : F.obj (op (ovR A B))) : Fac ξ η (stalkPt (ovR A B) (maximalPoint m)) := by
  let φ := completedStalkOverHom m A
  have : Flat φ.left := inferInstanceAs (Flat (completedStalkMap m))
  have : Surjective φ.left := inferInstanceAs (Surjective (completedStalkMap m))
  have : QuasiCompact φ.left := inferInstanceAs (QuasiCompact (completedStalkMap m))
  apply fac_of_flat hmono hF φ
  exact (bijective_of_completedStalk m A ξ hA htest).2 _

end MaximalStalk

section Covers

private lemma exists_open_of_maximal {B : Type u} [CommRing B]
    (P : (Spec (CommRingCat.of B)).Opens → Prop)
    (h : ∀ (m : Ideal B) [m.IsMaximal], ∃ V, maximalPoint m ∈ V ∧ P V)
    (t : Spec (CommRingCat.of B)) : ∃ V, t ∈ V ∧ P V := by
  obtain ⟨m, hm, htm⟩ := t.asIdeal.exists_le_maximal t.2.1
  obtain ⟨V, hV, hP⟩ := h m
  have hs : t ⤳ (maximalPoint m : Spec (CommRingCat.of B)) :=
    (PrimeSpectrum.le_iff_specializes t (maximalPoint m)).mp htm
  exact ⟨V, hs.mem_open V.isOpen hV, hP⟩

private lemma hom_eq_of_forall_opens {S : Scheme.{u}} {T U : Over S}
    {a b : T ⟶ U}
    (h : ∀ t : T.left, ∃ V : T.left.Opens, t ∈ V ∧ ιOver T V ≫ a = ιOver T V ≫ b) :
    a = b := by
  choose V hV he using h
  let 𝒰 : T.left.OpenCover := Scheme.Cover.mkOfCovers T.left
    (fun t ↦ (V t : Scheme.{u})) (fun t ↦ (V t).ι)
    (fun t ↦ ⟨t, ⟨t, hV t⟩, rfl⟩)
  exact Over.OverMorphism.ext (𝒰.hom_ext _ _ fun t ↦ congrArg CommaMorphism.left (he t))

variable {A : CommRingCat.{u}} {F : (Over (Spec A))ᵒᵖ ⥤ Type v} {U : Over (Spec A)}
  (ξ : F.obj (op U))

private lemma of_affine_tests (P : Over (Spec A) → Prop)
    (hiso : ∀ {T T' : Over (Spec A)}, (T ≅ T') → P T' → P T)
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B], P (ovR A B))
    (T : Over (Spec A)) [IsAffine T.left] : P T := by
  let f := Spec.preimage (T.left.isoSpec.inv ≫ T.hom)
  let : Algebra A Γ(T.left, ⊤) := f.hom.toAlgebra
  have e : T ≅ ovR A Γ(T.left, ⊤) := Over.isoMk T.left.isoSpec (by
    change T.left.isoSpec.hom ≫ Spec.map f = T.hom
    rw [Spec.map_preimage, Iso.hom_inv_id_assoc])
  exact hiso e (h _)

private lemma injective_of_affine_tests
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B],
      Function.Injective fun g : ovR A B ⟶ U ↦ F.map g.op ξ) :
    IsMonoElement F ξ := by
  intro T a b hab
  let 𝒰 := T.left.affineCover
  apply Over.OverMorphism.ext
  refine 𝒰.hom_ext _ _ fun i ↦ ?_
  let aᵢ : Over.mk (𝒰.f i ≫ T.hom) ⟶ T := Over.homMk (𝒰.f i)
  let : IsAffine (Over.mk (𝒰.f i ≫ T.hom)).left :=
    inferInstanceAs (IsAffine (T.left.affineCover.X i))
  have hinj := of_affine_tests (fun V ↦ Function.Injective fun g : V ⟶ U ↦ F.map g.op ξ)
    (fun e ↦ injective_of_iso ξ e) h (Over.mk (𝒰.f i ≫ T.hom))
  have he : aᵢ ≫ a = aᵢ ≫ b := hinj (by
    simpa only [op_comp, Functor.map_comp_apply] using congrArg (F.map aᵢ.op) hab)
  exact congrArg CommaMorphism.left he

private lemma surjective_of_affine_tests (hmono : IsMonoElement F ξ) (hZ : ZariskiSheaf F)
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B],
      Function.Surjective fun g : ovR A B ⟶ U ↦ F.map g.op ξ)
    (T : Over (Spec A)) :
    Function.Surjective fun g : T ⟶ U ↦ F.map g.op ξ := by
  intro η
  have hfac : Fac ξ η (𝟙 T) := by
    let 𝒰 := T.left.affineCover
    apply fac_of_openCover hmono hZ (𝟙 T) 𝒰
    intro i
    let : IsAffine (Over.mk (𝒰.f i ≫ T.hom)).left :=
      inferInstanceAs (IsAffine (T.left.affineCover.X i))
    exact of_affine_tests (fun V ↦ Function.Surjective fun g : V ⟶ U ↦ F.map g.op ξ)
      (fun e ↦ surjective_of_iso ξ e) h (Over.mk (𝒰.f i ≫ T.hom)) _
  obtain ⟨g, hg⟩ := hfac
  change F.map g.op ξ = F.map (𝟙 T).op η at hg
  rw [op_id, F.map_id] at hg
  exact ⟨g, hg⟩

end Covers

end ArtinianDetection

open ArtinianDetection ChartGluing Charts

/-- Murre's Lemma 1 for the comparison from a scheme locally of finite type. -/
theorem murreArtinianDetection : MurreArtinianDetectionStatement.{u, v} := by
  intro A _ F hZ hF h2 hA Y q hq ξ htest
  let : LocallyOfFiniteType (Over.mk q : Over (Spec A)).hom := hq
  let : LocallyOfFinitePresentation (Over.mk q : Over (Spec A)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation q)
  have hInjective (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B] :
      Function.Injective fun g : ovR A B ⟶ Over.mk q ↦ F.map g.op ξ := by
    let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
    intro a b hab
    apply hom_eq_of_forall_opens
    apply exists_open_of_maximal
      (fun V ↦ ιOver (ovR A B) V ≫ a = ιOver (ovR A B) V ≫ b)
    intro m _
    let : (ovR A B).left.IsGermInjectiveAt (maximalPoint m) :=
      (inferInstance : (Spec (CommRingCat.of B)).IsGermInjective) (maximalPoint m)
    apply exists_open_agreement (T := ovR A B) (maximalPoint m)
    apply injective_at_maximalStalk m A ξ hA htest
    simpa only [op_comp, Functor.map_comp_apply] using
      congrArg (F.map (stalkPt (ovR A B) (maximalPoint m)).op) hab
  have hmono : IsMonoElement F ξ := injective_of_affine_tests ξ (affineInjective h2 hInjective)
  have hSurjective (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B] :
      Function.Surjective fun g : ovR A B ⟶ Over.mk q ↦ F.map g.op ξ := by
    let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
    intro η
    have hfac : Fac ξ η (𝟙 (ovR A B)) := by
      apply fac_of_forall_opens hmono hZ (𝟙 (ovR A B))
      apply exists_open_of_maximal (fun V ↦ Fac ξ η (ιOver (ovR A B) V ≫ 𝟙 (ovR A B)))
      intro m _
      let : (ovR A B).left.IsGermInjectiveAt (maximalPoint m) :=
        (inferInstance : (Spec (CommRingCat.of B)).IsGermInjective) (maximalPoint m)
      obtain ⟨V, hmV, hV⟩ := exists_open_factorization hZ h2 η (maximalPoint m)
        (fac_at_maximalStalk m A ξ hA htest hmono hF η)
      exact ⟨V, hmV, by simpa only [Category.comp_id] using hV⟩
    obtain ⟨g, hg⟩ := hfac
    change F.map g.op ξ = F.map (𝟙 (ovR A B)).op η at hg
    rw [op_id, F.map_id] at hg
    exact ⟨g, hg⟩
  intro T
  exact ⟨@hmono T, surjective_of_affine_tests ξ hmono hZ (affineSurjective h2 hSurjective) T⟩

end Langlands.AlgebraicGeometry.UnramifiedFunctor
