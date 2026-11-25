/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.CategoryTheory.Principal.PrincipalPowerQuotients
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralScalarRegular
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralProjectionDivisibility
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt

/-! # Regular scalars and finite quotients of completed coefficients

Source: blueprint, chap-Smooth-purity, proposition-sp-integral-towers proof, first paragraph,
and coefficient setup in prose-09-21; Stacks Tags 00WK and 00YR.
(blueprint: lem-sp-completed-coefficient-regular-quotients).

Natural level n denotes exponent n+1. The commutative-ring objects below retain the
underlying ring sheaves of the recorded coefficient towers. Quotients are the existing
sheafifications of sectionwise principal-power quotients.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

/-- A constant integral scalar as a compatible section of the actual completed ring.
Source: blueprint, coefficient setup, constant scalar convention
(blueprint: lem-sp-completed-coefficient-regular-quotients). -/
def spCompletedScalarSection (a : Padic.coefficientExtensionIntegers l E) :
    ((completedIntegralCommRingSheafUnrestricted l E T).obj ⋙
      forget CommRingCat.{max u (t + 1)}).sections :=
  (Functor.sectionsFunctor T.ProEtᵒᵖ).map
    (Functor.whiskerRight (integralConstantToCompletionOfUniverses l E T).hom
      (forget RingCat.{max u (t + 1)}))
    ((Functor.sectionsFunctor T.ProEtᵒᵖ).map
      (Functor.whiskerRight (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))))
        (forget CommRingCat.{max u (t + 1)}))
      ⟨fun _ ↦ ULift.up a, fun _ ↦ rfl⟩)

/-- The recorded ell-power constant coefficient sheaf, retaining commutativity.
Source: blueprint, coefficient towers, R_(n+1)
(blueprint: lem-sp-completed-coefficient-regular-quotients). -/
def spEllCommRingSheaf (n : ℕ) :
    Sheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)} :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))

/-- The actual ell-power projection, from the uniquely normalized tower comparison.
Source: blueprint, coefficient towers, completed-coefficient comparison
(blueprint: lem-sp-completed-coefficient-regular-quotients). -/
def spCompletedEllCommRingProjection (n : ℕ) :
    completedIntegralCommRingSheafUnrestricted l E T ⟶ spEllCommRingSheaf l E T n where
  hom :=
    { app := fun U ↦
        letI := completedIntegralCoefficientCommRingUnrestricted l E T U
        CommRingCat.ofHom
          ((((sp_completed_coefficient_limit l E T).choose.hom ≫
          limit.π (spCoefficientRings l E T) (op n)).hom.app U).hom)
      naturality := fun _ _ f ↦ (forget₂ CommRingCat RingCat).map_injective
        (((sp_completed_coefficient_limit l E T).choose.hom ≫
          limit.π (spCoefficientRings l E T) (op n)).hom.naturality f) }

/-- Every uniformizer quotient transition, induced by the identity on integers.
Source: blueprint, finite coefficient reductions
(blueprint: lem-sp-completed-coefficient-regular-quotients). -/
def spUniformizerQuotientTransition {m n : ℕ} (h : m ≤ n) :
    integralCoefficientCommRingSheaf l E T n ⟶ integralCoefficientCommRingSheaf l E T m :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom (RingHom.ulift
      (Ideal.Quotient.factorPow (Ideal.span {Padic.coefficientExtensionUniformizer l E})
        (Nat.add_le_add_right h 1))))

/-- Every ell-power quotient transition, induced by the identity on integers.
Source: blueprint, coefficient towers, quotient reductions
(blueprint: lem-sp-completed-coefficient-regular-quotients). -/
def spEllQuotientTransition {m n : ℕ} (h : m ≤ n) :
    spEllCommRingSheaf l E T n ⟶ spEllCommRingSheaf l E T m :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom (RingHom.ulift
      (Ideal.Quotient.factorPow (spEllIdeal l E) (Nat.add_le_add_right h 1))))

private theorem constRing_surj {C : Type*} [Category* C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{u}]
    [HasSheafify J (Type u)] [J.PreservesSheafification (forget CommRingCat.{u})]
    [J.HasSheafCompose (forget CommRingCat.{u})]
    {A B : CommRingCat.{u}} (f : A ⟶ B) (hf : Function.Surjective f)
    (U : Cᵒᵖ) :
    Function.Surjective (((constantSheaf J CommRingCat.{u}).map f).hom.app U) := by
  classical
  let e := constantCommuteCompose J (forget CommRingCat.{u})
  let s' := (constantSheaf J (Type u)).map (TypeCat.ofHom (Function.surjInv hf))
  have hs : s' ≫ (constantSheaf J (Type u)).map ((forget _).map f) = 𝟙 _ := by
    rw [← Functor.map_comp]
    trans (constantSheaf J (Type u)).map (𝟙 ((forget CommRingCat.{u}).obj B))
    · congr 1
      ext x
      exact Function.surjInv_eq hf x
    exact (constantSheaf J (Type u)).map_id _
  let r := e.hom.app B ≫ s' ≫ e.inv.app A
  have hr : r ≫ (sheafCompose J (forget CommRingCat.{u})).map
      ((constantSheaf J CommRingCat.{u}).map f) = 𝟙 _ := by
    dsimp only [r]
    rw [Category.assoc, Category.assoc]
    change e.hom.app B ≫ s' ≫ e.inv.app A ≫
      (constantSheaf J CommRingCat.{u} ⋙ sheafCompose J (forget CommRingCat.{u})).map f = _
    rw [← e.inv.naturality f]
    change e.hom.app B ≫ s' ≫
      (constantSheaf J (Type u)).map ((forget _).map f) ≫ e.inv.app B = _
    rw [← Category.assoc s', hs, Category.id_comp, e.hom_inv_id_app B]
  intro x
  refine ⟨r.hom.app U x, ?_⟩
  exact congrArg (fun h ↦ h.hom.app U x) hr

private def scalarHom (U : T.ProEtᵒᵖ) :
    Padic.coefficientExtensionIntegers l E →+*
      (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U :=
  ((integralConstantToCompletionOfUniverses l E T).hom.app U).hom.comp
    (((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U).hom.comp
      ULift.ringEquiv.symm.toRingHom)

private theorem ell_factor : ∃ e : ℕ, 1 ≤ e ∧
    ∃ v : (Padic.coefficientExtensionIntegers l E)ˣ,
      (l : Padic.coefficientExtensionIntegers l E) =
        v * Padic.coefficientExtensionUniformizer l E ^ e := by
  let O := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsDiscreteValuationRing O := h.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({π} : Set O) = Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal l E = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
  have hπ : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 (hm.symm.trans hgen.symm)
  have hl0 : (l : O) ≠ 0 := by
    intro heq
    have heq' : (l : E) = 0 := congrArg (fun x : O ↦ (x : E)) heq
    have hq : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    exact hq ((algebraMap ℚ_[l] E).injective (by simpa only [map_natCast, map_zero]
      using heq'))
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hπ
  refine ⟨e, ?_, v, hv⟩
  have hval : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    have hext := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
    change spectralNorm ℚ_[l] E (l : E) < 1
    simpa only [map_natCast] using hext.trans_lt (Padic.norm_p_lt_one (p := l))
  have hnu : ¬ IsUnit (l : O) := by
    intro hu
    exact (ne_of_lt hval) ((h.2.2.1 (l : O)).mp hu)
  by_contra he
  have he0 : e = 0 := by omega
  apply hnu
  rw [hv, he0, pow_zero, mul_one]
  exact v.isUnit

private abbrev constO :=
  (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))

private def constMap : constO l E T ⟶ completedIntegralCommRingSheafUnrestricted l E T where
  hom :=
    { app U :=
        letI := completedIntegralCoefficientCommRingUnrestricted l E T U
        CommRingCat.ofHom ((integralConstantToCompletionOfUniverses l E T).hom.app U).hom
      naturality := by
        intro U V f
        apply (forget₂ CommRingCat RingCat).map_injective
        exact (integralConstantToCompletionOfUniverses l E T).hom.naturality f }

private def constQuot (I : Ideal (Padic.coefficientExtensionIntegers l E)) :
    constO l E T ⟶ (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))) :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I)))

private theorem uniformizer_normalized (n : ℕ) :
    constMap l E T ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
      constQuot l E T (Padic.coefficientExtensionIdeal l E (n + 1)) := by
  ext U x
  exact congrArg (fun h ↦ h.hom.app U x)
    (limit.lift_π (integralConstantConeOfUniverses l E T) (op n))

private theorem ell_normalized (n : ℕ) :
    constMap l E T ≫ spCompletedEllCommRingProjection l E T n =
      constQuot l E T (spEllIdeal l E ^ (n + 1)) := by
  ext U x
  exact congrArg (fun h ↦ h.hom.app U x)
    ((sp_completed_coefficient_limit l E T).choose_spec.1 n)

private theorem projection_scalar {I : Ideal (Padic.coefficientExtensionIntegers l E)}
    (p : completedIntegralCommRingSheafUnrestricted l E T ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))
    (hp : constMap l E T ≫ p = constQuot l E T I)
    (U : T.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) :
    (p.hom.app U) (scalarHom l E T U a) =
      (toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))).app U
          (ULift.up (Ideal.Quotient.mk I a)) := by
  have hc := congrArg (fun h ↦ h.hom.app U
    ((toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
        (ULift.up a))) hp
  let φ : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I)) :=
    CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I))
  have hn := congrArg (fun h ↦ h.app U (ULift.up a))
    (toSheafify_naturality (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).map φ))
  exact hc.trans hn.symm

private theorem projection_surjective {I : Ideal (Padic.coefficientExtensionIntegers l E)}
    (p : completedIntegralCommRingSheafUnrestricted l E T ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))
    (hp : constMap l E T ≫ p = constQuot l E T I) (U : T.ProEtᵒᵖ) :
    Function.Surjective (p.hom.app U) := by
  have : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf _
  have hs : Function.Surjective ((constQuot l E T I).hom.app U) := by
    let φ : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
        CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I)) :=
      CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk I))
    have hsφ : Function.Surjective φ := by
      intro b
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b.down
      exact ⟨ULift.up a, ULift.ext ha⟩
    exact constRing_surj (Scheme.ProEt.topology T) φ hsφ U
  intro x
  obtain ⟨a, ha⟩ := hs x
  exact ⟨(constMap l E T).hom.app U a,
    (congrArg (fun h ↦ h.hom.app U a) hp).trans ha⟩

private theorem scalar_killed {I : Ideal (Padic.coefficientExtensionIntegers l E)}
    (p : completedIntegralCommRingSheafUnrestricted l E T ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))
    (hp : constMap l E T ≫ p = constQuot l E T I)
    (U : T.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) (m : ℕ)
    (ha : a ^ m ∈ I) : (p.hom.app U) (scalarHom l E T U a ^ m) = 0 := by
  rw [← map_pow, projection_scalar l E T p hp]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact map_zero _

private theorem uniformizer_kernel (n : ℕ) (U : T.ProEtᵒᵖ) :
    RingHom.ker ((completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U).hom =
      sectionPowerIdeal (completedIntegralCommRingSheafUnrestricted l E T)
        (spCompletedScalarSection l E T (Padic.coefficientExtensionUniformizer l E))
        (n + 1) U := by
  ext x
  change _ = 0 ↔ x ∈ Ideal.span
    {scalarHom l E T U (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)}
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := completedIntegralProjection_divisible l E T n U x hx
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have hz := scalar_killed l E T _ (uniformizer_normalized l E T n) U
      (Padic.coefficientExtensionUniformizer l E) (n + 1)
      (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) (n + 1))
    change ((completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U).hom
      (scalarHom l E T U (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)) = 0 at hz
    rw [map_mul, hz, zero_mul]

private theorem normalized_ext {I : Ideal (Padic.coefficientExtensionIntegers l E)}
    (hI : ∃ k : ℕ, Padic.coefficientExtensionIdeal l E (k + 1) ≤ I)
    (f g : completedIntegralCommRingSheafUnrestricted l E T ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))
    (hf : constMap l E T ≫ f = constQuot l E T I)
    (hg : constMap l E T ≫ g = constQuot l E T I) : f = g := by
  let F := sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  have h := completedIntegralFiniteQuotientHom_ext l E T I hI (F.map f) (F.map g)
    (congrArg F.map hf) (congrArg F.map hg)
  ext U x
  exact congrArg (fun h ↦ h.hom.app U x) h

private theorem normalized_kernel (n : ℕ)
    (I : Ideal (Padic.coefficientExtensionIntegers l E))
    (hI : I = Padic.coefficientExtensionIdeal l E (n + 1))
    (p : completedIntegralCommRingSheafUnrestricted l E T ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))))
    (hp : constMap l E T ≫ p = constQuot l E T I) (U : T.ProEtᵒᵖ) :
    RingHom.ker (p.hom.app U).hom =
      Ideal.span {scalarHom l E T U (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)} := by
  subst I
  have he := normalized_ext l E T ⟨n, le_rfl⟩ p
    (completedIntegralCommRingProjectionUnrestricted l E T n) hp
    (uniformizer_normalized l E T n)
  rw [he]
  exact uniformizer_kernel l E T n U

private theorem sheaf_epi {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R H : Sheaf J CommRingCat.{u}} (p : R ⟶ H)
    (hs : ∀ U, Function.Surjective (p.hom.app U)) : Epi p where
  left_cancellation f g h := by
    ext U x
    obtain ⟨x, rfl⟩ := hs U x
    exact congrArg (fun h ↦ h.hom.app U x) h

private theorem quotient_iso {C : Type t} [Category C]
    {J : GrothendieckTopology C} [HasSheafify J CommRingCat.{u}]
    (R H : Sheaf J CommRingCat.{u})
    (a : (R.obj ⋙ forget CommRingCat.{u}).sections) (n : ℕ) (p : R ⟶ H)
    (hs : ∀ U, Function.Surjective (p.hom.app U))
    (hk : ∀ U, RingHom.ker (p.hom.app U).hom = sectionPowerIdeal R a n U) :
    ∃ e : principalPowerRingQuotient R a n ≅ H,
      principalPowerRingProjection R a n ≫ e.hom = p := by
  let q : sectionPowerQuotientPresheaf R a n ⟶ H.obj :=
    { app U := CommRingCat.ofHom (Ideal.Quotient.lift _ (p.hom.app U).hom
        (by intro x hx; exact (show x ∈ RingHom.ker (p.hom.app U).hom by rwa [hk U])))
      naturality := by
        intro U V f
        ext x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact congrArg (fun h ↦ h x) (p.hom.naturality f) }
  have hq : sectionPowerQuotientProjection R a n ≫ q = p.hom := by
    ext U x
    rfl
  have hi : IsIso q := by
    have : ∀ U, IsIso (q.app U) := by
      intro U
      apply (ConcreteCategory.isIso_iff_bijective _).2
      constructor
      · exact RingHom.lift_injective_of_ker_le_ideal _ _ (by rw [hk U])
      · intro y
        obtain ⟨x, rfl⟩ := hs U y
        exact ⟨Ideal.Quotient.mk _ x, rfl⟩
    exact NatIso.isIso_of_isIso_app q
  let e : principalPowerRingQuotient R a n ≅ H := by
    unfold principalPowerRingQuotient
    exact (presheafToSheaf J CommRingCat.{u}).mapIso (asIso q) ≪≫
      asIso ((sheafificationAdjunction J CommRingCat.{u}).counit.app H)
  refine ⟨e, ?_⟩
  apply Sheaf.hom_ext
  dsimp only [principalPowerRingProjection, e, Iso.trans_hom, Functor.mapIso_hom]
  change (sectionPowerQuotientProjection R a n ≫ toSheafify J _) ≫
    (sheafifyMap J q ≫ _) = p.hom
  rw [Category.assoc, ← Category.assoc (toSheafify J _),
    ← toSheafify_naturality, Category.assoc]
  simp only [asIso_hom, sheafificationAdjunction_counit_app_val]
  rw [toSheafify_sheafifyLift, Category.comp_id, hq]

/-- Completed coefficients have regular positive scalar powers and the specified finite
quotients, with the actual projections and all quotient transitions normalized.

Source: blueprint, proposition-sp-integral-towers proof, first paragraph; coefficient setup in
prose-09-21; Stacks Tags 00WK, 00YR, 03CO and 03DB.
(blueprint: lem-sp-completed-coefficient-regular-quotients).

Proof: (1) DVR factorization gives ell = u pi^e. The extending absolute value of ell
is less than one, so e is positive. Equality (ell^n)=(pi^(en)) proves cofinality;
finite residue field and the finite-quotient theorem give finiteness of both families.
(2) The integral-limit comparison identifies the actual completed ring and its scalar
map with the uniformizer tower. Cofinal restriction to en identifies the ell tower:
reduce from a sufficiently large en to define the inverse, independently of the choice.
(3) Apply completedIntegralScalar_regular on every object to pi powers.
(4) Apply completedIntegralProjection_divisible at index j-1 to a section in ker rho_j;
it is a pi^j multiple. The converse follows by reduction. Injectivity ensures unique
preimages glue, so this sectionwise ideal is the ideal subsheaf pi^jR.
(5) A section of the finite constant sheaf locally comes from O/pi^j, by 00WK and the
underlying-set comparison for ring sheafification. Lift the representative to O and
then to its compatible constant family. These local lifts prove rho_j is epi by sheaf
separatedness and cancellation against any two maps out of its target.
(6) Multiplication by the constant unit u^n is invertible. Hence ell^n is regular,
ell^nR=pi^(en)R, and the same conclusions hold for the actual ell projections.
(7) The sectionwise quotient map descends through ring sheafification. To construct its
inverse, lift target sections locally and glue their quotient classes: differences
of lifts lie in the kernel ideal by (4) and (6). The inverse is independent of lifts,
respects restrictions and ring operations, and is inverse on local representatives.
Both composites in each transition square send a local representative x to its lower
reduction; 00WK and separatedness imply equality. No property of T is used. -/
theorem sp_completed_coefficient_regular_quotients :
    (∃ (v : (Padic.coefficientExtensionIntegers l E)ˣ) (e : ℕ),
      1 ≤ e ∧ (l : Padic.coefficientExtensionIntegers l E) =
        (v : Padic.coefficientExtensionIntegers l E) *
          Padic.coefficientExtensionUniformizer l E ^ e) ∧
    ((∀ j : ℕ, ∃ n : ℕ, spEllIdeal l E ^ (n + 1) ≤
        Padic.coefficientExtensionIdeal l E (j + 1)) ∧
      (∀ n : ℕ, ∃ j : ℕ, Padic.coefficientExtensionIdeal l E (j + 1) ≤
        spEllIdeal l E ^ (n + 1))) ∧
    (∀ n : ℕ, Finite (Padic.coefficientExtensionRing l E (n + 1)) ∧
      Finite (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))) ∧
    (∀ (n : ℕ) (U : T.ProEtᵒᵖ),
      Function.Injective (fun x : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U ↦
        (@id ((completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
          ((spCompletedScalarSection l E T (Padic.coefficientExtensionUniformizer l E)).val U)) ^
          (n + 1) * x) ∧
      Function.Injective (fun x : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U ↦
        (@id ((completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
          ((spCompletedScalarSection l E T l).val U)) ^ (n + 1) * x)) ∧
    (∀ n : ℕ, Epi (completedIntegralCommRingProjectionUnrestricted l E T n) ∧
      Epi (spCompletedEllCommRingProjection l E T n) ∧
      ∀ U : T.ProEtᵒᵖ,
        RingHom.ker ((completedIntegralCommRingProjectionUnrestricted l E T n).hom.app U).hom =
          sectionPowerIdeal (completedIntegralCommRingSheafUnrestricted l E T)
            (spCompletedScalarSection l E T (Padic.coefficientExtensionUniformizer l E))
            (n + 1) U ∧
        RingHom.ker ((spCompletedEllCommRingProjection l E T n).hom.app U).hom =
          sectionPowerIdeal (completedIntegralCommRingSheafUnrestricted l E T)
            (spCompletedScalarSection l E T l) (n + 1) U) ∧
    ∃ (a : ∀ n : ℕ, principalPowerRingQuotient
        (completedIntegralCommRingSheafUnrestricted l E T)
        (spCompletedScalarSection l E T (Padic.coefficientExtensionUniformizer l E)) (n + 1) ≅
          integralCoefficientCommRingSheaf l E T n)
      (b : ∀ n : ℕ, principalPowerRingQuotient
        (completedIntegralCommRingSheafUnrestricted l E T)
        (spCompletedScalarSection l E T l) (n + 1) ≅ spEllCommRingSheaf l E T n),
      (∀ n : ℕ,
        principalPowerRingProjection (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalarSection l E T (Padic.coefficientExtensionUniformizer l E))
          (n + 1) ≫ (a n).hom = completedIntegralCommRingProjectionUnrestricted l E T n) ∧
      (∀ n : ℕ,
        principalPowerRingProjection (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalarSection l E T l) (n + 1) ≫ (b n).hom =
            spCompletedEllCommRingProjection l E T n) ∧
      (∀ (m n : ℕ) (h : m ≤ n),
        ∃ (r : principalPowerRingQuotient (completedIntegralCommRingSheafUnrestricted l E T)
            (spCompletedScalarSection l E T (Padic.coefficientExtensionUniformizer l E))
            (n + 1) ⟶ principalPowerRingQuotient
              (completedIntegralCommRingSheafUnrestricted l E T)
              (spCompletedScalarSection l E T (Padic.coefficientExtensionUniformizer l E))
              (m + 1))
          (s : principalPowerRingQuotient (completedIntegralCommRingSheafUnrestricted l E T)
            (spCompletedScalarSection l E T l) (n + 1) ⟶ principalPowerRingQuotient
              (completedIntegralCommRingSheafUnrestricted l E T)
              (spCompletedScalarSection l E T l) (m + 1)),
          principalPowerRingProjection (completedIntegralCommRingSheafUnrestricted l E T)
            (spCompletedScalarSection l E T (Padic.coefficientExtensionUniformizer l E))
            (n + 1) ≫ r =
              principalPowerRingProjection (completedIntegralCommRingSheafUnrestricted l E T)
                (spCompletedScalarSection l E T (Padic.coefficientExtensionUniformizer l E))
                (m + 1) ∧
          principalPowerRingProjection (completedIntegralCommRingSheafUnrestricted l E T)
            (spCompletedScalarSection l E T l) (n + 1) ≫ s =
              principalPowerRingProjection (completedIntegralCommRingSheafUnrestricted l E T)
                (spCompletedScalarSection l E T l) (m + 1) ∧
          r ≫ (a m).hom = (a n).hom ≫ spUniformizerQuotientTransition l E T h ∧
          s ≫ (b m).hom = (b n).hom ≫ spEllQuotientTransition l E T h) := by
  classical
  obtain ⟨e, he, v, hv⟩ := ell_factor l E
  let π := Padic.coefficientExtensionUniformizer l E
  let O := Padic.coefficientExtensionIntegers l E
  let R := completedIntegralCommRingSheafUnrestricted l E T
  let a := spCompletedScalarSection l E T π
  let b := spCompletedScalarSection l E T l
  have hell : spEllIdeal l E = Ideal.span {π} ^ e := by
    unfold spEllIdeal
    rw [hv, Ideal.span_singleton_mul_left_unit v.isUnit, Ideal.span_singleton_pow]
  have hpos (n : ℕ) : 1 ≤ e * (n + 1) := by nlinarith
  have hpow (n : ℕ) : spEllIdeal l E ^ (n + 1) =
      Padic.coefficientExtensionIdeal l E (e * (n + 1) - 1 + 1) := by
    rw [Nat.sub_add_cancel (hpos n)]
    change spEllIdeal l E ^ (n + 1) = Ideal.span {π} ^ (e * (n + 1))
    rw [hell, pow_mul]
  have hscalar (n : ℕ) (U : T.ProEtᵒᵖ) :
      scalarHom l E T U (l : O) ^ (n + 1) =
        scalarHom l E T U (v : O) ^ (n + 1) *
          scalarHom l E T U π ^ (e * (n + 1)) := by
    rw [hv, map_mul, map_pow, mul_pow, ← pow_mul]
  have hunit (n : ℕ) (U : T.ProEtᵒᵖ) :
      IsUnit (scalarHom l E T U (v : O) ^ (n + 1)) :=
    (v.isUnit.map (scalarHom l E T U)).pow (n + 1)
  have hkerπ := uniformizer_kernel l E T
  have hkerl (n : ℕ) (U : T.ProEtᵒᵖ) :
      RingHom.ker ((spCompletedEllCommRingProjection l E T n).hom.app U).hom =
        sectionPowerIdeal R b (n + 1) U := by
    have hk := normalized_kernel l E T (e * (n + 1) - 1)
      (spEllIdeal l E ^ (n + 1)) (hpow n)
      (spCompletedEllCommRingProjection l E T n) (ell_normalized l E T n) U
    rw [Nat.sub_add_cancel (hpos n)] at hk
    change _ = Ideal.span {scalarHom l E T U (l : O) ^ (n + 1)}
    rw [hscalar, Ideal.span_singleton_mul_left_unit (hunit n U)]
    exact hk
  have hsπ (n : ℕ) := projection_surjective l E T _ (uniformizer_normalized l E T n)
  have hsl (n : ℕ) := projection_surjective l E T _ (ell_normalized l E T n)
  refine ⟨⟨v, e, he, hv⟩, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro j
      obtain ⟨n, hn⟩ := (sp_coefficient_ideals_cofinal l E).1 (j + 1)
      exact ⟨n, (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn⟩
    · intro n
      obtain ⟨j, hj⟩ := (sp_coefficient_ideals_cofinal l E).2 (n + 1)
      exact ⟨j, (Ideal.pow_le_pow_right (Nat.le_succ j)).trans hj⟩
  · intro n
    refine ⟨Padic.finite_coefficientExtensionRing l E (n + 1) (by omega), ?_⟩
    rw [hpow n]
    exact Padic.finite_coefficientExtensionRing l E _ (by omega)
  · intro n U
    refine ⟨completedIntegralScalar_regular l E T (n + 1) U, ?_⟩
    change Function.Injective (fun x : R.obj.obj U ↦ scalarHom l E T U (l : O) ^ (n + 1) * x)
    intro x y hxy
    dsimp only at hxy
    rw [hscalar, mul_assoc, mul_assoc] at hxy
    apply completedIntegralScalar_regular l E T (e * (n + 1)) U
    exact (hunit n U).mul_left_cancel hxy
  · intro n
    exact ⟨sheaf_epi _ (hsπ n), sheaf_epi _ (hsl n), fun U ↦ ⟨hkerπ n U, hkerl n U⟩⟩
  · have hA (n : ℕ) := quotient_iso R (integralCoefficientCommRingSheaf l E T n) a
      (n + 1) (completedIntegralCommRingProjectionUnrestricted l E T n) (hsπ n) (hkerπ n)
    have hB (n : ℕ) := quotient_iso R (spEllCommRingSheaf l E T n) b
      (n + 1) (spCompletedEllCommRingProjection l E T n) (hsl n) (hkerl n)
    choose A hA using hA
    choose B hB using hB
    refine ⟨A, B, hA, hB, ?_⟩
    intro m n h
    have hcπ : completedIntegralCommRingProjectionUnrestricted l E T n ≫
        spUniformizerQuotientTransition l E T h =
          completedIntegralCommRingProjectionUnrestricted l E T m := by
      apply normalized_ext l E T ⟨m, le_rfl⟩ _ _ ?_
        (uniformizer_normalized l E T m)
      rw [← Category.assoc, uniformizer_normalized]
      unfold constQuot spUniformizerQuotientTransition
      rw [← Functor.map_comp]
      congr 1
    have hcl : spCompletedEllCommRingProjection l E T n ≫
        spEllQuotientTransition l E T h = spCompletedEllCommRingProjection l E T m := by
      apply normalized_ext l E T ?_ _ _ ?_ (ell_normalized l E T m)
      · exact ⟨e * (m + 1) - 1, (hpow m).ge⟩
      rw [← Category.assoc, ell_normalized]
      unfold constQuot spEllQuotientTransition
      rw [← Functor.map_comp]
      congr 1
    refine ⟨(A n).hom ≫ spUniformizerQuotientTransition l E T h ≫ (A m).inv,
      (B n).hom ≫ spEllQuotientTransition l E T h ≫ (B m).inv, ?_, ?_, ?_, ?_⟩
    · rw [← Category.assoc, hA, ← Category.assoc, hcπ, ← hA m]
      simp
      rfl
    · rw [← Category.assoc, hB, ← Category.assoc, hcl, ← hB m]
      simp
      rfl
    · simp
    · simp

end AlgebraicGeometry.ProEtale
