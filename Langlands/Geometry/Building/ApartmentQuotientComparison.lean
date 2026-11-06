import Langlands.Geometry.Building.ApartmentQuotient
import Mathlib.Algebra.Group.Action.Basic

/-!
# Equivariant comparison from an apartment quotient

The universal equivariant lift uses a fixer inclusion at every apartment point.
Global injectivity additionally uses common translated source apartments and
injectivity on the target apartment. These are explicit hypotheses.
-/

namespace Langlands.Geometry.Building.ApartmentQuotient

universe uH uA uB

variable {H : Type uH} [Group H] {N : Subgroup H}
  {A : Type uA} [MulAction N A] (P : CovariantSubgroupFamily N A)
  {B : Type uB} [MulAction H B]

/-- Any two quotient points belong to one translate of the canonical apartment. -/
def HasCommonTranslatedApartment : Prop :=
  ∀ q q' : ApartmentQuotient P,
    ∃ (g : H) (x y : A), g • apartment P x = q ∧ g • apartment P y = q'

/-- The equivariant lift of an apartment map whose value at every point is fixed
by the corresponding subgroup. -/
def lift (f : A →[N] B) (hf : ∀ x, P x ≤ MulAction.stabilizer H (f x)) :
    ApartmentQuotient P →[H] B where
  toFun := Quotient.lift (fun a : H × A => a.1 • f a.2) (by
    rintro ⟨g, x⟩ ⟨h, y⟩ ⟨n, hn, hmem⟩
    have hfix := MulAction.mem_stabilizer_iff.mp (hf x hmem)
    change (g⁻¹ * h * (n : H)) • f x = f x at hfix
    rw [← hn, map_smul, Subgroup.smul_def, smul_smul]
    calc
      g • f x = g • ((g⁻¹ * h * (n : H)) • f x) :=
        congrArg (fun z => g • z) hfix.symm
      _ = (h * (n : H)) • f x := by rw [smul_smul]; simp [mul_assoc])
  map_smul' h q := by
    induction q using ind with
    | h g x => exact mul_smul h g (f x)

@[simp]
theorem lift_mk (f : A →[N] B) (hf : ∀ x, P x ≤ MulAction.stabilizer H (f x))
    (g : H) (x : A) :
    lift P f hf (mk P (g, x)) = g • f x :=
  rfl

@[simp]
theorem lift_apartment (f : A →[N] B) (hf : ∀ x, P x ≤ MulAction.stabilizer H (f x))
    (x : A) :
    lift P f hf (apartment P x) = f x := by
  change (1 : H) • f x = f x
  exact one_smul H (f x)

/-- An equivariant map from the quotient is determined by its values on the
canonical apartment. -/
theorem hom_ext {F F' : ApartmentQuotient P →[H] B}
    (h : ∀ x, F (apartment P x) = F' (apartment P x)) : F = F' := by
  ext q
  induction q using ind with
  | h g x =>
    rw [mk_eq_smul_apartment, map_smul, map_smul, h x]

theorem lift_unique (f : A →[N] B) (hf : ∀ x, P x ≤ MulAction.stabilizer H (f x))
    (F : ApartmentQuotient P →[H] B) (hF : ∀ x, F (apartment P x) = f x) :
    F = lift P f hf := by
  apply hom_ext P
  intro x
  rw [hF, lift_apartment]

/-- The every-point fixer inclusion gives exactly one equivariant extension. -/
theorem existsUnique_lift (f : A →[N] B)
    (hf : ∀ x, P x ≤ MulAction.stabilizer H (f x)) :
    ∃! F : ApartmentQuotient P →[H] B, ∀ x, F (apartment P x) = f x :=
  ⟨lift P f hf, lift_apartment P f hf, fun F hF => lift_unique P f hf F hF⟩

theorem lift_surjective_iff (f : A →[N] B)
    (hf : ∀ x, P x ≤ MulAction.stabilizer H (f x)) :
    Function.Surjective (lift P f hf) ↔
      ∀ b : B, ∃ (g : H) (x : A), g • f x = b := by
  constructor
  · intro h b
    obtain ⟨q, hq⟩ := h b
    induction q using ind with
    | h g x => exact ⟨g, x, hq⟩
  · intro h b
    obtain ⟨g, x, hx⟩ := h b
    exact ⟨mk P (g, x), hx⟩

/-- Equality of images can be checked inside a common translated source
apartment, then cancelled by the group action. -/
theorem injective_of_common_translated_apartment
    (hcommon : HasCommonTranslatedApartment P)
    (F : ApartmentQuotient P →[H] B)
    (hF : Function.Injective (fun x => F (apartment P x))) :
    Function.Injective F := by
  intro q q' hqq'
  obtain ⟨g, x, y, rfl, rfl⟩ := hcommon q q'
  rw [map_smul, map_smul] at hqq'
  have hxy := hF (MulAction.injective g hqq')
  rw [hxy]

theorem lift_injective (f : A →[N] B)
    (hf : ∀ x, P x ≤ MulAction.stabilizer H (f x))
    (hcommon : HasCommonTranslatedApartment P) (hinj : Function.Injective f) :
    Function.Injective (lift P f hf) := by
  apply injective_of_common_translated_apartment P hcommon
  simpa only [lift_apartment] using hinj

/-- An equivariant bijection from the existing quotient to the supplied target.
Orbit coverage and common apartments are retained as hypotheses. -/
noncomputable def liftEquiv (f : A →[N] B)
    (hf : ∀ x, P x ≤ MulAction.stabilizer H (f x))
    (hcommon : HasCommonTranslatedApartment P) (hinj : Function.Injective f)
    (hcover : ∀ b : B, ∃ (g : H) (x : A), g • f x = b) :
    ApartmentQuotient P ≃ B :=
  Equiv.ofBijective (lift P f hf)
    ⟨lift_injective P f hf hcommon hinj, (lift_surjective_iff P f hf).mpr hcover⟩

@[simp]
theorem liftEquiv_apply (f : A →[N] B)
    (hf : ∀ x, P x ≤ MulAction.stabilizer H (f x))
    (hcommon : HasCommonTranslatedApartment P) (hinj : Function.Injective f)
    (hcover : ∀ b : B, ∃ (g : H) (x : A), g • f x = b)
    (q : ApartmentQuotient P) :
    liftEquiv P f hf hcommon hinj hcover q = lift P f hf q :=
  rfl

theorem liftEquiv_smul (f : A →[N] B)
    (hf : ∀ x, P x ≤ MulAction.stabilizer H (f x))
    (hcommon : HasCommonTranslatedApartment P) (hinj : Function.Injective f)
    (hcover : ∀ b : B, ∃ (g : H) (x : A), g • f x = b)
    (g : H) (q : ApartmentQuotient P) :
    liftEquiv P f hf hcommon hinj hcover (g • q) =
      g • liftEquiv P f hf hcommon hinj hcover q :=
  (lift P f hf).map_smul g q

theorem liftEquiv_symm_smul (f : A →[N] B)
    (hf : ∀ x, P x ≤ MulAction.stabilizer H (f x))
    (hcommon : HasCommonTranslatedApartment P) (hinj : Function.Injective f)
    (hcover : ∀ b : B, ∃ (g : H) (x : A), g • f x = b)
    (g : H) (b : B) :
    (liftEquiv P f hf hcommon hinj hcover).symm (g • b) =
      g • (liftEquiv P f hf hcommon hinj hcover).symm b := by
  apply (liftEquiv P f hf hcommon hinj hcover).injective
  rw [Equiv.apply_symm_apply, liftEquiv_smul, Equiv.apply_symm_apply]

section QuotientMap

variable {A' : Type uB} [MulAction N A'] (P' : CovariantSubgroupFamily N A')

/-- The comparison of quotients is injective once its apartment map is
injective, the target apartment embeds, and source points share apartments. -/
theorem map_injective_of_common_translated_apartment (f : A →[N] A')
    (hf : ∀ x, P x ≤ P' (f x))
    (hcommon : HasCommonTranslatedApartment P)
    (hinj : Function.Injective f) (hP' : IsStabilizerCompatible N P') :
    Function.Injective (map P P' f hf) := by
  apply injective_of_common_translated_apartment P hcommon
  simpa only [map_apartment, Function.comp_def] using (apartment_injective P' hP').comp hinj

theorem map_bijective_of_common_translated_apartment (f : A →[N] A')
    (hf : ∀ x, P x ≤ P' (f x))
    (hcommon : HasCommonTranslatedApartment P)
    (hbij : Function.Bijective f) (hP' : IsStabilizerCompatible N P') :
    Function.Bijective (map P P' f hf) :=
  ⟨map_injective_of_common_translated_apartment P P' f hf hcommon hbij.1 hP',
    map_surjective f hf hbij.2⟩

end QuotientMap

end Langlands.Geometry.Building.ApartmentQuotient
