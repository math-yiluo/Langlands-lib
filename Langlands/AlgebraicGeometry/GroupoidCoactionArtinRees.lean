import Langlands.AlgebraicGeometry.GroupoidCoactionIdealDevissage
import Langlands.AlgebraicGeometry.GroupoidCoactionCokernel
import Mathlib.RingTheory.Filtration

/-! # Artin–Rees support dévissage for coactions -/

universe u v

namespace Langlands.AlgebraicGeometry

namespace CoactionArtinRees

variable {B : Type u} [CommRing B]
variable {M N : Type v} [AddCommGroup M] [Module B M]
  [AddCommGroup N] [Module B N]

/-- The restriction of a linear map to an ideal-power multiple of its domain. -/
def idealPowerRestriction (I : Ideal B) (f : M →ₗ[B] N) (n : ℕ) :
    ↥(I ^ n • (⊤ : Submodule B M)) →ₗ[B] N :=
  f.comp (I ^ n • (⊤ : Submodule B M)).subtype

@[simp]
lemma idealPowerRestriction_apply (I : Ideal B) (f : M →ₗ[B] N) (n : ℕ)
    (x : ↥(I ^ n • (⊤ : Submodule B M))) :
    idealPowerRestriction I f n x = f x := rfl

/-- An annihilator containment is equivalent to the ideal multiple lying in
an equivariant map's image; the assertion itself only uses linear algebra. -/
lemma le_annihilator_quotient_iff (I : Ideal B) (P : Submodule B M) :
    I ≤ Module.annihilator B (M ⧸ P) ↔ I • (⊤ : Submodule B M) ≤ P := by
  constructor
  · intro h
    apply Submodule.smul_le.mpr
    intro a ha m _
    apply (Submodule.Quotient.mk_eq_zero P).mp
    change P.mkQ (a • m) = 0
    rw [P.mkQ.map_smul]
    exact Module.mem_annihilator.mp (h ha) (P.mkQ m)
  · intro h a ha
    apply Module.mem_annihilator.mpr
    intro q
    obtain ⟨m, rfl⟩ := P.mkQ_surjective q
    rw [← P.mkQ.map_smul]
    exact (Submodule.Quotient.mk_eq_zero P).mpr
      (h (Submodule.smul_mem_smul ha Submodule.mem_top))

/-- Artin–Rees removes the kernel of a map after multiplication by a high
power of an ideal supported on that kernel. -/
lemma exists_pow_smul_inf_ker_eq_bot [IsNoetherianRing B] [Module.Finite B M]
    (I : Ideal B) (f : M →ₗ[B] N)
    (hI : I ≤ (Module.annihilator B (LinearMap.ker f)).radical) :
    ∃ n : ℕ, (I ^ n • (⊤ : Submodule B M)) ⊓ LinearMap.ker f = ⊥ := by
  obtain ⟨r, hr⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hI I.fg_of_isNoetherianRing
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.ker f)
  refine ⟨r + k, ?_⟩
  rw [hk (r + k) (by omega), Nat.add_sub_cancel]
  apply eq_bot_iff.mpr
  apply Submodule.smul_le.mpr
  intro a ha m hm
  change a • m = 0
  exact congrArg Subtype.val (Module.mem_annihilator.mp (hr ha)
    (⟨m, hm.2⟩ : LinearMap.ker f))

/-- Restriction to an ideal power with zero intersection with the kernel is
injective. -/
lemma injective_restrict_of_inf_ker_eq_bot (I : Ideal B) (f : M →ₗ[B] N) (n : ℕ)
    (hn : (I ^ n • (⊤ : Submodule B M)) ⊓ LinearMap.ker f = ⊥) :
    Function.Injective (idealPowerRestriction I f n) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hz : (x : M) - y ∈ (I ^ n • (⊤ : Submodule B M)) ⊓ LinearMap.ker f :=
    ⟨Submodule.sub_mem _ x.property y.property,
      by change f ((x : M) - y) = 0; rw [map_sub, sub_eq_zero]; exact hxy⟩
  simpa only [hn, Submodule.mem_bot] using hz

/-- The original cokernel's annihilator controls the cokernel after restriction
to an ideal power. -/
lemma pow_le_annihilator_cokernel_restrict (I : Ideal B) (f : M →ₗ[B] N)
    (r n : ℕ) (hr : I ^ r ≤ Module.annihilator B (N ⧸ LinearMap.range f)) :
    I ^ (n + r) ≤ Module.annihilator B
      (N ⧸ LinearMap.range (idealPowerRestriction I f n)) := by
  apply (le_annihilator_quotient_iff _ _).mpr
  have hle : I ^ r • (⊤ : Submodule B N) ≤ LinearMap.range f :=
    (le_annihilator_quotient_iff _ _).mp hr
  have hrange : LinearMap.range (idealPowerRestriction I f n) =
      I ^ n • LinearMap.range f := by
    rw [idealPowerRestriction, LinearMap.range_comp, Submodule.range_subtype,
      Submodule.map_smul'', Submodule.map_top]
  rw [hrange, pow_add, mul_smul]
  exact smul_le_smul_left (I ^ n) hle

/-- A map whose kernel is supported on the vanishing locus of an ideal is
injective on a high ideal power, and its restricted cokernel is still
supported there if the original cokernel was. -/
lemma exists_injective_pow_restrict [IsNoetherianRing B] [Module.Finite B M]
    (I : Ideal B) (f : M →ₗ[B] N)
    (hK : I ≤ (Module.annihilator B (LinearMap.ker f)).radical)
    (hQ : I ≤ (Module.annihilator B (N ⧸ LinearMap.range f)).radical) :
    ∃ n r : ℕ,
      Function.Injective (idealPowerRestriction I f n) ∧
      I ^ r ≤ Module.annihilator B
        (N ⧸ LinearMap.range (idealPowerRestriction I f n)) := by
  obtain ⟨n, hn⟩ := exists_pow_smul_inf_ker_eq_bot I f hK
  obtain ⟨r, hr⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hQ I.fg_of_isNoetherianRing
  exact ⟨n, n + r, injective_restrict_of_inf_ker_eq_bot I f n hn,
    pow_le_annihilator_cokernel_restrict I f r n hr⟩

end CoactionArtinRees

namespace GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C} [IsNoetherianRing B]
variable {M N : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
  [AddCommGroup N] [Module B N] [Module.Finite B N]

/-- Support dévissage through a map whose ideal-power restrictions are acyclic.
Artin–Rees makes one such restriction injective and power dévissage handles
its cokernel on the smaller support. -/
theorem oneCohomologyVanishes_of_artinRees (hE : RingEtaleEquivalenceRelation t)
    (θM : GroupoidCoaction t M) (θN : GroupoidCoaction t N)
    (f : M →ₗ[B] N) (hf : θM.IsHom θN f)
    (I : Ideal B) (hI : IsInvariantIdeal t I)
    (hK : I ≤ (Module.annihilator B (LinearMap.ker f)).radical)
    (hQ : I ≤ (Module.annihilator B (N ⧸ LinearMap.range f)).radical)
    (hvan : FiniteAnnihilatorVanishing.{u, v} t I)
    (hpowers : ∀ n : ℕ, ∀ hstable : θM.IsStableSubmodule
      (I ^ n • (⊤ : Submodule B M)),
      (submodule θM _ hE hstable).OneCohomologyVanishes) :
    θN.OneCohomologyVanishes := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  obtain ⟨n, r, hinj, hann⟩ := CoactionArtinRees.exists_injective_pow_restrict I f hK hQ
  let P : Submodule B M := I ^ n • ⊤
  have hP : θM.IsStableSubmodule P := hI.isStableSubmodule_pow_smul_top θM n
  let θP := submodule θM P hE hP
  let g := f.comp P.subtype
  have hg : θP.IsHom θN g := hf.comp (submodule_subtype_isHom θM P hE hP)
  let θQ := cokernel θP θN g hg
  have hQvan : θQ.OneCohomologyVanishes :=
    finiteAnnihilatorVanishing_pow hE I hI hvan r _ θQ hann
  exact oneCohomologyVanishes_of_shortExact g (LinearMap.range g).mkQ
    hg (cokernel_mkQ_isHom θP θN g hg) hinj
    (LinearMap.range g).mkQ_surjective (by simp) (hpowers n hP) hQvan

end GroupoidCoaction

end Langlands.AlgebraicGeometry
