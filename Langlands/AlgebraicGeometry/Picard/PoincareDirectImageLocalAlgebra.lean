import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Langlands.Cohomology.PerfectModuleComplex

/-! # Local algebra for the Poincaré direct image -/

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace Langlands.AbelianScheme.PoincareDirectImage

section DualNumber

variable {K : Type u} {R : Type u} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]

/-- The `K`-algebra map `K[ε] ⟶ R ⧸ J` sending `ε` to the class of `e`. -/
noncomputable def dualNumberHom (J : Ideal R) (e : R) (he : e * e ∈ J) :
    DualNumber K →ₐ[K] R ⧸ J :=
  DualNumber.lift ⟨(Algebra.ofId K (R ⧸ J), Ideal.Quotient.mk J e),
    by rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact he,
    fun _ => Commute.all _ _⟩

omit [IsLocalRing R] in
lemma dualNumberHom_apply (J : Ideal R) (e : R) (he : e * e ∈ J) (z : DualNumber K) :
    dualNumberHom J e he z =
      Ideal.Quotient.mk J (algebraMap K R z.fst + algebraMap K R z.snd * e) := by
  rw [dualNumberHom, DualNumber.lift_apply_apply]
  simp only [Algebra.ofId_apply, map_add, map_mul]
  rfl

/-- If the residue field of the local `K`-algebra `R` is `K`, and `m² ≤ J ⋖ m`, then
`R ⧸ J` is isomorphic to the dual numbers over `K`. -/
theorem nonempty_dualNumber_algEquiv
    (hres : Function.Bijective (algebraMap K (ResidueField R)))
    (J : Ideal R) (hsq : maximalIdeal R ^ 2 ≤ J) (hcov : J ⋖ maximalIdeal R) :
    Nonempty (DualNumber K ≃ₐ[K] R ⧸ J) := by
  obtain ⟨e, hem, heJ⟩ := SetLike.exists_of_lt hcov.lt
  have he : e * e ∈ J := hsq (by rw [pow_two]; exact Ideal.mul_mem_mul hem hem)
  have hres' : ∀ a : K, residue R (algebraMap K R a) = algebraMap K (ResidueField R) a :=
    fun a => (IsScalarTower.algebraMap_apply K R (ResidueField R) a).symm
  have hsup : J ⊔ Ideal.span {e} = maximalIdeal R := by
    have hle : J ⊔ Ideal.span {e} ≤ maximalIdeal R :=
      sup_le hcov.le (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hem)
    have hlt : J < J ⊔ Ideal.span {e} := by
      refine lt_of_le_of_ne le_sup_left fun h => heJ ?_
      rw [h]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self e)
    exact eq_of_le_of_not_lt hle (hcov.2 hlt)
  refine ⟨AlgEquiv.ofBijective (dualNumberHom J e he) ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    rw [dualNumberHom_apply, Ideal.Quotient.eq_zero_iff_mem] at hz
    have hbe : algebraMap K R z.snd * e ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hem
    have ha : algebraMap K R z.fst ∈ maximalIdeal R := by
      have := hcov.le hz
      simpa using (Ideal.add_mem_iff_left _ hbe).mp this
    have ha0 : z.fst = 0 := by
      apply hres.1
      rw [map_zero, ← hres', (residue_eq_zero_iff _).mpr ha]
    rw [ha0, map_zero, zero_add] at hz
    have hb0 : z.snd = 0 := by
      by_contra hb
      have hu : IsUnit (algebraMap K R z.snd) := (IsUnit.mk0 _ hb).map _
      exact heJ ((Ideal.unit_mul_mem_iff_mem J hu).mp hz)
    exact TrivSqZeroExt.ext ha0 hb0
  · intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hres.2 (residue R r)
    have hra : r - algebraMap K R a ∈ maximalIdeal R := by
      rw [← residue_eq_zero_iff, map_sub, hres', ha, sub_self]
    rw [← hsup, Submodule.mem_sup] at hra
    obtain ⟨j, hj, s, hs, hjs⟩ := hra
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    obtain ⟨b, hb⟩ := hres.2 (residue R c)
    have hcb : c - algebraMap K R b ∈ maximalIdeal R := by
      rw [← residue_eq_zero_iff, map_sub, hres', hb, sub_self]
    have hcbe : (c - algebraMap K R b) * e ∈ J :=
      hsq (by rw [pow_two]; exact Ideal.mul_mem_mul hcb hem)
    refine ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, ?_⟩
    rw [dualNumberHom_apply, Ideal.Quotient.eq]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, add_zero, zero_add]
    have : algebraMap K R a + algebraMap K R b * e - r = -(j + (c - algebraMap K R b) * e) := by
      linear_combination hjs
    rw [this]
    exact J.neg_mem (J.add_mem hj hcbe)

end DualNumber

section ResidueField

variable {B S : Type u} [CommRing B] [CommRing S] [Algebra B S]

/-- For the localization `S` of `B` at a maximal ideal `p`, every element of the residue field
of `S` comes from `B`. -/
theorem algebraMap_residueField_surjective_of_isLocalization (p : Ideal B) [p.IsMaximal]
    [IsLocalization.AtPrime S p] [IsLocalRing S] :
    Function.Surjective (algebraMap B (ResidueField S)) := by
  intro z
  obtain ⟨s, rfl⟩ := residue_surjective z
  obtain ⟨⟨r, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl s
  obtain ⟨v, i, hi, hvi⟩ := Ideal.IsMaximal.exists_inv (I := p) ‹_› u.2
  refine ⟨r * v, ?_⟩
  rw [IsScalarTower.algebraMap_apply B S (ResidueField S), ResidueField.algebraMap_eq]
  dsimp only
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  have hu : algebraMap B S u * IsLocalization.mk' S r u = algebraMap B S r :=
    IsLocalization.mk'_spec' S r u
  have hiS : algebraMap B S i ∈ maximalIdeal S :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff S p i).mpr hi
  have : algebraMap B S (r * v) - IsLocalization.mk' S r u =
      -(IsLocalization.mk' S r u * algebraMap B S i) := by
    have h1 : algebraMap B S v * algebraMap B S u + algebraMap B S i = 1 := by
      rw [← map_mul, ← map_add, hvi, map_one]
    rw [map_mul, ← hu]
    linear_combination (IsLocalization.mk' S r u) * h1
  rw [this]
  exact (maximalIdeal S).neg_mem (Ideal.mul_mem_left _ _ hiS)

/-- If `K → B` has a retraction `ev : B → K` whose kernel is the maximal ideal `p`, and `S` is
the localization of `B` at `p`, then `K` maps isomorphically onto the residue field of `S`. -/
theorem bijective_algebraMap_residueField {K : Type u} [Field K] [Algebra K S]
    (κ : K →+* B) (ev : B →+* K) (hev : ev.comp κ = RingHom.id K) (p : Ideal B)
    (hker : RingHom.ker ev = p) [p.IsMaximal] [IsLocalization.AtPrime S p] [IsLocalRing S]
    (hK : algebraMap K S = (algebraMap B S).comp κ) :
    Function.Bijective (algebraMap K (ResidueField S)) := by
  refine ⟨(algebraMap K (ResidueField S)).injective, fun z => ?_⟩
  obtain ⟨b, rfl⟩ := algebraMap_residueField_surjective_of_isLocalization (S := S) p z
  refine ⟨ev b, ?_⟩
  have hb : b - κ (ev b) ∈ p := by
    rw [← hker, RingHom.mem_ker, map_sub, ← RingHom.comp_apply ev κ, hev, RingHom.id_apply,
      sub_self]
  rw [IsScalarTower.algebraMap_apply K S (ResidueField S), hK, RingHom.comp_apply,
    IsScalarTower.algebraMap_apply B S (ResidueField S) b, ResidueField.algebraMap_eq,
    ← sub_eq_zero, ← map_sub, ← map_sub, residue_eq_zero_iff, ← neg_sub, map_neg]
  exact (maximalIdeal S).neg_mem ((IsLocalization.AtPrime.to_map_mem_maximal_iff S p _).mpr hb)

end ResidueField

section Support

variable {B : Type u} [CommRing B] {M : Type u} [AddCommGroup M] [Module B M]

/-- If every element of a finite module is killed by a power of `f`, then one power of `f`
kills the whole module. -/
theorem exists_pow_smul_eq_zero [Module.Finite B M] (f : B)
    (h : ∀ x : M, ∃ k : ℕ, f ^ k • x = 0) : ∃ k : ℕ, ∀ x : M, f ^ k • x = 0 := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := M)
  choose k hk using h
  refine ⟨s.sup k, fun x => ?_⟩
  have hx : x ∈ Submodule.span B (s : Set M) := hs ▸ Submodule.mem_top
  have hle : Submodule.span B (s : Set M) ≤
      LinearMap.ker ((f ^ s.sup k) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    have hky : k y ≤ s.sup k := Finset.le_sup (f := k) hy
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← Nat.sub_add_cancel hky, pow_add, mul_smul, hk y, smul_zero]
  have := hle hx
  simpa only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] using this

/-- Over a noetherian ring, if every element of the ideal `m` acts nilpotently on each element
of the finite module `M`, then a power of `m` kills `M`. -/
theorem exists_pow_le_annihilator [IsNoetherianRing B] [Module.Finite B M] (m : Ideal B)
    (h : ∀ f ∈ m, ∀ x : M, ∃ k : ℕ, f ^ k • x = 0) :
    ∃ N : ℕ, m ^ N ≤ Module.annihilator B M := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian m)
  intro f hf
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero f (h f hf)
  exact ⟨k, Module.mem_annihilator.mpr hk⟩

/-- Extending scalars along `φ : B →+* S` carries the annihilator of `M` into the annihilator
of `S ⊗_B M`. -/
theorem map_annihilator_le {S : Type u} [CommRing S] (φ : B →+* S) (M : ModuleCat.{u} B) :
    (Module.annihilator B M).map φ ≤
      Module.annihilator S ((ModuleCat.extendScalars φ).obj M) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro z
  refine TensorProduct.inductionOn
    (motive := fun z : TensorProduct B ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) M =>
      φ a • (show (ModuleCat.extendScalars φ).obj M from z) = 0) z ?_ ?_
  · intro s x
    have hx : a • x = 0 := Module.mem_annihilator.mp ha x
    exact (TensorProduct.smul_tmul a s x).trans (by rw [hx, TensorProduct.tmul_zero]; rfl)
  · intro y w hy hw
    exact (smul_add (A := (ModuleCat.extendScalars φ).obj M) (φ a)
      (show (ModuleCat.extendScalars φ).obj M from y)
      (show (ModuleCat.extendScalars φ).obj M from w)).trans (by rw [hy, hw, add_zero])

/-- If the scalar extension of `M` to a localization of `B` at `T` vanishes, then every element
of `M` is killed by an element of `T`. -/
theorem exists_smul_eq_zero_of_isZero {A : Type u} [CommRing A] (φ : B →+* A)
    {T : Submonoid B} (hT : T.IsLocalizationMap φ) (M : ModuleCat.{u} B)
    (h : IsZero ((ModuleCat.extendScalars φ).obj M)) (x : M) : ∃ t ∈ T, t • x = 0 := by
  let := φ.toAlgebra
  have : IsLocalization T A := ⟨hT⟩
  let g : M →ₗ[B] TensorProduct B A M := TensorProduct.mk B A M 1
  have : IsLocalizedModule T g :=
    (isLocalizedModule_iff_isBaseChange T A g).2 (TensorProduct.isBaseChange B M A)
  have hsub : Subsingleton (TensorProduct B A M) := ModuleCat.isZero_iff_subsingleton.mp h
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T g).mp (Subsingleton.elim _ _)
  exact ⟨t, t.2, ht⟩

/-- If `B_f ⊗_B M` vanishes, then every element of `M` is killed by a power of `f`. -/
theorem exists_pow_smul_eq_zero_of_isZero (f : B) (M : ModuleCat.{u} B)
    (h : IsZero ((ModuleCat.extendScalars (algebraMap B (Localization.Away f))).obj M))
    (x : M) : ∃ k : ℕ, f ^ k • x = 0 := by
  obtain ⟨t, ⟨k, rfl⟩, ht⟩ := exists_smul_eq_zero_of_isZero _
    ((isLocalization_iff_isLocalizationMap (Submonoid.powers f) (Localization.Away f)).mp
      inferInstance) M h x
  exact ⟨k, ht⟩

end Support

section PunctualAux

variable {B R : Type u} [CommRing B] [CommRing R]

/-- A module killed by a power of a maximal ideal `m`, whose extension of scalars along a
localization map at `m` is the residue field, is isomorphic to `B ⧸ m`. -/
theorem nonempty_iso_quotient_of_pow_le_annihilator' [IsLocalRing R] (φ : B →+* R)
    (m : Ideal B) [m.IsMaximal] (hφ : m.primeCompl.IsLocalizationMap φ) (M : ModuleCat.{u} B)
    {N : ℕ} (hN : m ^ N ≤ Module.annihilator B M)
    (e : (ModuleCat.extendScalars φ).obj M ≅ ModuleCat.of R (ResidueField R)) :
    Nonempty (M ≅ ModuleCat.of B (B ⧸ m)) := by
  let := φ.toAlgebra
  have : IsLocalization.AtPrime R m := ⟨hφ⟩
  have hunit : ∀ t ∈ m.primeCompl, ∃ a : B, ∀ x : M, a • t • x = x := by
    intro t ht
    obtain ⟨v, i, hi, hvi⟩ := Ideal.IsMaximal.exists_inv ‹m.IsMaximal› ht
    have hc : IsCoprime t (i ^ N) :=
      (show IsCoprime t i from ⟨v, 1, by linear_combination hvi⟩).pow_right
    obtain ⟨a, b, hab⟩ := hc
    refine ⟨a, fun x => ?_⟩
    have hix : (i ^ N) • x = 0 := Module.mem_annihilator.mp (hN (Ideal.pow_mem_pow hi N)) x
    have h1 : a * t = 1 - b * i ^ N := by linear_combination hab
    rw [← mul_smul, h1, sub_smul, one_smul, mul_smul, hix, smul_zero, sub_zero]
  let g : M →ₗ[B] TensorProduct B R M := TensorProduct.mk B R M 1
  have hloc : IsLocalizedModule m.primeCompl g :=
    (isLocalizedModule_iff_isBaseChange m.primeCompl R g).2 (TensorProduct.isBaseChange B M R)
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨⟨t, ht⟩, htx⟩ := (IsLocalizedModule.eq_zero_iff m.primeCompl g).mp hx
    obtain ⟨a, ha⟩ := hunit t ht
    rw [← ha x]
    change a • (t • x) = 0
    rw [show t • x = 0 from htx, smul_zero]
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨⟨x, ⟨t, ht⟩⟩, hxy⟩ := IsLocalizedModule.surj m.primeCompl g y
    obtain ⟨a, ha⟩ := hunit t ht
    refine ⟨a • x, ?_⟩
    have hu := IsLocalizedModule.map_units g ⟨t, ht⟩
    apply ((Module.End.isUnit_iff _).mp hu).1
    change t • g (a • x) = t • y
    rw [← map_smul, smul_comm, ha x]
    exact hxy.symm
  let ψ : M ≃ₗ[B] TensorProduct B R M := LinearEquiv.ofBijective g ⟨hinj, hsurj⟩
  let e' : TensorProduct B R M ≃ₗ[R] ResidueField R := e.toLinearEquiv
  let e'' : TensorProduct B R M ≃ₗ[B] ResidueField R := e'.restrictScalars B
  have hsurjres : Function.Surjective (Algebra.ofId B (ResidueField R)) :=
    algebraMap_residueField_surjective_of_isLocalization (S := R) m
  have hker : RingHom.ker (Algebra.ofId B (ResidueField R)) = m := by
    ext r
    rw [RingHom.mem_ker, Algebra.ofId_apply,
      IsScalarTower.algebraMap_apply B R (ResidueField R), ResidueField.algebraMap_eq,
      residue_eq_zero_iff, IsLocalization.AtPrime.to_map_mem_maximal_iff R m]
  let q : (B ⧸ m) ≃ₗ[B] ResidueField R :=
    Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ
      (Ideal.quotientKerAlgEquivOfSurjective hsurjres).toLinearEquiv
  exact ⟨(ψ ≪≫ₗ e'' ≪≫ₗ q.symm).toModuleIso⟩

end PunctualAux

section Punctual

variable {B R : Type u} [CommRing B] [CommRing R] [Algebra B R]

/-- A module killed by a power of a maximal ideal `m`, whose localization at `m` vanishes, is
zero. -/
theorem isZero_of_pow_le_annihilator (m : Ideal B) [m.IsMaximal] [IsLocalization.AtPrime R m]
    (M : ModuleCat.{u} B) {N : ℕ} (hN : m ^ N ≤ Module.annihilator B M)
    (hz : IsZero ((ModuleCat.extendScalars (algebraMap B R)).obj M)) : IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ z : M, z = 0 by rw [h x, h y]
  intro z
  obtain ⟨t, ht, htz⟩ := exists_smul_eq_zero_of_isZero (algebraMap B R)
    ((isLocalization_iff_isLocalizationMap m.primeCompl R).mp inferInstance) M hz z
  let I : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B M z)
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨n, hn, hIn⟩ := Ideal.exists_le_maximal I hne
    have hmn : m ^ N ≤ n := fun r hr => hIn (by
      change r • z = 0
      exact Module.mem_annihilator.mp (hN hr) z)
    have hmn' : m ≤ n := hn.isPrime.le_of_pow_le hmn
    have hmeq : m = n := ‹m.IsMaximal›.eq_of_le hn.ne_top hmn'
    exact ht (hmeq ▸ hIn (show t • z = 0 from htz))
  have h1 : (1 : B) ∈ I := hI ▸ Submodule.mem_top
  simpa using (show (1 : B) • z = 0 from h1)

/-- A module killed by a power of a maximal ideal `m`, whose localization at `m` is the residue
field, is isomorphic to `B ⧸ m`. -/
theorem nonempty_iso_quotient_of_pow_le_annihilator [IsLocalRing R] (m : Ideal B) [m.IsMaximal]
    [IsLocalization.AtPrime R m] (M : ModuleCat.{u} B) {N : ℕ}
    (hN : m ^ N ≤ Module.annihilator B M)
    (e : (ModuleCat.extendScalars (algebraMap B R)).obj M ≅ ModuleCat.of R (ResidueField R)) :
    Nonempty (M ≅ ModuleCat.of B (B ⧸ m)) :=
  nonempty_iso_quotient_of_pow_le_annihilator' (algebraMap B R) m
    ((isLocalization_iff_isLocalizationMap m.primeCompl R).mp inferInstance) M hN e

end Punctual

section FlatHomology

open Langlands.Cohomology.ModuleComplex

/-- Flat scalar extension commutes with the homology of a cochain complex. -/
theorem nonempty_baseChange_homology_iso_of_flat {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Nonempty (((baseChange φ).obj K).homology n ≅
      (ModuleCat.extendScalars φ).obj (K.homology n)) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  exact ⟨(K.sc n).mapHomologyIso (ModuleCat.extendScalars φ)⟩

end FlatHomology

section SupportHomology

open Langlands.Cohomology.ModuleComplex

variable {B : Type u} [CommRing B]

/-- Over a noetherian ring, the homology of a strictly perfect complex is finite. -/
theorem finite_homology [IsNoetherianRing B] {Kc : CochainComplex (ModuleCat.{u} B) ℤ}
    (hKc : IsStrictlyPerfect Kc) (n : ℤ) : Module.Finite B (Kc.homology n) := by
  have := (hKc.2 n).1
  have : Module.Finite B (Kc.cycles n) :=
    Module.Finite.of_injective (Kc.iCycles n).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  exact Module.Finite.of_surjective (Kc.homologyπ n).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- If the homology of a strictly perfect complex over a noetherian ring vanishes after
inverting each element of `m`, then a power of `m` kills each homology module. -/
theorem exists_pow_le_annihilator_homology [IsNoetherianRing B] (m : Ideal B)
    {Kc : CochainComplex (ModuleCat.{u} B) ℤ} (hKc : IsStrictlyPerfect Kc)
    (hsupp : ∀ f ∈ m, ∀ n : ℤ,
      IsZero (((baseChange (algebraMap B (Localization.Away f))).obj Kc).homology n))
    (n : ℤ) : ∃ N : ℕ, m ^ N ≤ Module.annihilator B (Kc.homology n) := by
  have := finite_homology hKc n
  refine exists_pow_le_annihilator m fun f hf x => ?_
  have hflat : (algebraMap B (Localization.Away f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  obtain ⟨e⟩ := nonempty_baseChange_homology_iso_of_flat _ hflat Kc n
  exact exists_pow_smul_eq_zero_of_isZero f _ (IsZero.of_iso (hsupp f hf n) e.symm) x

/-- The corresponding statement for the localization at a prime `m`. -/
theorem exists_pow_le_annihilator_homology_localization [IsNoetherianRing B] (m : Ideal B)
    [m.IsPrime] {R : Type u} [CommRing R] [Algebra B R] [IsLocalization.AtPrime R m]
    [IsLocalRing R] {Kc : CochainComplex (ModuleCat.{u} B) ℤ} (hKc : IsStrictlyPerfect Kc)
    (hsupp : ∀ f ∈ m, ∀ n : ℤ,
      IsZero (((baseChange (algebraMap B (Localization.Away f))).obj Kc).homology n))
    (n : ℤ) : ∃ N : ℕ, maximalIdeal R ^ N ≤
      Module.annihilator R (((baseChange (algebraMap B R)).obj Kc).homology n) := by
  obtain ⟨N, hN⟩ := exists_pow_le_annihilator_homology m hKc hsupp n
  refine ⟨N, ?_⟩
  have hflat : (algebraMap B R).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ m.primeCompl)
  obtain ⟨e⟩ := nonempty_baseChange_homology_iso_of_flat _ hflat Kc n
  rw [e.toLinearEquiv.annihilator_eq, ← IsLocalization.AtPrime.map_eq_maximalIdeal m R,
    ← Ideal.map_pow]
  exact (Ideal.map_mono hN).trans (map_annihilator_le _ _)

end SupportHomology

end Langlands.AbelianScheme.PoincareDirectImage
