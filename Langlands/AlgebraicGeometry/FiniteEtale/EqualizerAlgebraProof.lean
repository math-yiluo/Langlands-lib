/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 files have no copyright notice; their holder requires review.

Adapted from the NYLL files
`Nyll/SchemeTheory/Pi1/FiniteEtale/Algebra/Basic.lean`,
`Nyll/SchemeTheory/Pi1/FiniteEtale/Algebra/Descent.lean` and
`Nyll/SchemeTheory/Pi1/FiniteEtale/Algebra/Equalizer.lean`
at commit fbd320cd8b1b06487c58227e92eb135794267709
(https://github.com/n-yamaguchi-0729/ClassFieldTheory), which are NYLL-maintained
adaptations of the pinned pi1 sources
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Basic.lean
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Descent.lean
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Equalizer.lean
The pi1 revision is a comparison revision; the historical NYLL import revision is
unverified. Adaptation to this Library: Worker 266. The upstream license and
notices are retained in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/
import Langlands.AlgebraicGeometry.FiniteEtale.EqualizerAlgebraStatements
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Logic.Function.Coequalizer
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.TotallySplit

/-!
# Proof of finite étale closure of algebra equalizers

The equalizer of two algebra maps between finite étale `R`-algebras is finite and
étale over `R`. After localizing to constant ranks and splitting both algebras by
a faithfully flat finite étale base change, the maps become maps between finite
function algebras. These are coordinate maps locally on `Spec R`, and the equalizer
of two coordinate maps is the function algebra on a finite coequalizer.

Finiteness and étaleness are carried as the explicit pair
`Module.Finite R S ∧ Algebra.Etale R S`; no finite étale class is introduced.
-/

universe u

open TensorProduct

namespace Langlands.AlgebraicGeometry.FiniteEtale

namespace EqualizerAlgebra

section Basic

/-- A property that is local in the sense of `RingHom.OfLocalizationSpan` holds as
soon as every prime has a basic open neighbourhood on which it holds. -/
lemma ofLocalizationSpan_of_exists_of_isPrime
    {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hP : RingHom.OfLocalizationSpan P)
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p, P (Localization.awayMap f r)) :
    P f := by
  have := H
  choose u hu₁ hu₂ using this
  apply hP f (Set.range (fun p : PrimeSpectrum R ↦ u p.asIdeal))
  · rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    rw [_root_.eq_top_iff]
    rintro p -
    simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
      PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iUnion, Set.mem_compl_iff,
      PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
    use p
    apply hu₁
  · rintro ⟨p, ⟨p, rfl⟩⟩
    apply hu₂

/-- The algebra-map form of `ofLocalizationSpan_of_exists_of_isPrime`, with the
localized map written as a base change `Rᵣ → Rᵣ ⊗[R] S`. -/
lemma ofLocalizationSpan_of_exists_of_isPrime'
    {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hP : RingHom.OfLocalizationSpan P)
    (hPi : RingHom.RespectsIso P)
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      P (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] S))) :
    P (algebraMap R S) := by
  apply ofLocalizationSpan_of_exists_of_isPrime hP
  intro p hp
  obtain ⟨r, hr, hf⟩ := H p
  refine ⟨r, hr, ?_⟩
  have : IsLocalization.Away ((Algebra.ofId R S) r) (Localization.Away ((algebraMap R S) r)) :=
    inferInstanceAs <| IsLocalization.Away (algebraMap R S r) _
  let e₀ : S ⊗[R] Localization.Away r ≃ₐ[R] Localization.Away (algebraMap R S r) :=
    (IsLocalization.Away.tensorEquiv _ r (Localization.Away r)).restrictScalars R
  let e : Localization.Away r ⊗[R] S ≃+* Localization.Away (algebraMap R S r) :=
    (Algebra.TensorProduct.comm R _ _).trans e₀
  have : Localization.awayMap (algebraMap R S) r =
      e.toRingHom.comp (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] S)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext x
    simp [e, Localization.awayMap, IsLocalization.Away.map, ← IsScalarTower.algebraMap_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [this]
  exact hPi.left _ _ hf

/-- Étaleness is local on the base for basic open covers. -/
lemma etale_of_exists_of_isPrime {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.Etale (Localization.Away r) (Localization.Away r ⊗[R] S)) :
    Algebra.Etale R S := by
  simp_rw [← RingHom.etale_algebraMap] at H ⊢
  apply ofLocalizationSpan_of_exists_of_isPrime' RingHom.Etale.ofLocalizationSpan
  · exact RingHom.Etale.respectsIso
  · intro p hp
    obtain ⟨r, hr, hf⟩ := H p
    use r, hr

/-- Module finiteness is local on the base for basic open covers. -/
lemma finite_of_exists_of_isPrime {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] S)) :
    Module.Finite R S := by
  simp_rw [← RingHom.finite_algebraMap] at H ⊢
  apply ofLocalizationSpan_of_exists_of_isPrime' RingHom.finite_ofLocalizationSpan
  · exact RingHom.finite_respectsIso
  · intro p hp
    obtain ⟨r, hr, h⟩ := H p
    use r, hr

/-- Finiteness together with étaleness is local on the base for basic open covers. -/
lemma finite_and_etale_of_exists_of_isPrime {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] S) ∧
        Algebra.Etale (Localization.Away r) (Localization.Away r ⊗[R] S)) :
    Module.Finite R S ∧ Algebra.Etale R S := by
  refine ⟨finite_of_exists_of_isPrime fun p hp ↦ ?_, etale_of_exists_of_isPrime fun p hp ↦ ?_⟩
  · obtain ⟨r, hr, hf⟩ := H p
    exact ⟨r, hr, hf.1⟩
  · obtain ⟨r, hr, hf⟩ := H p
    exact ⟨r, hr, hf.2⟩

/-- Finiteness together with étaleness is transported along algebra equivalences. -/
lemma finite_and_etale_of_equiv {R S S' : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S')
    (h : Module.Finite R S ∧ Algebra.Etale R S) :
    Module.Finite R S' ∧ Algebra.Etale R S' := by
  obtain ⟨h₁, h₂⟩ := h
  exact ⟨Module.Finite.equiv e.toLinearEquiv, Algebra.Etale.of_equiv e⟩

/-- Finiteness together with étaleness descends along faithfully flat base change. -/
lemma finite_and_etale_of_tensorProduct_of_faithfullyFlat {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    (h : Module.Finite T (T ⊗[R] S) ∧ Algebra.Etale T (T ⊗[R] S)) :
    Module.Finite R S ∧ Algebra.Etale R S := by
  obtain ⟨h₁, h₂⟩ := h
  exact ⟨.of_finite_tensorProduct_of_faithfullyFlat T,
    .of_etale_tensorProduct_of_faithfullyFlat T⟩

end Basic

attribute [local instance] Module.FinitePresentation.of_finite_of_finitePresentation

section

open Localization in
/-- If two maps out of a finite algebra agree after localizing at `S`, they agree
after base change to `R_r` for some `r ∈ S`. -/
lemma exists_cover_eq_of_eq {R A B : Type*} [CommRing R] (S : Submonoid R)
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Finite R A]
    (Rₚ : Type*) (Aₚ Bₚ : Type u) [CommRing Rₚ] [CommRing Aₚ] [CommRing Bₚ]
    [Algebra R Rₚ] [Algebra R Aₚ] [Algebra R Bₚ] [Algebra Rₚ Aₚ] [Algebra Rₚ Bₚ]
    [Algebra A Aₚ] [Algebra B Bₚ]
    [IsScalarTower R A Aₚ] [IsScalarTower R B Bₚ] [IsScalarTower R Rₚ Aₚ] [IsScalarTower R Rₚ Bₚ]
    [IsLocalization S Rₚ] [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₚ]
    [IsLocalization (Algebra.algebraMapSubmonoid B S) Bₚ]
    (f g : A →ₐ[R] B) (hf : IsLocalization.mapₐ S Rₚ Aₚ Bₚ f = IsLocalization.mapₐ S Rₚ Aₚ Bₚ g) :
    ∃ (r : S),
      Algebra.TensorProduct.map (.id (Away r.val) (Away r.val)) f =
        Algebra.TensorProduct.map (.id (Away r.val) (Away r.val)) g := by
  let u : B →ₗ[R] Bₚ := (IsScalarTower.toAlgHom R B Bₚ).toLinearMap
  have : IsLocalizedModule S u := by
    simp only [u]
    rw [isLocalizedModule_iff_isLocalization]
    infer_instance
  obtain ⟨s, hs⟩ := by
    refine Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S
      (N := B) (N' := Bₚ) (M := A) u f g ?_
    ext x
    change algebraMap B Bₚ (f x) = algebraMap B Bₚ (g x)
    simpa using DFunLike.congr_fun hf (algebraMap A Aₚ x)
  use s
  ext a
  simp only [Algebra.TensorProduct.map_restrictScalars_comp_includeRight, AlgHom.coe_comp,
    Function.comp_apply, Algebra.TensorProduct.includeRight_apply]
  have hun : IsUnit ((algebraMap R (Away s.val ⊗[R] B) s)) := by
    rw [IsScalarTower.algebraMap_apply R (Away s.val) _]
    apply (IsLocalization.Away.algebraMap_isUnit s.val).map
  suffices s.val • ((1 : Away s.val) ⊗ₜ[R] f a) = s.val • (1 ⊗ₜ[R] g a) by
    apply hun.mul_left_cancel
    rwa [← Algebra.smul_def, ← Algebra.smul_def]
  have := DFunLike.congr_fun hs a
  simp only [Submonoid.smul_def, LinearMap.smul_apply] at this
  rw [← TensorProduct.tmul_smul]
  rw [← TensorProduct.tmul_smul]
  exact congrArg (fun b : B ↦ (1 : Away s.val) ⊗ₜ[R] b) this

end

section Equalizer

/-- Transports equalizers along algebra equivalences that intertwine both defining maps. -/
def equalizerCongr {R A A' B B' : Type*} [CommSemiring R]
    [Semiring A] [Semiring A'] [Semiring B] [Semiring B']
    [Algebra R A] [Algebra R A'] [Algebra R B] [Algebra R B']
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B')
    {f g : A →ₐ[R] B} {f' g' : A' →ₐ[R] B'}
    (hf : eB.toAlgHom.comp f = f'.comp eA) (hg : eB.toAlgHom.comp g = g'.comp eA) :
    AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' :=
  AlgEquiv.ofAlgHom
    (AlgHom.codRestrict (eA.toAlgHom.comp (AlgHom.equalizer f g).val) _ <| by
      intro x
      simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Subalgebra.coe_val,
        Function.comp_apply, AlgHom.mem_equalizer]
      rw [← hf', x.2, hg'])
    (AlgHom.codRestrict (eA.symm.toAlgHom.comp (AlgHom.equalizer f' g').val) _ <| by
      intro x
      simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Subalgebra.coe_val,
        Function.comp_apply, AlgHom.mem_equalizer]
      apply eB.injective
      rw [hf', hg', AlgEquiv.apply_symm_apply, x.2])
    (by ext x; exact eA.apply_symm_apply x)
    (by ext x; exact eA.symm_apply_apply x)
   where
    hf' (x) : eB (f x) = f' (eA x) := DFunLike.congr_fun hf x
    hg' (x) : eB (g x) = g' (eA x) := DFunLike.congr_fun hg x

/-- Identifies equalizers when both defining algebra homomorphisms are equal. -/
def equalizerCongrOfEq {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] {f g f' g' : A →ₐ[R] B}
    (hf : f = f') (hg : g = g') :
    AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' :=
  equalizerCongr AlgEquiv.refl AlgEquiv.refl
    (by subst hf; ext x; rfl) (by subst hg; ext x; rfl)

end Equalizer

section rankAtStalk

/-- Every prime has a basic open neighbourhood on which the rank function of a
finitely presented flat algebra is constant. -/
lemma exists_cover_rankAtStalk_eq {R : Type*} (S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FinitePresentation R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p,
      Module.rankAtStalk (R := Localization.Away r) (Localization.Away r ⊗[R] S) =
        Module.rankAtStalk S ⟨p, inferInstance⟩ := by
  obtain ⟨U, hU, hp, heq⟩ := (Module.isLocallyConstant_rankAtStalk (M := S)).exists_open ⟨p, ‹_›⟩
  obtain ⟨V, ⟨r, rfl⟩, (hr : r ∉ p), hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hU
  refine ⟨r, hr, ?_⟩
  ext q
  rw [Module.rankAtStalk_baseChange]
  apply heq
  apply hrU
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.mem_compl_iff,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff,
    SetLike.mem_coe]
  obtain ⟨-, b⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint (.powers r) _ q.asIdeal).mp q.2
  rw [Set.disjoint_left] at b
  simp only [SetLike.mem_coe, Ideal.coe_comap, Set.mem_preimage] at b
  apply b
  exact ⟨1, pow_one r⟩

end rankAtStalk

section

variable {E F : Type*}

/-- Precomposition with `σ` as an `R`-algebra homomorphism between function algebras. -/
@[simps!]
def compRight (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (σ : E → F) :
    (F → S) →ₐ[R] E → S :=
  AlgHom.pi (fun f ↦ Pi.evalAlgHom R _ (σ f))

lemma finite_coequalizer [Finite F] (σ τ : E → F) : Finite (Function.Coequalizer σ τ) :=
  Finite.of_surjective _ (Function.Coequalizer.mk_surjective σ τ)

attribute [local instance] finite_coequalizer

/-- Identifies functions equal after precomposition by `σ` and `τ` with functions
on their coequalizer. -/
def equalizerCompRightEquiv (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (σ τ : E → F) :
    AlgHom.equalizer (compRight R S σ) (compRight R S τ) ≃ₐ[R]
      Function.Coequalizer σ τ → S :=
  AlgEquiv.ofAlgHom
    (AlgHom.pi (Function.Coequalizer.desc σ τ
      (fun f ↦ (Pi.evalAlgHom R (fun _ ↦ S) f).comp
        (AlgHom.equalizer (compRight R S σ) (compRight R S τ)).val)
        (by ext f ⟨x, hx⟩; exact congrFun hx f)))
    (AlgHom.codRestrict (compRight _ _ (Function.Coequalizer.mk _ _))
      (AlgHom.equalizer _ _)
      (fun x ↦ by ext e; simp only [compRight_apply]; rw [Function.Coequalizer.condition]))
    (by
      ext f x
      obtain ⟨x, rfl⟩ := Function.Coequalizer.mk_surjective _ _ x
      rfl)
    (by ext f x; rfl)

lemma isFiniteSplit_equalizer_compRight (R : Type*) [CommRing R] [Finite E] [Finite F]
    (σ τ : E → F) :
    Algebra.IsFiniteSplit R
      (AlgHom.equalizer (compRight R R σ) (compRight R R τ)) :=
  Algebra.IsFiniteSplit.of_algEquiv (equalizerCompRightEquiv R R σ τ).symm

attribute [local instance] isFiniteSplit_equalizer_compRight

/-- If `R` has no nontrivial idempotents, every `R`-algebra map between finite
function algebras with nonempty source index is a coordinate map. -/
lemma eq_compRight_of_no_nontrivial_isIdempotentElem {R E F : Type*} [_root_.Finite E]
    [Nonempty E] [CommRing R] (H : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (f : (E → R) →ₐ[R] F → R) : ∃ (σ : F → E), f = compRight R R σ := by
  nontriviality R
  cases nonempty_fintype E
  classical
  have hor (i) (j) : f (Pi.single j 1) i = 0 ∨ f (Pi.single j 1) i = 1 := by
    apply H
    unfold IsIdempotentElem
    rw [← Pi.mul_apply, ← map_mul, ← Pi.single_mul_left]
    simp only [Pi.single_eq_same, one_mul]
  have (x : F) : ∃ (y : E), f (Pi.single y 1) x = 1 := by
    by_contra! hc
    replace hc (y : E) : f (Pi.single y 1) x = 0 := by
      obtain (h|h) := hor x y
      · assumption
      · simp [hc] at h
    have : 1 = ∑ y : E, f (Pi.single y 1) x := by
      rw [← Fintype.sum_apply]
      rw [← map_sum, Finset.univ_sum_single, ← Pi.one_def, map_one, Pi.one_apply]
    simp_rw [hc] at this
    exact one_ne_zero (by simpa only [Finset.sum_const_zero] using this)
  have (x : F) : ∃! (y : E), f (Pi.single y 1) x = 1 := by
    apply existsUnique_of_exists_of_unique
    · exact this x
    · intro a b ha hb
      by_contra! h
      have : (Pi.single a 1) * (Pi.single b 1 : E → R) = 0 := by
        simp [← Pi.single_mul_left, h]
      apply_fun ((f ·) · x) at this
      simp [ha, hb] at this
  choose σ hσ hun using this
  use σ
  ext x i
  induction x using Pi.single_induction with
  | zero => simp only [map_zero, Pi.zero_apply, compRight_apply]
  | add x y hx hy => simp [hx, hy]
  | single j r =>
      have : Pi.single j r = r • (Pi.single j 1 : E → R) := by simp [← Pi.single_smul]
      rw [this]
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, compRight_apply]
      congr
      obtain (h|h) := hor i j
      · have : j ≠ σ i := by
          intro hj
          subst hj
          simp [hσ] at h
        simp [this, h]
      · have := hun i j h
        subst this
        simp [hσ]

/-- The previous lemma, allowing an empty source index over a nontrivial ring. -/
lemma eq_compRight_of_no_nontrivial_isIdempotentElem' {R E F : Type*} [_root_.Finite E]
    [CommRing R] [Nontrivial R] (H : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (f : (E → R) →ₐ[R] F → R) : ∃ (σ : F → E), f = compRight R R σ := by
  cases isEmpty_or_nonempty E
  · have : Subsingleton (F → R) := f.codomain_trivial
    cases isEmpty_or_nonempty F
    · use default
      apply Subsingleton.elim
    · simpa using false_of_nontrivial_of_subsingleton (F → R)
  · apply eq_compRight_of_no_nontrivial_isIdempotentElem H

/-- A local ring has no nontrivial idempotents. -/
lemma isIdempotentElem_iff_eq_zero_or_eq_one_of_isLocalRing {R : Type*} [CommRing R]
    [IsLocalRing R] {e : R} : IsIdempotentElem e ↔ e = 0 ∨ e = 1 := by
  refine ⟨fun he ↦ ?_, ?_⟩
  · obtain (h|h) := IsLocalRing.isUnit_or_isUnit_one_sub_self e
    · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit h).mp he)
    · exact Or.inl
        (sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit h).mp he.one_sub))
  · rintro (h|h) <;> subst h
    · exact IsIdempotentElem.zero
    · exact IsIdempotentElem.one

/-- Over a local ring, every algebra map between finite function algebras is a
coordinate map. -/
lemma eq_compRight_of_isLocalRing {R E F : Type*} [_root_.Finite E] [CommRing R]
    (f : (E → R) →ₐ[R] F → R) [IsLocalRing R] :
    ∃ (σ : F → E), f = compRight R R σ := by
  apply eq_compRight_of_no_nontrivial_isIdempotentElem'
  intro e he
  rwa [isIdempotentElem_iff_eq_zero_or_eq_one_of_isLocalRing] at he

open Localization in
/-- Locally around every prime, an algebra map between finite function algebras
is a coordinate map. -/
lemma exists_cover_eq_compRight {R : Type*} {E F : Type u}
    [_root_.Finite E] [_root_.Finite F]
    [CommRing R]
    (f : (E → R) →ₐ[R] F → R) (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ (σ : F → E),
      Algebra.TensorProduct.map (.id (Away r) (Away r)) f =
        Algebra.TensorProduct.map (.id (Away r) (Away r)) (compRight _ _ σ) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (E → R) p.primeCompl)
      (E → Localization.AtPrime p) := by
    rw [← isLocalizedModule_iff_isLocalization]
    convert IsLocalizedModule.pi p.primeCompl
      (fun _ ↦ Algebra.linearMap R (Localization.AtPrime p))
    all_goals first | rfl | infer_instance
  have : IsLocalization (Algebra.algebraMapSubmonoid (F → R) p.primeCompl)
      (F → Localization.AtPrime p) := by
    rw [← isLocalizedModule_iff_isLocalization]
    convert IsLocalizedModule.pi p.primeCompl
      (fun _ ↦ Algebra.linearMap R (Localization.AtPrime p))
    all_goals first | rfl | infer_instance
  let fₚ : (E → Localization.AtPrime p) →ₐ[Localization.AtPrime p] F → Localization.AtPrime p :=
    IsLocalization.mapₐ p.primeCompl (Localization.AtPrime p)
      (E → Localization.AtPrime p)
      (F → Localization.AtPrime p) f
  obtain ⟨σ, hσ⟩ := eq_compRight_of_isLocalRing fₚ
  let gₚ : (E → Localization.AtPrime p) →ₐ[Localization.AtPrime p] F → Localization.AtPrime p :=
    IsLocalization.mapₐ p.primeCompl (Localization.AtPrime p)
      (E → Localization.AtPrime p)
      (F → Localization.AtPrime p) (compRight R R σ)
  have : fₚ = gₚ := by
    rw [hσ]
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (E → R) p.primeCompl)
    ext x i
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      compRight_apply, IsLocalization.mapₐ_coe, IsLocalization.map_eq, gₚ]
    rfl
  obtain ⟨⟨r, hr⟩, heq⟩ := exists_cover_eq_of_eq _ _ _ _ f (compRight R R σ) this
  exact ⟨r, hr, σ, heq⟩

open Localization in
/-- Locally around every prime, two algebra maps between finite function algebras
are simultaneously coordinate maps. -/
lemma exists_cover_eq_compRight₂ {R : Type*} {E F : Type u}
    [_root_.Finite E] [_root_.Finite F] [CommRing R] (f g : (E → R) →ₐ[R] F → R)
    (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ (σ τ : F → E),
      Algebra.TensorProduct.map (.id (Away r) (Away r)) f =
        Algebra.TensorProduct.map (.id (Away r) (Away r)) (compRight _ _ σ) ∧
      Algebra.TensorProduct.map (.id (Away r) (Away r)) g =
        Algebra.TensorProduct.map (.id (Away r) (Away r)) (compRight _ _ τ) := by
  obtain ⟨r, hr, σ, hσ⟩ := exists_cover_eq_compRight f p
  obtain ⟨r', hr', τ, hτ⟩ := exists_cover_eq_compRight g p
  let : Algebra (Localization.Away r) (Localization.Away (r * r')) := by
    refine (IsLocalization.Away.lift r (g := algebraMap R _) ?_).toAlgebra
    apply isUnit_of_mul_isUnit_left (y := algebraMap _ _ r')
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (r * r')
  let : Algebra (Localization.Away r') (Localization.Away (r * r')) := by
    refine (IsLocalization.Away.lift r' (g := algebraMap R _) ?_).toAlgebra
    apply isUnit_of_mul_isUnit_right (x := algebraMap _ _ r)
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (r * r')
  have : IsScalarTower R (Away r) (Localization.Away (r * r')) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower R (Away r') (Localization.Away (r * r')) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp [RingHom.algebraMap_toAlgebra]
  let eE : Localization.Away (r * r') ⊗[R] (E → R) ≃ₐ[Localization.Away (r * r')]
      Localization.Away (r * r') ⊗[Away r] (Localization.Away r ⊗[R] (E → R)) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  let eF : Localization.Away (r * r') ⊗[R] (F → R) ≃ₐ[Localization.Away (r * r')]
      Localization.Away (r * r') ⊗[Away r] (Localization.Away r ⊗[R] (F → R)) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  let eE' : Localization.Away (r * r') ⊗[R] (E → R) ≃ₐ[Localization.Away (r * r')]
      Localization.Away (r * r') ⊗[Away r'] (Localization.Away r' ⊗[R] (E → R)) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  let eF' : Localization.Away (r * r') ⊗[R] (F → R) ≃ₐ[Localization.Away (r * r')]
      Localization.Away (r * r') ⊗[Away r'] (Localization.Away r' ⊗[R] (F → R)) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  have heq (u : (E → R) →ₐ[R] F → R) : Algebra.TensorProduct.map
      (AlgHom.id (Away (r * r')) (Away (r * r'))) u =
      eF.symm.toAlgHom.comp ((Algebra.TensorProduct.map (.id _ _)
        (Algebra.TensorProduct.map (.id _ _) u)).comp eE.toAlgHom) := by
    ext
    simp [eF, eE]
  have heq' (u : (E → R) →ₐ[R] F → R) : Algebra.TensorProduct.map
      (AlgHom.id (Away (r * r')) (Away (r * r'))) u =
      eF'.symm.toAlgHom.comp ((Algebra.TensorProduct.map (.id _ _)
        (Algebra.TensorProduct.map (.id _ _) u)).comp eE'.toAlgHom) := by
    ext
    simp [eF', eE']
  refine ⟨r * r', ?_, σ, τ, ?_, ?_⟩
  · intro hr
    cases Ideal.IsPrime.mem_or_mem inferInstance hr <;> contradiction
  · rw [heq, hσ, ← heq]
  · rw [heq', hτ, ← heq']

end

/-- The equalizer of two algebra maps between finite function algebras is finite
and étale. -/
lemma finite_and_etale_equalizer_fun {R : Type u} {E F : Type} [CommRing R]
    [Finite E] [Finite F] (f g : (E → R) →ₐ[R] (F → R)) :
    Module.Finite R (AlgHom.equalizer f g) ∧ Algebra.Etale R (AlgHom.equalizer f g) := by
  apply finite_and_etale_of_exists_of_isPrime
  intro p hp
  obtain ⟨r, hr, σ, τ, hσ, hτ⟩ := exists_cover_eq_compRight₂ f g p
  use r, hr
  set A := Localization.Away r
  let f' : A ⊗[R] (E → R) →ₐ[A] A ⊗[R] (F → R) := Algebra.TensorProduct.map (.id _ _) f
  let g' : A ⊗[R] (E → R) →ₐ[A] A ⊗[R] (F → R) := Algebra.TensorProduct.map (.id _ _) g
  let cong₁ : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
    AlgHom.tensorEqualizerEquiv A A f g
  let T := AlgHom.equalizer
    (Algebra.TensorProduct.map (.id A A) (compRight R R σ))
    (Algebra.TensorProduct.map (.id A A) (compRight R R τ))
  let cong₂ : AlgHom.equalizer f' g' ≃ₐ[A] T := equalizerCongrOfEq hσ hτ
  let cong₃ : T ≃ₐ[A] A ⊗[R] AlgHom.equalizer (compRight R R σ) (compRight R R τ) :=
    (AlgHom.tensorEqualizerEquiv A A _ _).symm
  let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] A ⊗[R]
      AlgHom.equalizer (compRight R R σ) (compRight R R τ) :=
    cong₁.trans (cong₂.trans cong₃)
  have := isFiniteSplit_equalizer_compRight R σ τ
  have : Algebra.IsFiniteSplit A
      (A ⊗[R] ↥(AlgHom.equalizer (compRight R R σ) (compRight R R τ))) :=
    inferInstance
  exact finite_and_etale_of_equiv cong.symm ⟨inferInstance, inferInstance⟩

/-- The equalizer of two algebra maps between finite split algebras is finite
and étale. -/
lemma finite_and_etale_equalizer_of_isFiniteSplit {R S T : Type u} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra.IsFiniteSplit R S] [Algebra.IsFiniteSplit R T] (f g : S →ₐ[R] T) :
    Module.Finite R (AlgHom.equalizer f g) ∧ Algebra.Etale R (AlgHom.equalizer f g) := by
  obtain ⟨n, ⟨eS⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R S
  obtain ⟨m, ⟨eT⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R T
  let f' : (Fin n → R) →ₐ[R] Fin m → R := eT.toAlgHom.comp (f.comp eS.symm)
  let g' : (Fin n → R) →ₐ[R] Fin m → R := eT.toAlgHom.comp (g.comp eS.symm)
  let cong : AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' :=
    equalizerCongr eS eT (by ext; simp [f']) (by ext; simp [g'])
  exact finite_and_etale_of_equiv cong.symm (finite_and_etale_equalizer_fun f' g')

/-- The equalizer of two algebra maps between finite étale algebras of constant
ranks is finite and étale. -/
lemma finite_and_etale_equalizer_of_rankAtStalk_eq {R S T : Type u} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Module.Finite R S] [Module.Finite R T] [Algebra.Etale R S] [Algebra.Etale R T]
    {n m : ℕ} (hn : Module.rankAtStalk (R := R) S = n) (hm : Module.rankAtStalk (R := R) T = m)
    (f g : S →ₐ[R] T) :
    Module.Finite R (AlgHom.equalizer f g) ∧ Algebra.Etale R (AlgHom.equalizer f g) := by
  wlog hS : Algebra.IsFiniteSplit R S
  · obtain ⟨A, _, _, _, _, _, hA⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hn
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Module.Finite A (AlgHom.equalizer f' g') ∧
        Algebra.Etale A (AlgHom.equalizer f' g') := by
      apply this (n := n) (m := m)
      · ext p
        rw [Module.rankAtStalk_baseChange, hn]
        rfl
      · ext p
        rw [Module.rankAtStalk_baseChange, hm]
        rfl
      exact hA
    exact finite_and_etale_of_tensorProduct_of_faithfullyFlat A
      (finite_and_etale_of_equiv cong.symm this)
  clear n hn
  wlog hT : Algebra.IsFiniteSplit R T
  · obtain ⟨A, _, _, _, _, _, hA⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hm
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Module.Finite A (AlgHom.equalizer f' g') ∧
        Algebra.Etale A (AlgHom.equalizer f' g') := by
      apply this (m := m)
      · ext p
        rw [Module.rankAtStalk_baseChange, hm]
        rfl
      · infer_instance
      · exact hA
    exact finite_and_etale_of_tensorProduct_of_faithfullyFlat A
      (finite_and_etale_of_equiv cong.symm this)
  exact finite_and_etale_equalizer_of_isFiniteSplit f g

/-- The equalizer of two algebra maps between finite étale algebras is finite and
étale. This is the conjunction form of NYLL's `Algebra.Etale.equalizer`. -/
theorem finite_and_etale_equalizer {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [Module.Finite R S] [Module.Finite R T] [Algebra.Etale R S] [Algebra.Etale R T]
    (f g : S →ₐ[R] T) :
    Module.Finite R (AlgHom.equalizer f g) ∧ Algebra.Etale R (AlgHom.equalizer f g) := by
  wlog h : ∃ (n : ℕ), Module.rankAtStalk (R := R) S = n
  · apply finite_and_etale_of_exists_of_isPrime
    intro p hp
    obtain ⟨r, hr, hn⟩ := exists_cover_rankAtStalk_eq S p
    use r, hr
    let A := Localization.Away r
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Module.Finite A (AlgHom.equalizer f' g') ∧
        Algebra.Etale A (AlgHom.equalizer f' g') := by
      apply this
      use Module.rankAtStalk S ⟨p, hp⟩
    exact finite_and_etale_of_equiv (S := AlgHom.equalizer f' g') cong.symm this
  obtain ⟨n, hn⟩ := h
  wlog h : ∃ (m : ℕ), Module.rankAtStalk (R := R) T = m
  · apply finite_and_etale_of_exists_of_isPrime
    intro p hp
    obtain ⟨r, hr, hm⟩ := exists_cover_rankAtStalk_eq T p
    use r, hr
    let A := Localization.Away r
    let f' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) f
    let g' : A ⊗[R] S →ₐ[A] A ⊗[R] T := Algebra.TensorProduct.map (AlgHom.id _ _) g
    let cong : A ⊗[R] AlgHom.equalizer f g ≃ₐ[A] AlgHom.equalizer f' g' :=
      AlgHom.tensorEqualizerEquiv A A f g
    have : Module.Finite A (AlgHom.equalizer f' g') ∧
        Algebra.Etale A (AlgHom.equalizer f' g') := by
      apply this (n := n)
      · ext p
        rw [Module.rankAtStalk_baseChange, hn]
        rfl
      · use (Module.rankAtStalk T ⟨p, hp⟩)
    exact finite_and_etale_of_equiv (S := AlgHom.equalizer f' g') cong.symm this
  obtain ⟨m, hm⟩ := h
  exact finite_and_etale_equalizer_of_rankAtStalk_eq hn hm f g

end EqualizerAlgebra

/-- The published equalizer proposition holds: the equalizer subalgebra of two
`R`-algebra maps between finite étale `R`-algebras is finite and étale over `R`. -/
theorem equalizerAlgebraFiniteEtale (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Module.Finite R A] [Module.Finite R B]
    [Algebra.Etale R A] [Algebra.Etale R B]
    (f g : A →ₐ[R] B) :
    EqualizerAlgebraFiniteEtale R A B f g :=
  EqualizerAlgebra.finite_and_etale_equalizer f g

end Langlands.AlgebraicGeometry.FiniteEtale
