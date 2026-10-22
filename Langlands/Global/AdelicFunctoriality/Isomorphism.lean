import Langlands.Global.AdelicFunctoriality.Infinite
import Langlands.Global.AdelicFunctoriality.Finite
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Units

/-! # Number-field isomorphisms on adeles, ideles and idele classes -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain
open scoped NumberField

universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
  [Field K] [Field L] [Field M] [NumberField K] [NumberField L] [NumberField M]

/-- Arithmetic ring transport on full adeles, using the actual infinite and finite factors. -/
def adeleEquiv (e : K ≃+* L) : AdeleRing (𝓞 K) K ≃+* AdeleRing (𝓞 L) L :=
  RingEquiv.prodCongr (infiniteAdeleEquiv e) (finiteAdeleEquiv e)

theorem continuous_adeleEquiv (e : K ≃+* L) : Continuous (adeleEquiv e) :=
  ((continuous_infiniteAdeleEquiv e).comp continuous_fst).prodMk
    ((continuous_finiteAdeleEquiv e).comp continuous_snd)

theorem continuous_adeleEquiv_symm (e : K ≃+* L) : Continuous (adeleEquiv e).symm :=
  ((continuous_infiniteAdeleEquiv_symm e).comp continuous_fst).prodMk
    ((continuous_finiteAdeleEquiv_symm e).comp continuous_snd)

def adeleHomeomorph (e : K ≃+* L) : AdeleRing (𝓞 K) K ≃ₜ AdeleRing (𝓞 L) L where
  __ := (adeleEquiv e).toEquiv
  continuous_toFun := continuous_adeleEquiv e
  continuous_invFun := continuous_adeleEquiv_symm e

def adeleContinuousMulEquiv (e : K ≃+* L) :
    AdeleRing (𝓞 K) K ≃ₜ* AdeleRing (𝓞 L) L where
  __ := (adeleEquiv e).toMulEquiv
  continuous_toFun := continuous_adeleEquiv e
  continuous_invFun := continuous_adeleEquiv_symm e

@[simp] theorem adeleEquiv_infinite_apply (e : K ≃+* L) (x : AdeleRing (𝓞 K) K)
    (p : InfinitePlace L) :
    (adeleEquiv e x).1 p =
      infiniteCompletionEquiv e p (x.1 (infinitePlaceEquiv e p)) := rfl

@[simp] theorem adeleEquiv_finite_apply (e : K ≃+* L) (x : AdeleRing (𝓞 K) K)
    (p : HeightOneSpectrum (𝓞 L)) :
    (adeleEquiv e x).2 p =
      finiteCompletionEquiv e p (x.2 (finitePlaceEquiv e p)) := rfl

@[simp] theorem adeleEquiv_diagonal (e : K ≃+* L) (x : K) :
    adeleEquiv e (algebraMap K (AdeleRing (𝓞 K) K) x) =
      algebraMap L (AdeleRing (𝓞 L) L) (e x) :=
  Prod.ext (infiniteAdeleEquiv_diagonal e x) (finiteAdeleEquiv_diagonal e x)

@[simp] theorem adeleEquiv_refl :
    adeleEquiv (RingEquiv.refl K) = RingEquiv.refl (AdeleRing (𝓞 K) K) := by
  apply RingEquiv.ext
  intro x
  exact Prod.ext
    (RingEquiv.congr_fun infiniteAdeleEquiv_refl x.1)
    (RingEquiv.congr_fun finiteAdeleEquiv_refl x.2)

theorem adeleEquiv_trans (e : K ≃+* L) (f : L ≃+* M) :
    adeleEquiv (e.trans f) = (adeleEquiv e).trans (adeleEquiv f) := by
  apply RingEquiv.ext
  intro x
  exact Prod.ext
    (RingEquiv.congr_fun (infiniteAdeleEquiv_trans e f) x.1)
    (RingEquiv.congr_fun (finiteAdeleEquiv_trans e f) x.2)

theorem adeleEquiv_ofCompletion (e : K ≃+* L) (p : InfinitePlace L)
    (x : (infinitePlaceEquiv e p).Completion) :
    adeleEquiv e (AdeleRing.ofCompletion (𝓞 K) K (infinitePlaceEquiv e p) x) =
      AdeleRing.ofCompletion (𝓞 L) L p (infiniteCompletionEquiv e p x) := by
  classical
  apply Prod.ext
  · funext q
    change infiniteCompletionEquiv e q
      (Pi.mulSingle (infinitePlaceEquiv e p) x (infinitePlaceEquiv e q)) =
      Pi.mulSingle p (infiniteCompletionEquiv e p x) q
    by_cases h : q = p
    · subst q
      simp
    · have h' : infinitePlaceEquiv e q ≠ infinitePlaceEquiv e p :=
        (infinitePlaceEquiv e).injective.ne h
      simp [h, h']
      exact map_one (infiniteCompletionEquiv e q)
  · exact map_one (finiteAdeleEquiv e)

theorem adeleEquiv_ofAdicCompletion (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L))
    (x : (finitePlaceEquiv e p).adicCompletion K) :
    adeleEquiv e (AdeleRing.ofAdicCompletion (𝓞 K) K (finitePlaceEquiv e p) x) =
      AdeleRing.ofAdicCompletion (𝓞 L) L p (finiteCompletionEquiv e p x) := by
  classical
  apply Prod.ext
  · exact map_one (infiniteAdeleEquiv e)
  · apply FiniteAdeleRing.ext
    intro q
    change finiteCompletionEquiv e q
      (Pi.mulSingle (finitePlaceEquiv e p) x (finitePlaceEquiv e q)) =
      Pi.mulSingle p (finiteCompletionEquiv e p x) q
    by_cases h : q = p
    · subst q
      simp
    · have h' : finitePlaceEquiv e q ≠ finitePlaceEquiv e p :=
        (finitePlaceEquiv e).injective.ne h
      simp [h, h']

/-- The induced isomorphism uses the units topology on the actual adele ring. -/
def ideleEquiv (e : K ≃+* L) : IdeleGroup (𝓞 K) K ≃ₜ* IdeleGroup (𝓞 L) L :=
  Units.mapContinuousMulEquiv (adeleContinuousMulEquiv e)

@[simp] theorem ideleEquiv_val (e : K ≃+* L) (x : IdeleGroup (𝓞 K) K) :
    (ideleEquiv e x : AdeleRing (𝓞 L) L) = adeleEquiv e x := rfl

@[simp] theorem ideleEquiv_diagonal (e : K ≃+* L) (x : Kˣ) :
    ideleEquiv e (IdeleGroup.unitEmbedding (𝓞 K) K x) =
      IdeleGroup.unitEmbedding (𝓞 L) L (Units.mapEquiv e.toMulEquiv x) := by
  apply Units.ext
  exact adeleEquiv_diagonal e x

@[simp] theorem ideleEquiv_refl :
    ideleEquiv (RingEquiv.refl K) = ContinuousMulEquiv.refl (IdeleGroup (𝓞 K) K) := by
  apply ContinuousMulEquiv.ext
  intro x
  apply Units.ext
  exact RingEquiv.congr_fun adeleEquiv_refl x.val

theorem ideleEquiv_trans (e : K ≃+* L) (f : L ≃+* M) :
    ideleEquiv (e.trans f) = (ideleEquiv e).trans (ideleEquiv f) := by
  apply ContinuousMulEquiv.ext
  intro x
  apply Units.ext
  exact RingEquiv.congr_fun (adeleEquiv_trans e f) x.val

theorem ideleEquiv_ofCompletion (e : K ≃+* L) (p : InfinitePlace L)
    (x : (infinitePlaceEquiv e p).Completionˣ) :
    ideleEquiv e (IdeleGroup.ofCompletion (𝓞 K) K (infinitePlaceEquiv e p) x) =
      IdeleGroup.ofCompletion (𝓞 L) L p
        (Units.mapEquiv (infiniteCompletionEquiv e p).toMulEquiv x) := by
  apply Units.ext
  exact adeleEquiv_ofCompletion e p x

theorem ideleEquiv_ofAdicCompletion (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L))
    (x : ((finitePlaceEquiv e p).adicCompletion K)ˣ) :
    ideleEquiv e (IdeleGroup.ofAdicCompletion (𝓞 K) K (finitePlaceEquiv e p) x) =
      IdeleGroup.ofAdicCompletion (𝓞 L) L p
        (Units.mapEquiv (finiteCompletionEquiv e p).toMulEquiv x) := by
  apply Units.ext
  exact adeleEquiv_ofAdicCompletion e p x

/-- Principal ideles are transported onto principal ideles, by the field isomorphism itself. -/
theorem ideleEquiv_principal (e : K ≃+* L) :
    (IdeleGroup.principalSubgroup (𝓞 K) K).map (ideleEquiv e).toMonoidHom =
      IdeleGroup.principalSubgroup (𝓞 L) L := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨Units.mapEquiv e.toMulEquiv a, (ideleEquiv_diagonal e a).symm⟩
  · rintro _ ⟨b, rfl⟩
    refine ⟨IdeleGroup.unitEmbedding (𝓞 K) K (Units.mapEquiv e.toMulEquiv.symm b),
      ⟨_, rfl⟩, ?_⟩
    change ideleEquiv e
      (IdeleGroup.unitEmbedding (𝓞 K) K (Units.mapEquiv e.toMulEquiv.symm b)) =
      IdeleGroup.unitEmbedding (𝓞 L) L b
    rw [ideleEquiv_diagonal]
    congr 1
    exact (Units.mapEquiv e.toMulEquiv).apply_symm_apply b

/-- Quotient transport on the genuine principal-idele quotient, with its quotient topology. -/
def ideleClassEquiv (e : K ≃+* L) :
    IdeleClassGroup (𝓞 K) K ≃ₜ* IdeleClassGroup (𝓞 L) L where
  __ := QuotientGroup.congr _ _ (ideleEquiv e).toMulEquiv (ideleEquiv_principal e)
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp (ideleEquiv e).continuous
  continuous_invFun := by
    apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp (ideleEquiv e).symm.continuous

@[simp] theorem ideleClassEquiv_mk (e : K ≃+* L) (x : IdeleGroup (𝓞 K) K) :
    ideleClassEquiv e (QuotientGroup.mk x) = QuotientGroup.mk (ideleEquiv e x) := rfl

@[simp] theorem ideleClassEquiv_refl :
    ideleClassEquiv (RingEquiv.refl K) =
      ContinuousMulEquiv.refl (IdeleClassGroup (𝓞 K) K) := by
  apply ContinuousMulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x fun a => ?_
  change QuotientGroup.mk (ideleEquiv (RingEquiv.refl K) a) = QuotientGroup.mk a
  rw [ideleEquiv_refl]
  rfl

theorem ideleClassEquiv_trans (e : K ≃+* L) (f : L ≃+* M) :
    ideleClassEquiv (e.trans f) = (ideleClassEquiv e).trans (ideleClassEquiv f) := by
  apply ContinuousMulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x fun a => ?_
  change QuotientGroup.mk (ideleEquiv (e.trans f) a) =
    QuotientGroup.mk (ideleEquiv f (ideleEquiv e a))
  rw [ideleEquiv_trans]
  rfl

theorem ideleClassEquiv_ofCompletion (e : K ≃+* L) (p : InfinitePlace L)
    (x : (infinitePlaceEquiv e p).Completionˣ) :
    ideleClassEquiv e (IdeleClassGroup.ofCompletion (𝓞 K) K (infinitePlaceEquiv e p) x) =
      IdeleClassGroup.ofCompletion (𝓞 L) L p
        (Units.mapEquiv (infiniteCompletionEquiv e p).toMulEquiv x) :=
  congrArg QuotientGroup.mk (ideleEquiv_ofCompletion e p x)

theorem ideleClassEquiv_ofAdicCompletion (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L))
    (x : ((finitePlaceEquiv e p).adicCompletion K)ˣ) :
    ideleClassEquiv e (IdeleClassGroup.ofAdicCompletion (𝓞 K) K (finitePlaceEquiv e p) x) =
      IdeleClassGroup.ofAdicCompletion (𝓞 L) L p
        (Units.mapEquiv (finiteCompletionEquiv e p).toMulEquiv x) :=
  congrArg QuotientGroup.mk (ideleEquiv_ofAdicCompletion e p x)

/-- The actual number-field automorphism group acts on full adeles. -/
def adeleAut : (K ≃ₐ[ℚ] K) →* (AdeleRing (𝓞 K) K ≃+* AdeleRing (𝓞 K) K) where
  toFun σ := adeleEquiv σ.toRingEquiv
  map_one' := adeleEquiv_refl
  map_mul' σ τ := adeleEquiv_trans τ.toRingEquiv σ.toRingEquiv

/-- The induced action on ideles. -/
def ideleAut : (K ≃ₐ[ℚ] K) →* (IdeleGroup (𝓞 K) K ≃* IdeleGroup (𝓞 K) K) where
  toFun σ := (ideleEquiv σ.toRingEquiv).toMulEquiv
  map_one' := congrArg ContinuousMulEquiv.toMulEquiv ideleEquiv_refl
  map_mul' σ τ := congrArg ContinuousMulEquiv.toMulEquiv
    (ideleEquiv_trans τ.toRingEquiv σ.toRingEquiv)

/-- Action of the actual number-field automorphism group on idele classes. -/
def ideleClassAut :
    (K ≃ₐ[ℚ] K) →* (IdeleClassGroup (𝓞 K) K ≃* IdeleClassGroup (𝓞 K) K) where
  toFun σ := (ideleClassEquiv σ.toRingEquiv).toMulEquiv
  map_one' := congrArg ContinuousMulEquiv.toMulEquiv ideleClassEquiv_refl
  map_mul' σ τ := congrArg ContinuousMulEquiv.toMulEquiv
    (ideleClassEquiv_trans τ.toRingEquiv σ.toRingEquiv)

theorem continuous_ideleClassAut (σ : K ≃ₐ[ℚ] K) : Continuous (ideleClassAut σ) :=
  (ideleClassEquiv σ.toRingEquiv).continuous

/-- The action as an installable instance, without imposing global notation on the quotient. -/
@[instance_reducible]
def ideleClassAction : MulDistribMulAction (K ≃ₐ[ℚ] K) (IdeleClassGroup (𝓞 K) K) where
  __ := MulAction.compHom (IdeleClassGroup (𝓞 K) K) ideleClassAut
  smul_one σ := map_one (ideleClassAut σ)
  smul_mul σ x y := map_mul (ideleClassAut σ) x y

@[simp] theorem ideleClassAut_mk (σ : K ≃ₐ[ℚ] K) (x : IdeleGroup (𝓞 K) K) :
    ideleClassAut σ (QuotientGroup.mk x) =
      QuotientGroup.mk (ideleEquiv σ.toRingEquiv x) := rfl

variable [IsCMField K]

/-- The concrete arithmetic CM involution on the actual idele-class group. -/
def ideleClassComplexConj :
    IdeleClassGroup (𝓞 K) K ≃ₜ* IdeleClassGroup (𝓞 K) K :=
  ideleClassEquiv (IsCMField.complexConj K).toRingEquiv

theorem continuous_ideleClassComplexConj :
    Continuous (ideleClassComplexConj (K := K)) := ideleClassComplexConj.continuous

@[simp] theorem ideleClassComplexConj_mk (x : IdeleGroup (𝓞 K) K) :
    ideleClassComplexConj (QuotientGroup.mk x) =
      QuotientGroup.mk (ideleEquiv (IsCMField.complexConj K).toRingEquiv x) := rfl

theorem ideleComplexConj_infinite_coordinate (x : IdeleGroup (𝓞 K) K)
    (p : InfinitePlace K) :
    InfinitePlace.Completion.extensionEmbedding p
      ((ideleEquiv (IsCMField.complexConj K).toRingEquiv x).val.1 p) =
        star (InfinitePlace.Completion.extensionEmbedding p (x.val.1 p)) :=
  infiniteComplexConj_coordinate p x.val.1

@[simp] theorem ideleClassComplexConj_involutive :
    Function.Involutive (ideleClassComplexConj (K := K)) := by
  have h : (IsCMField.complexConj K).toRingEquiv.trans
      (IsCMField.complexConj K).toRingEquiv = RingEquiv.refl K := by
    ext x
    exact IsCMField.complexConj_apply_apply K x
  intro x
  have hh := ideleClassEquiv_trans (IsCMField.complexConj K).toRingEquiv
    (IsCMField.complexConj K).toRingEquiv
  rw [h, ideleClassEquiv_refl] at hh
  exact (DFunLike.congr_fun hh x).symm

end Langlands.Global.AdelicFunctoriality
