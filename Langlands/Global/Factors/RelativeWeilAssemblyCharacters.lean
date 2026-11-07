import Langlands.Global.Factors.RelativeWeilBrauer
import Langlands.ClassField.Global.RelativeWeilTransferNormStatement
import Langlands.ClassField.Global.RelativeWeilCharacterFactorizationStatement
import Langlands.Global.HeckeCharacter
import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Langlands.Global.AdelicFunctoriality.Trace
import Langlands.Global.Factors.HeckeFunctionalEquationStatement
import Langlands.HarmonicAnalysis.CharacterTransport

/-!
# Characters of relative Weil groups in the global assembly

Reciprocity characters `λ ∘ τ` of relative Weil groups, their restriction to intermediate
fields through the norm compatibility of the transfer, and their values on local maps whose
transfer is inverse local reciprocity.
-/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NumberField
open scoped NumberField
open Langlands.Global Langlands.Global.AdelicFunctoriality

attribute [local instance] relativeGaloisTopology

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u}
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

@[simp]
theorem continuousReciprocityCharacter_apply (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (t : RelativeWeilGroup c F E) :
    continuousReciprocityCharacter c F E χ t = (χ (transfer c F E t))⁻¹ := rfl

theorem continuousReciprocityCharacter_mul (χ χ' : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) :
    continuousReciprocityCharacter c F E (χ * χ') =
      continuousReciprocityCharacter c F E χ * continuousReciprocityCharacter c F E χ' :=
  DFunLike.ext _ _ fun _ => mul_inv _ _

theorem continuousReciprocityCharacter_inv (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) :
    continuousReciprocityCharacter c F E χ⁻¹ = (continuousReciprocityCharacter c F E χ)⁻¹ :=
  DFunLike.ext _ _ fun _ => rfl

/-- Under the factorization of characters through the transfer, every continuous character
of `W_{E/F}` is a reciprocity character `λ ∘ τ_F`. -/
theorem exists_eq_continuousReciprocityCharacter (hfac : TransferCharacterFactorization c F E)
    (θ : RelativeWeilGroup c F E →ₜ* ℂˣ) :
    ∃ l : HeckeCharacter F, θ = continuousReciprocityCharacter c F E l := by
  obtain ⟨χ, hχ⟩ := hfac θ
  refine ⟨χ⁻¹, DFunLike.ext _ _ fun t => ?_⟩
  rw [hχ t]
  exact (inv_inv _).symm

/-- The value of a reciprocity character on a homomorphism whose transfer is the inverse of
a local unit at the finite place `v` is the component of the character at `v`. -/
theorem continuousReciprocityCharacter_apply_of_transfer_eq (l : HeckeCharacter F)
    {v : Langlands.Global.FinitePlace F} {G : Type*} (φ : G → RelativeWeilGroup c F E)
    (f : G → (FiniteCompletion F v)ˣ)
    (hφ : ∀ y, transfer c F E (φ y) = (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (f y))⁻¹)
    (y : G) :
    continuousReciprocityCharacter c F E l (φ y) = l.finiteComponent v (f y) := by
  rw [continuousReciprocityCharacter_apply, hφ y, map_inv, inv_inv]
  rfl

section Tower

variable (K : Type u) [Field K] [NumberField K] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
  (h : FundamentalClass.Restriction c)

/-- With the norm compatibility of the transfer, the restriction of `χ ∘ τ_F` to `W_{E/K}` is
`(χ ∘ N_{K/F}) ∘ τ_K`. -/
theorem continuousReciprocityCharacter_comp_restrictionInclusion
    (hN : TransferNormCompatibility c F K E h) (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) :
    haveI : IsGalois K E := IsGalois.tower_top_of_isGalois F K E
    (continuousReciprocityCharacter c F E χ).comp (restrictionInclusion c F E K h) =
      continuousReciprocityCharacter c K E (χ.comp (ideleClassNorm (K := F) (L := K))) := by
  have : IsGalois K E := IsGalois.tower_top_of_isGalois F K E
  ext t
  simp only [ContinuousMonoidHom.comp_toFun, continuousReciprocityCharacter_apply]
  rw [hN t]

end Tower

end Langlands.ClassField.Global.RelativeWeilGroup

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField

variable {K : Type u} {L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- The idele norm of an idele supported at one finite place `q` above `p` is supported at
`p`, with the local norm there. -/
theorem ideleNorm_ofAdicCompletion (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p)
    (x : (q.1.adicCompletion L)ˣ) :
    ideleNorm (K := K) (IdeleGroup.ofAdicCompletion (𝓞 L) L q.1 x) =
      IdeleGroup.ofAdicCompletion (𝓞 K) K p (FiniteExtension.localUnitNorm p q.1 x) := by
  classical
  apply Units.ext
  refine Prod.ext ?_ ?_
  · change infiniteAdeleNorm (1 : InfiniteAdeleRing L) = 1
    exact map_one _
  · apply FiniteAdeleRing.ext
    intro p'
    change (∏ q' : FinitePlacesAbove L p', FiniteExtension.localNorm p' q'.1
        (Pi.mulSingle q.1 (x : q.1.adicCompletion L) q'.1)) =
      Pi.mulSingle p (FiniteExtension.localNorm p q.1 x) p'
    by_cases hp : p' = p
    · subst hp
      rw [Pi.mulSingle_eq_same, Finset.prod_eq_single q]
      · rw [Pi.mulSingle_eq_same]
      · intro q' _ hq'
        have hne : q'.1 ≠ q.1 := fun h => hq' (Subtype.ext h)
        rw [Pi.mulSingle_eq_of_ne hne, map_one]
      · intro h
        exact absurd (Finset.mem_univ q) h
    · rw [Pi.mulSingle_eq_of_ne hp]
      refine Finset.prod_eq_one fun q' _ => ?_
      have hne : q'.1 ≠ q.1 := by
        intro h
        apply hp
        rw [← finitePlacesAbove_under p' q', ← finitePlacesAbove_under p q, h]
      rw [Pi.mulSingle_eq_of_ne hne, map_one]

/-- The idele-class norm of the class of an idele supported at one finite place. -/
theorem ideleClassNorm_ofAdicCompletion (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p)
    (x : (q.1.adicCompletion L)ˣ) :
    ideleClassNorm (K := K) (IdeleClassGroup.ofAdicCompletion (𝓞 L) L q.1 x) =
      IdeleClassGroup.ofAdicCompletion (𝓞 K) K p (FiniteExtension.localUnitNorm p q.1 x) := by
  change ideleClassNorm (K := K) (QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 L) L q.1 x)) = _
  rw [ideleClassNorm_mk, ideleNorm_ofAdicCompletion]
  rfl

/-- The idele norm of an idele supported at one infinite place `w` above `v` is supported at
`v`, with the local norm there. -/
theorem ideleNorm_ofCompletion (v : InfinitePlace K) (w : InfinitePlacesAbove L v)
    (x : (w.1.Completion)ˣ) :
    ideleNorm (K := K) (IdeleGroup.ofCompletion (𝓞 L) L w.1 x) =
      IdeleGroup.ofCompletion (𝓞 K) K v (InfiniteExtension.localUnitNorm v w.1 x) := by
  classical
  apply Units.ext
  refine Prod.ext ?_ ?_
  · funext v'
    change (∏ w' : InfinitePlacesAbove L v', InfiniteExtension.localNorm v' w'.1
        (Pi.mulSingle w.1 (x : w.1.Completion) w'.1)) =
      Pi.mulSingle v (InfiniteExtension.localNorm v w.1 x) v'
    by_cases hv : v' = v
    · subst hv
      rw [Pi.mulSingle_eq_same, Finset.prod_eq_single w]
      · rw [Pi.mulSingle_eq_same]
      · intro w' _ hw'
        have hne : w'.1 ≠ w.1 := fun h => hw' (Subtype.ext h)
        rw [Pi.mulSingle_eq_of_ne hne, map_one]
      · intro h
        exact absurd (Finset.mem_univ w) h
    · rw [Pi.mulSingle_eq_of_ne hv]
      refine Finset.prod_eq_one fun w' _ => ?_
      have hne : w'.1 ≠ w.1 := by
        intro h
        apply hv
        rw [← NumberField.InfinitePlace.LiesOver.comap_eq w'.1 v',
          ← NumberField.InfinitePlace.LiesOver.comap_eq w.1 v, h]
      rw [Pi.mulSingle_eq_of_ne hne, map_one]
  · change finiteAdeleNorm (1 : FiniteAdeleRing (𝓞 L) L) = 1
    exact map_one _

/-- The idele-class norm of the class of an idele supported at one infinite place. -/
theorem ideleClassNorm_ofCompletion (v : InfinitePlace K) (w : InfinitePlacesAbove L v)
    (x : (w.1.Completion)ˣ) :
    ideleClassNorm (K := K) (IdeleClassGroup.ofCompletion (𝓞 L) L w.1 x) =
      IdeleClassGroup.ofCompletion (𝓞 K) K v (InfiniteExtension.localUnitNorm v w.1 x) := by
  change ideleClassNorm (K := K) (QuotientGroup.mk (IdeleGroup.ofCompletion (𝓞 L) L w.1 x)) = _
  rw [ideleClassNorm_mk, ideleNorm_ofCompletion]
  rfl

section AdditiveCharacter

open Langlands.Global
open scoped FiniteExtension

/-- The additive character `ψ_p ∘ Tr_{L_q/K_p}` of the completion `L_q`. -/
def localTraceCharacter (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    [q.asIdeal.LiesOver p.asIdeal]
    (ψp : HarmonicAnalysis.UnitaryAdditiveCharacter (p.adicCompletion K)) :
    HarmonicAnalysis.UnitaryAdditiveCharacter (q.adicCompletion L) :=
  haveI : CharZero (p.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (p.adicCompletion K)).injective
  ψp.comapSurjective (FiniteExtension.localTrace p q).toAddMonoidHom
    (FiniteExtension.continuous_localTrace p q)
    (Algebra.trace_surjective (p.adicCompletion K) (q.adicCompletion L))

@[simp]
theorem localTraceCharacter_apply (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    [q.asIdeal.LiesOver p.asIdeal]
    (ψp : HarmonicAnalysis.UnitaryAdditiveCharacter (p.adicCompletion K)) (x : q.adicCompletion L) :
    localTraceCharacter p q ψp x = ψp (FiniteExtension.localTrace p q x) := rfl

/-- The component of `ψ ∘ Tr` at a finite place `q` above `p` is `ψ_p ∘ Tr_{L_q/K_p}`, where
`ψ_p` is the component of `ψ` at `p`. -/
theorem isFiniteAdditiveComponent_traceAdditiveCharacter
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (hψ : ∀ x : K, ψ (diagonal K x) = 1) (p : FinitePlace K)
    (ψp : HarmonicAnalysis.UnitaryAdditiveCharacter (p.adicCompletion K))
    (hp : HeckeFunctionalEquation.IsFiniteAdditiveComponent ψ p ψp)
    (q : FinitePlacesAbove L p) :
    HeckeFunctionalEquation.IsFiniteAdditiveComponent (traceAdditiveCharacter ψ hψ) q.1
      (localTraceCharacter p q.1 ψp) := by
  classical
  intro x
  rw [localTraceCharacter_apply, hp, traceAdditiveCharacter_single]

end AdditiveCharacter

end Langlands.Global.AdelicFunctoriality

namespace Langlands.Global.HeckeCharacter

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

variable {K : Type u} {L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- The Hecke character `χ ∘ N_{L/K}` of `L`. -/
def normComp (χ : HeckeCharacter K) : HeckeCharacter L :=
  χ.comp (ideleClassNorm (K := K) (L := L))

/-- The component of `χ ∘ N_{L/K}` at a finite place `q` above `p` is the component of `χ`
at `p` composed with the local norm. -/
theorem normComp_finiteComponent (χ : HeckeCharacter K) (p : FinitePlace K)
    (q : FinitePlacesAbove L p) (x : (FiniteCompletion L q.1)ˣ) :
    (normComp (L := L) χ).finiteComponent q.1 x =
      χ.finiteComponent p (FiniteExtension.localUnitNorm p q.1 x) := by
  change χ (ideleClassNorm (K := K) (IdeleClassGroup.ofAdicCompletion (𝓞 L) L q.1 x)) = _
  rw [ideleClassNorm_ofAdicCompletion]
  rfl

/-- `χ ∘ N_{L/K}` is unramified above every finite place where `χ` is unramified. -/
theorem normComp_isUnramifiedAt (χ : HeckeCharacter K) (p : FinitePlace K)
    (hχ : χ.IsUnramifiedAt p) (q : FinitePlacesAbove L p) :
    (normComp (L := L) χ).IsUnramifiedAt q.1 := by
  intro x hx
  rw [normComp_finiteComponent]
  exact hχ _ (FiniteExtension.localUnitNorm_integral p q.1 hx)

/-- A Hecke character trivial on the archimedean ideles has trivial archimedean components. -/
theorem infiniteComponent_eq_one_of_hasPrescribedInfinityComponent_one (χ : HeckeCharacter K)
    (h : χ.HasPrescribedInfinityComponent 1) (v : InfinitePlace K) :
    χ.infiniteComponent v = 1 := by
  refine DFunLike.ext _ _ fun y => ?_
  have hy : χ.infiniteComponent v y =
      χ.atInfinity (Units.map (NumberField.InfiniteAdeleRing.ofCompletion v) y) := by
    change χ (ideleClassMap K (infiniteIdeleInclusion K v y)) =
      χ (ideleClassMap K (infiniteIdelesInclusion K _))
    congr 2
  rw [hy, h]
  rfl

/-- If `χ` is trivial on the archimedean ideles, so is every archimedean component of
`χ ∘ N_{L/K}`. -/
theorem normComp_infiniteComponent_eq_one (χ : HeckeCharacter K)
    (h : χ.HasPrescribedInfinityComponent 1) (w : InfinitePlace L) :
    (normComp (L := L) χ).infiniteComponent w = 1 := by
  let v : InfinitePlace K := w.comap (algebraMap K L)
  have hw : w.LiesOver v := ⟨rfl⟩
  refine DFunLike.ext _ _ fun y => ?_
  change χ (ideleClassNorm (K := K) (IdeleClassGroup.ofCompletion (𝓞 L) L w y)) = 1
  rw [ideleClassNorm_ofCompletion v ⟨w, hw⟩ y]
  have := DFunLike.congr_fun (infiniteComponent_eq_one_of_hasPrescribedInfinityComponent_one χ h v)
    (InfiniteExtension.localUnitNorm v w y)
  exact this

end Langlands.Global.HeckeCharacter
