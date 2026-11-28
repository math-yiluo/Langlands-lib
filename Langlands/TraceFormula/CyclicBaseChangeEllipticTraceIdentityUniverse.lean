import Langlands.TraceFormula.CyclicBaseChangeEllipticTraceIdentityStatement
import Langlands.Automorphic.ArithmeticComapSupercuspidalComponentProof
import Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeEquivarianceProof
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.Global.Arithmetic.CyclicNormKernelUnramifiedOrderProof
import Langlands.BaseChange.EllipticTraceIdentityTransport

/-!
# The elliptic twisted trace identity for extensions in an arbitrary universe

Reduction of `CyclicBaseChangeEllipticTraceIdentityStatement.{uF, uE, uV, uW}` to the case
`uE = uF`, by replacing `E` with an isomorphic simple extension of `F` in its own universe.
-/

noncomputable section

set_option autoImplicit false

universe uK uL uV

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.AdelicGLTransport

local instance universeRationalGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance universeContinuousGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance universeSmoothGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance universeFormsGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) := Submodule.addCommGroup _
local instance universeSpaceGroup {F : Type*} [Field F] [NumberField F]
    {n : ℕ} {v : Langlands.Global.FinitePlace F} (S : Langlands.Automorphic.LocalRealization F n v) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace Langlands.Automorphic

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]

/-- Pull back an equivalence of representations along a group homomorphism. -/
private def equivCompHom {k G H V W : Type*} [CommSemiring k] [Monoid G]
    [Monoid H] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    {ρ : Representation k G V} {ρ' : Representation k G W} (e : ρ.Equiv ρ') (f : H →* G) :
    Representation.Equiv (ρ.comp f) (ρ'.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv (fun h => e.toIntertwiningMap.isIntertwining' (f h))

/-- A representation is equivalent, by the identity, to its pullback along `f ∘ g` when
`f ∘ g = id`. -/
private def equivOfCompComp {k G H V : Type*} [CommSemiring k] [Monoid G]
    [Monoid H] [AddCommMonoid V] [Module k V] (ρ : Representation k G V) (f : H →* G)
    (g : G →* H) (hfg : ∀ y, f (g y) = y) :
    Representation.Equiv ρ ((ρ.comp f).comp g) :=
  Representation.Equiv.mk (LinearEquiv.refl k V) (fun y => by
    apply LinearMap.ext
    intro x
    change ρ y x = ρ (f (g y)) x
    rw [hfg y])

namespace CuspidalSpectralPresentation

variable [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
variable {r : ℕ} {S : CuspidalOperatorRealization L r}

/-- The local component of a presentation at the place `finitePlaceEquiv e' v` of `L`, for
`e' = e.symm`, is equivalent to the local component of the pulled-back presentation at `v`,
read through the completion isomorphism. (The inverse is a separate argument so that callers
may supply it in any syntactic form.) -/
def arithmeticComapLocalComponentEquiv (P : CuspidalSpectralPresentation.{uL, uV} S)
    (e : K ≃+* L) (e' : L ≃+* K) (he : e' = e.symm) (v : FinitePlace K) :
    (P.localComponent (finitePlaceEquiv e' v)).representation.Equiv
      (((P.arithmeticComap e).localComponent v).representation.comp
        (localEquiv (r + 1) e' v).toMonoidHom) := by
  subst he
  exact
    let c := localEquiv (r + 1) e.symm v
    let α := P.presentation.localComponentEquiv P.finiteSlice.nonzero (finitePlaceEquiv e.symm v)
    let β := (P.arithmeticComap e).presentation.localComponentEquiv
      (P.arithmeticComap e).finiteSlice.nonzero v
    let γ : (P.localFactor (finitePlaceEquiv e.symm v)).representation.Equiv
        (((P.arithmeticComap e).localFactor v).representation.comp c.toMonoidHom) :=
      equivOfCompComp (P.localFactor (finitePlaceEquiv e.symm v)).representation
        c.symm.toMonoidHom c.toMonoidHom c.symm_apply_apply
    α.symm.trans (γ.trans (equivCompHom β c.toMonoidHom))

end CuspidalSpectralPresentation

end Langlands.Automorphic

namespace Langlands.TraceFormula

open NumberField IsDedekindDomain MeasureTheory
open Langlands.Automorphic Langlands.BaseChange Langlands.HarmonicAnalysis Langlands.Unramified
open Langlands.Global.HeckeCharacter
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

universe uF uE uE' uW

/-- The matrix group map induced by the `w`-component of the completion tensor map. -/
def tensorComponentMap {F : Type uF} {E : Type uE} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (v : Langlands.Global.FinitePlace F) (w : FinitePlacesAbove E v) :
    GeneralLinear n (v.adicCompletion F ⊗[F] E) →* FiniteLocalGL E n w.1 :=
  Matrix.GeneralLinearGroup.map
    ((Pi.evalRingHom (fun q : FinitePlacesAbove E v => q.1.adicCompletion E) w).comp
      (finiteTensorMap v).toRingHom)

/-- The conclusion of `CyclicBaseChangeEllipticTraceIdentityStatement` for given data, written
exactly as there. -/
def CyclicBaseChangeEllipticConclusion {F : Type uF} {E : Type uE} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)] (σ : E ≃ₐ[F] E) (l : ℕ)
    (v : Langlands.Global.FinitePlace F) (w : FinitePlacesAbove E v) {r : ℕ}
    {S : CuspidalOperatorRealization F r} {T : CuspidalOperatorRealization E r}
    (P : CuspidalSpectralPresentation.{uE, uW} T) (D : CuspidalSpectralPresentation.{uF, uV} S) :
    Prop :=
  letI : ValuativeRel (v.adicCompletion F) :=
    (CompletionPadic.topologicalData v).valuativeRel
  haveI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    (CompletionPadic.topologicalData v).localField
  letI : TopologicalSpace (v.adicCompletion F ⊗[F] E) :=
    moduleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E)
  haveI : IsModuleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (v.adicCompletion F ⊗[F] E) :=
    IsModuleTopology.isTopologicalRing (v.adicCompletion F) _
  haveI := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion F) (r + 1)
  haveI := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion F) (r + 1)
  haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace
    (v.adicCompletion F) (r + 1)
  haveI := generalLinear_t2Space_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E) (r + 1)
  haveI := generalLinear_locallyCompactSpace_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E) (r + 1)
  haveI := generalLinear_totallyDisconnectedSpace_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E) (r + 1)
  let σv : (v.adicCompletion F ⊗[F] E) ≃ₐ[v.adicCompletion F] (v.adicCompletion F ⊗[F] E) :=
    Algebra.TensorProduct.congr AlgEquiv.refl σ
  ∃ hπ : Langlands.IsAdmissible (D.localComponent v).representation,
    HasEllipticTraceIdentity (n := r + 1) σv l (D.localComponent v).representation hπ
      ((P.localComponent w.1).representation.comp (tensorComponentMap (r + 1) v w))

section TensorCompletion

variable {F : Type uF} {E : Type uE} {E' : Type uE'} [Field F] [NumberField F] [Field E]
  [NumberField E] [Field E'] [NumberField E'] [Algebra F E] [Algebra F E']

/-- The `q`-component of `finiteTensorMap` after `id ⊗ e` is the completed transport of the
component at the corresponding place of `E`. -/
theorem finiteTensorMap_congr_apply (e : E ≃ₐ[F] E') (v : Langlands.Global.FinitePlace F)
    (q : FinitePlacesAbove E' v)
    (hp : (finitePlaceEquiv e.toRingEquiv q.1).asIdeal.LiesOver v.asIdeal)
    (z : v.adicCompletion F ⊗[F] E) :
    finiteCompletionEquiv e.toRingEquiv q.1
        (finiteTensorMap v z ⟨finitePlaceEquiv e.toRingEquiv q.1, hp⟩) =
      finiteTensorMap v ((Algebra.TensorProduct.congr AlgEquiv.refl e :
        (v.adicCompletion F ⊗[F] E) ≃ₐ[v.adicCompletion F] (v.adicCompletion F ⊗[F] E')) z) q := by
  have := q.2
  induction z using TensorProduct.inductionOn with
  | tmul a y =>
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    simp only [finiteTensorMap_tmul]
    rw [map_mul, finiteCompletionEquiv_coe]
    congr 1
    exact finiteCompletionEquiv_algEquiv_completionMap e v q.1 a
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end TensorCompletion

section Transfer

variable {F : Type uF} {E : Type uE} {E' : Type uE'} [Field F] [NumberField F] [Field E]
  [NumberField E] [Field E'] [NumberField E'] [Algebra F E] [Algebra F E']
  [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
  [CompactSpace (AdeleQuotient E')]

/-- **Transfer of the conclusion along an isomorphism `E ≃ₐ[F] E'`.** The conclusion of
`CyclicBaseChangeEllipticTraceIdentityStatement` for the pulled-back presentation over `E'`,
the transported automorphism and the corresponding place gives the conclusion over `E`. -/
theorem CyclicBaseChangeEllipticConclusion.of_arithmeticComap (e : E ≃ₐ[F] E')
    (σ : E ≃ₐ[F] E) (l : ℕ) (v : Langlands.Global.FinitePlace F) (w : FinitePlacesAbove E v)
    (q : FinitePlacesAbove E' v) (hq : finitePlaceEquiv e.toRingEquiv q.1 = w.1)
    {r : ℕ} {S : CuspidalOperatorRealization F r} {T : CuspidalOperatorRealization E r}
    (P : CuspidalSpectralPresentation.{uE, uW} T) (D : CuspidalSpectralPresentation.{uF, uV} S)
    (h : CyclicBaseChangeEllipticConclusion (AlgEquiv.autCongr e σ) l v q
      (P.arithmeticComap e.toRingEquiv.symm) D) :
    CyclicBaseChangeEllipticConclusion σ l v w P D := by
  obtain ⟨p, hp⟩ := w
  change finitePlaceEquiv e.toRingEquiv q.1 = p at hq
  subst hq
  let : ValuativeRel (v.adicCompletion F) := (CompletionPadic.topologicalData v).valuativeRel
  have : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    (CompletionPadic.topologicalData v).localField
  let : TopologicalSpace (v.adicCompletion F ⊗[F] E) :=
    moduleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E)
  have : IsModuleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (v.adicCompletion F ⊗[F] E) :=
    IsModuleTopology.isTopologicalRing (v.adicCompletion F) _
  let : TopologicalSpace (v.adicCompletion F ⊗[F] E') :=
    moduleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E')
  have : IsModuleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E') := ⟨rfl⟩
  have : IsTopologicalRing (v.adicCompletion F ⊗[F] E') :=
    IsModuleTopology.isTopologicalRing (v.adicCompletion F) _
  have := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion F) (r + 1)
  have := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion F) (r + 1)
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace
    (v.adicCompletion F) (r + 1)
  have := generalLinear_t2Space_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E) (r + 1)
  have := generalLinear_locallyCompactSpace_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E) (r + 1)
  have := generalLinear_totallyDisconnectedSpace_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E) (r + 1)
  have := generalLinear_t2Space_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E') (r + 1)
  have := generalLinear_locallyCompactSpace_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E') (r + 1)
  have := generalLinear_totallyDisconnectedSpace_of_finite (v.adicCompletion F)
    (v.adicCompletion F ⊗[F] E') (r + 1)
  let σv : (v.adicCompletion F ⊗[F] E) ≃ₐ[v.adicCompletion F] (v.adicCompletion F ⊗[F] E) :=
    Algebra.TensorProduct.congr AlgEquiv.refl σ
  let σv' : (v.adicCompletion F ⊗[F] E') ≃ₐ[v.adicCompletion F] (v.adicCompletion F ⊗[F] E') :=
    Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.autCongr e σ)
  let ε : (v.adicCompletion F ⊗[F] E) ≃ₐ[v.adicCompletion F] (v.adicCompletion F ⊗[F] E') :=
    Algebra.TensorProduct.congr AlgEquiv.refl e
  have hε : Continuous ε := IsModuleTopology.continuous_of_linearMap ε.toLinearEquiv.toLinearMap
  have hε' : Continuous ε.symm :=
    IsModuleTopology.continuous_of_linearMap ε.symm.toLinearEquiv.toLinearMap
  have hσ : ∀ x, ε (σv x) = σv' (ε x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a y =>
      simp only [ε, σv, σv', Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
        AlgEquiv.autCongr_apply]
      congr 1
      change e (σ y) = e (σ (e.symm (e y)))
      rw [AlgEquiv.symm_apply_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  unfold CyclicBaseChangeEllipticConclusion at h ⊢
  obtain ⟨hπ, hτ⟩ := h
  refine ⟨hπ, ?_⟩
  let ψ := tensorComponentMap (r + 1) v ⟨finitePlaceEquiv e.toRingEquiv q.1, hp⟩
  let ψ' := tensorComponentMap (r + 1) v q
  let cE := localEquiv (r + 1) e.toRingEquiv q.1
  let κ := generalLinearRingEquiv (n := r + 1) ε.toRingEquiv hε hε'
  let B₀ := P.arithmeticComapLocalComponentEquiv e.toRingEquiv.symm e.toRingEquiv
    (RingEquiv.symm_symm _).symm q.1
  have hident : ∀ g, cE (ψ g) = ψ' (κ g) := by
    intro g
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact finiteTensorMap_congr_apply e v q hp (g i j)
  let π := (D.localComponent v).representation
  have key := ellipticTraceIdentity_transport_comp (n := r + 1) (l := l) (σ₁ := σv) (σ₂ := σv')
    ε hε hε' hσ (continuous_algebraMap _ _) (continuous_algebraMap _ _) π hπ
    B₀ ψ ψ' hident hτ
  with_reducible exact key

end Transfer

universe uV' uW'

/-- The trace identity stated with its local conclusion factored out. -/
def CyclicBaseChangeEllipticTraceIdentityWithConclusion : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsUnramifiedAtInfinitePlaces F E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E) (l : ℕ), l.Prime → IsCyclicAlgebra σ l →
    ∀ (v : Langlands.Global.FinitePlace F) (w : FinitePlacesAbove E v),
      (∀ w'' : FinitePlacesAbove E v, w'' = w) →
    ∀ (v' : Langlands.Global.FinitePlace F) (w' : FinitePlacesAbove E v'),
      v' ≠ v → (∀ w'' : FinitePlacesAbove E v', w'' = w') →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization F r) (T : CuspidalOperatorRealization E r)
      (P : CuspidalSpectralPresentation.{uE, uW'} T),
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      (P.localComponent w.1).IsSupercuspidal →
      (P.localComponent w'.1).IsSupercuspidal →
      CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{uF, uE, uV', uW'}
        T.isoClass S.isoClass →
    ∀ D : CuspidalSpectralPresentation.{uF, uV'} S,
      (D.localComponent v).IsIrreducible → (D.localComponent v).IsAdmissible →
      CyclicBaseChangeEllipticConclusion σ l v w P D

/-- Factoring out the local conclusion leaves the published trace identity unchanged. -/
theorem cyclicBaseChangeEllipticTraceIdentity_iff_withConclusion :
    CyclicBaseChangeEllipticTraceIdentityStatement.{uF, uE, uV', uW'} ↔
      CyclicBaseChangeEllipticTraceIdentityWithConclusion.{uF, uE, uV', uW'} :=
  Iff.rfl

/-- The elliptic twisted trace identity for number fields in a common universe implies
the identity for number fields in independently chosen universes. -/
def CyclicBaseChangeEllipticTraceIdentityUniverseReductionStatement.{uBase, uExtension,
    uOrdinary, uTwisted} : Prop :=
  CyclicBaseChangeEllipticTraceIdentityStatement.{uBase, uBase, uOrdinary, uTwisted} →
    CyclicBaseChangeEllipticTraceIdentityStatement.{uBase, uExtension, uOrdinary, uTwisted}

/-- Transport the extension, both exceptional places and the spectral data to the
base field's universe, then transport the local conclusion back. -/
theorem cyclicBaseChangeEllipticTraceIdentity_of_sameUniverse :
    CyclicBaseChangeEllipticTraceIdentityUniverseReductionStatement.{uF, uE, uV', uW'} := by
  intro h
  have hSame := cyclicBaseChangeEllipticTraceIdentity_iff_withConclusion.mp h
  apply cyclicBaseChangeEllipticTraceIdentity_iff_withConclusion.mpr
  intro F E _ _ _ _ _ _ _ _ σ l hl hcyc v w hw v' w' hv' hw' r S T P hunit hwsc hw'sc hbc
    D hDirr hDadm
  have : Module.Finite F E := hcyc.1
  obtain ⟨E', _, _, ⟨e⟩⟩ := exists_algEquiv_baseUniverse F E
  have : NumberField E' := NumberField.of_ringEquiv (K := E) (L := E') e.toRingEquiv
  have : CompactSpace (AdeleQuotient E') := adeleQuotientCompact E'
  have : IsUnramifiedAtInfinitePlaces F E' := ⟨fun q => by
    obtain ⟨p, rfl⟩ := (infinitePlaceEquiv e.toRingEquiv.symm).surjective q
    exact (p.isUnramified F).comap_algHom e.symm.toAlgHom⟩
  let σ' := e.autCongr σ
  have hcyc' : IsCyclicAlgebra σ' l := by
    refine ⟨Module.Finite.of_surjective e.toLinearMap e.surjective,
      e.symm.toLinearEquiv.finrank_eq.trans hcyc.2.1, inferInstance,
      (e.autCongr.orderOf_eq σ).trans hcyc.2.2.2.1, ?_⟩
    intro x hx
    have hfixed : σ (e.symm x) = e.symm x := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact hx
    obtain ⟨a, ha⟩ := hcyc.2.2.2.2 _ hfixed
    exact ⟨a, by rw [← e.commutes, ha, e.apply_symm_apply]⟩
  let place {p : Langlands.Global.FinitePlace F} (z : FinitePlacesAbove E p) :
      FinitePlacesAbove E' p :=
    ⟨finitePlaceEquiv e.toRingEquiv.symm z.1, by
      have := z.2
      exact liesOver_finitePlaceEquiv_algEquiv e.symm p z.1⟩
  have place_back {p : Langlands.Global.FinitePlace F} (z : FinitePlacesAbove E p) :
      finitePlaceEquiv e.toRingEquiv (place z).1 = z.1 := by
    change finitePlaceEquiv e.toRingEquiv (finitePlaceEquiv e.toRingEquiv.symm z.1) = z.1
    rw [finitePlaceEquiv_symm, Equiv.apply_symm_apply]
  have place_unique {p : Langlands.Global.FinitePlace F} {z : FinitePlacesAbove E p}
      (hz : ∀ y : FinitePlacesAbove E p, y = z) (q : FinitePlacesAbove E' p) : q = place z := by
    have := q.2
    let y : FinitePlacesAbove E p := ⟨finitePlaceEquiv e.toRingEquiv q.1,
      liesOver_finitePlaceEquiv_algEquiv e p q.1⟩
    apply Subtype.ext
    apply (finitePlaceEquiv e.toRingEquiv).injective
    exact (congrArg Subtype.val (hz y)).trans (place_back z).symm
  let T' := T.arithmeticComap e.toRingEquiv.symm
  let P' := P.arithmeticComap e.toRingEquiv.symm
  have hsuper {p : Langlands.Global.FinitePlace F} (z : FinitePlacesAbove E p)
      (hz : (P.localComponent z.1).IsSupercuspidal) :
      (P'.localComponent (place z).1).IsSupercuspidal :=
    P.arithmeticComap_localComponent_isSupercuspidal e.toRingEquiv.symm z.1 hz
  have hbc' : CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{uF, uF, uV', uW'}
      T'.isoClass S.isoClass := by
    obtain ⟨s, t, hs, ht, hst⟩ := hbc
    have hst' := SpectralSystem.IsArithmeticWeakBaseChangeOf.reindex_of_comm
      (RingEquiv.refl F) e.toRingEquiv (fun a => e.commutes a) hst
    rw [← finitePlaceEquiv_symm, ← finitePlaceEquiv_symm] at hst'
    have hs' := Langlands.Automorphic.Unramified.cuspidalSpectralArithmeticComap.{uF, uF, uV'}
      F F (RingEquiv.refl F).symm r S.isoClass s hs
    rw [RingEquiv.symm_refl] at hs' hst'
    rw [CuspidalOperatorRealization.IsoClass.arithmeticComap_refl] at hs'
    have ht' := Langlands.Automorphic.Unramified.cuspidalSpectralArithmeticComap.{uF, uE, uW'}
      E' E e.toRingEquiv.symm r T.isoClass t ht
    exact ⟨_, _, hs', ht', hst'⟩
  have h' := hSame F E' σ' l hl hcyc' v (place w) (place_unique hw) v' (place w') hv'
    (place_unique hw') r S T' P' hunit (hsuper w hwsc) (hsuper w' hw'sc) hbc' D hDirr hDadm
  have key := CyclicBaseChangeEllipticConclusion.of_arithmeticComap e σ l v w (place w)
    (place_back w) P D h'
  with_reducible exact key

end Langlands.TraceFormula
