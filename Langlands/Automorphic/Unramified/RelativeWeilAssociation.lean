import Langlands.ClassField.Global.LocalRelativeWeilMap
import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Weil.Representation.Restriction
import Langlands.Weil.Representation.Predicates
import Langlands.Weil.Representation.InductionContinuity
import Langlands.Correspondence.ArithmeticFactors

/-! # Weak association of relative Weil representations with unramified spectra

Representations of the relative Weil group `W_{E/F}` at a supplied class family are
compared with supplied unramified spectra through the local maps `W_{F_v} → W_{E/F}`
characterized by `IsLocalRelativeWeilMap`. No local map, representation, or spectrum
is constructed, and no comparison with the absolute Weil group is made.
-/

noncomputable section

namespace Langlands.ClassField.Global

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.Unramified

universe u uV uW uP

namespace RelativeWeilGroup

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}} {v : FinitePlace F}

/-- The local component `S ∘ ι` of `S` along a supplied map `ι : W_{F_v} → W_{E/F}`,
on the original carrier of `S`. -/
def localComponent (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    FiniteRepresentation.{0, u, uV} ℂ (Weil.Local.localWeilGroup (padicField v)) :=
  FiniteRepresentation.restrict ι.toMonoidHom S

@[simp] theorem localComponent_representation
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (g : Weil.Local.localWeilGroup (padicField v)) :
    (localComponent S ι).representation g = S.representation (ι g) :=
  rfl

/-- The local component of a continuous representation is continuous. -/
theorem localComponent_isContinuous
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hS : S.IsContinuous) : (localComponent S ι).IsContinuous :=
  FiniteRepresentation.isContinuous_restrict ι.toMonoidHom ι.continuous hS

/-- The zero-monodromy pair class of the local component, in the published class type
of the actual local Weil group with its actual norm character. -/
def localPairClass (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    Correspondence.LocalPairClass.{u, uV} (padicField v) :=
  WeilDeligneRepresentation.classOf
    (WeilDeligneRepresentation.zeroMonodromy
      (Weil.Local.localNormCharacter (padicField v)).toMonoidHom (localComponent S ι))

/-- The polynomial `det(1 - X S(ι Fr))` on the whole carrier, at the published geometric
Frobenius lift `Fr` of `W_{F_v}`. It is the Euler denominator when `S ∘ ι` is unramified. -/
def localEulerPolynomial (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    Polynomial ℂ :=
  LocalFactor.eulerPolynomial
    ((localComponent S ι).representation (Weil.Local.localGeometricFrobenius (padicField v)))

/-- At the finite place `v` of `F`, `S` is unramified and matches the polynomial `P`: at every
place `w` of `E` above `v`, a local map `ι : W_{F_v} → W_{E/F}` for `w` exists, and every such
map makes `S ∘ ι` unramified with `det(1 - X S(ι Fr)) = P`. -/
def IsUnramifiedMatchAt (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (v : FinitePlace F) (P : Polynomial ℂ) : Prop :=
  ∀ w : FinitePlacesAbove E v,
    (∃ (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
        (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E),
        IsLocalRelativeWeilMap v w.1 e ι) ∧
      ∀ (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
        (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E),
        IsLocalRelativeWeilMap v w.1 e ι →
          (localComponent S ι).IsUnramified (Weil.Local.localInertia (padicField v)) ∧
            localEulerPolynomial S ι = P

/-- `S` is weakly associated with the supplied spectral system `s` of rank `n`: `S` is
continuous of rank `n`, and on one cofinite set of finite places `v` of `F`, `s` is defined
at `v` and `S` is unramified and matches the Euler polynomial `∏ (1 - z X)` of the spectrum
of `s` at `v`. -/
def IsWeaklyAssociated {n : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (s : SpectralSystem (FinitePlace F) n) : Prop :=
  S.IsContinuous ∧ S.rank = n ∧
    ∀ᶠ v in Filter.cofinite, ∃ hs : v ∉ s.exceptional,
      IsUnramifiedMatchAt S v (s.eulerPolynomial v hs)

/-- The cofinite condition is one finite exceptional set containing that of `s`. -/
theorem isWeaklyAssociated_iff_exists_finset {n : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (s : SpectralSystem (FinitePlace F) n) :
    IsWeaklyAssociated S s ↔
      S.IsContinuous ∧ S.rank = n ∧ ∃ (T : Finset (FinitePlace F)) (hT : s.exceptional ⊆ T),
        ∀ (v : FinitePlace F) (hv : v ∉ T),
          IsUnramifiedMatchAt S v (s.eulerPolynomial v fun h => hv (hT h)) := by
  classical
  constructor
  · rintro ⟨hc, hn, h⟩
    have hfin := Filter.eventually_cofinite.mp h
    refine ⟨hc, hn, hfin.toFinset ∪ s.exceptional, Finset.subset_union_right, fun v hv => ?_⟩
    have hv' : v ∉ hfin.toFinset := fun h' => hv (Finset.mem_union_left _ h')
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv'
    obtain ⟨_, hm⟩ := hv'
    exact hm
  · rintro ⟨hc, hn, T, hT, h⟩
    refine ⟨hc, hn, ?_⟩
    filter_upwards [T.eventually_cofinite_notMem] with v hv
    exact ⟨fun h' => hv (hT h'), h v hv⟩

section Invariance

variable {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
  {S' : FiniteRepresentation.{0, u, uW} ℂ (RelativeWeilGroup c F E)}

/-- An equivalence conjugates every operator of `S` to the corresponding operator of `S'`. -/
theorem representation_eq_conj_of_equiv (φ : FiniteRepresentation.Equiv S S')
    (g : RelativeWeilGroup c F E) :
    S'.representation g = φ.toLinearEquiv.conj (S.representation g) := by
  have hc : φ.toLinearEquiv.toLinearMap ∘ₗ S.representation g ∘ₗ
      φ.toLinearEquiv.symm.toLinearMap = S'.representation g := by
    ext b
    have hx := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g (φ.symm b)
    exact hx.trans (congrArg (S'.representation g) (φ.right_inv b))
  rw [LinearEquiv.conj_apply]
  exact hc.symm

/-- Continuity is invariant under equivalence. -/
theorem isContinuous_of_equiv (φ : FiniteRepresentation.Equiv S S') (h : S.IsContinuous) :
    S'.IsContinuous := by
  let : TopologicalSpace (Module.End ℂ S) := moduleTopology ℂ (Module.End ℂ S)
  let : TopologicalSpace (Module.End ℂ S') := moduleTopology ℂ (Module.End ℂ S')
  have : IsModuleTopology ℂ (Module.End ℂ S) := ⟨rfl⟩
  have : ContinuousAdd (Module.End ℂ S') := ModuleTopology.continuousAdd ℂ _
  have : ContinuousSMul ℂ (Module.End ℂ S') := ModuleTopology.continuousSMul ℂ _
  have hS : Continuous S.representation := h
  have hconj : (S'.representation : RelativeWeilGroup c F E → Module.End ℂ S') =
      φ.toLinearEquiv.conj.toLinearMap ∘ S.representation :=
    funext (representation_eq_conj_of_equiv φ)
  change Continuous (S'.representation : RelativeWeilGroup c F E → Module.End ℂ S')
  rw [hconj]
  exact (IsModuleTopology.continuous_of_linearMap _).comp hS

/-- Equivalent representations have equal local Euler polynomials. -/
theorem localEulerPolynomial_eq_of_equiv (φ : FiniteRepresentation.Equiv S S')
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    localEulerPolynomial S' ι = localEulerPolynomial S ι := by
  set g := ι (Weil.Local.localGeometricFrobenius (padicField v))
  change LocalFactor.eulerPolynomial (S'.representation g) =
    LocalFactor.eulerPolynomial (S.representation g)
  rw [representation_eq_conj_of_equiv φ g, LinearEquiv.conj_apply]
  exact LocalFactor.eulerPolynomial_conj φ.toLinearEquiv (S.representation g)

/-- Unramifiedness of the local component is invariant under equivalence. -/
theorem localComponent_isUnramified_of_equiv (φ : FiniteRepresentation.Equiv S S')
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (h : (localComponent S ι).IsUnramified (Weil.Local.localInertia (padicField v))) :
    (localComponent S' ι).IsUnramified (Weil.Local.localInertia (padicField v)) := by
  intro i
  have hi : S.representation (ι i) = 1 := h i
  change S'.representation (ι i) = 1
  ext b
  have hx := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap (ι i)
    (φ.symm b)
  simpa [hi] using hx.symm

/-- The local matching condition depends only on the equivalence class of `S`. -/
theorem IsUnramifiedMatchAt.of_equiv {P : Polynomial ℂ} (φ : FiniteRepresentation.Equiv S S')
    (h : IsUnramifiedMatchAt S v P) : IsUnramifiedMatchAt S' v P := by
  refine fun w => ⟨(h w).1, fun e ι hι => ?_⟩
  obtain ⟨hu, hp⟩ := (h w).2 e ι hι
  exact ⟨localComponent_isUnramified_of_equiv φ ι hu,
    (localEulerPolynomial_eq_of_equiv φ ι).trans hp⟩

/-- Weak association depends only on the equivalence class of `S`. -/
theorem IsWeaklyAssociated.of_equiv {n : ℕ} {s : SpectralSystem (FinitePlace F) n}
    (φ : FiniteRepresentation.Equiv S S') (h : IsWeaklyAssociated S s) :
    IsWeaklyAssociated S' s := by
  rcases h with ⟨hc, hn, h⟩
  exact ⟨isContinuous_of_equiv φ hc, (FiniteRepresentation.rank_eq_of_equiv φ).symm.trans hn,
    h.mono fun v ⟨hs, hv⟩ => ⟨hs, hv.of_equiv φ⟩⟩

end Invariance

/-- Enlarging the exceptional set of the spectral system preserves weak association
in both directions. -/
theorem isWeaklyAssociated_restrict_iff {n : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (s : SpectralSystem (FinitePlace F) n) (U : Finset (FinitePlace F))
    (hU : s.exceptional ⊆ U) :
    IsWeaklyAssociated S (s.restrict U hU) ↔ IsWeaklyAssociated S s := by
  constructor
  · rintro ⟨hc, hn, h⟩
    exact ⟨hc, hn, h.mono fun v ⟨hs, hv⟩ => ⟨fun h' => hs (hU h'), hv⟩⟩
  · rintro ⟨hc, hn, h⟩
    refine ⟨hc, hn, ?_⟩
    filter_upwards [h, U.eventually_cofinite_notMem] with v hv hU'
    rcases hv with ⟨_, hv⟩
    exact ⟨hU', hv⟩

section Cuspidal

variable [CompactSpace (AdeleQuotient F)]

/-- `S` is weakly associated with the actual full cuspidal class `π` of `GL_{r+1}` over `F`:
some spectral system genuinely attached to `π` by a cuspidal spectral presentation is weakly
associated with `S`. The form-carrier universe of `π` is that of `F`; the universe `uP` of
the presentation's local factors is independent of the carrier universe of `S`. -/
def IsWeaklyAssociatedClass {r : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (π : Automorphic.CuspidalOperatorRealization.IsoClass F r) : Prop :=
  ∃ s : SpectralSystem (FinitePlace F) (r + 1),
    Automorphic.CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{u, uP} π s ∧
      IsWeaklyAssociated S s

/-- The class relation can be witnessed by a presentation of any actual representative. -/
theorem isWeaklyAssociatedClass_isoClass_iff {r : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (T : Automorphic.CuspidalOperatorRealization F r) :
    IsWeaklyAssociatedClass.{u, uV, uP} S T.isoClass ↔
      ∃ P : Automorphic.CuspidalSpectralPresentation.{u, uP} T,
        IsWeaklyAssociated S P.spectralSystem := by
  constructor
  · rintro ⟨s, hs, h⟩
    obtain ⟨P, rfl⟩ :=
      (Automorphic.CuspidalOperatorRealization.IsoClass.hasSpectralSystem_iff T s).mp hs
    exact ⟨P, h⟩
  · rintro ⟨P, h⟩
    exact ⟨P.spectralSystem,
      (Automorphic.CuspidalOperatorRealization.IsoClass.hasSpectralSystem_iff T _).mpr
        ⟨P, rfl⟩, h⟩

/-- The class relation depends only on the equivalence class of `S`. -/
theorem IsWeaklyAssociatedClass.of_equiv {r : ℕ}
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    {S' : FiniteRepresentation.{0, u, uW} ℂ (RelativeWeilGroup c F E)}
    {π : Automorphic.CuspidalOperatorRealization.IsoClass F r}
    (φ : FiniteRepresentation.Equiv S S') (h : IsWeaklyAssociatedClass.{u, uV, uP} S π) :
    IsWeaklyAssociatedClass.{u, uW, uP} S' π := by
  rcases h with ⟨s, hs, h⟩
  exact ⟨s, hs, h.of_equiv φ⟩

end Cuspidal

end RelativeWeilGroup

end Langlands.ClassField.Global
