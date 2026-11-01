import Langlands.AlgebraicGeometry.Modules.IntegralIdealFiltration.Killed
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-! # A minimal associated point of a quasi-coherent module -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules

namespace IntegralIdealFiltration

open AffineVanishing QuasicoherentLocal Scheme.IdealSheafData

variable {X : Scheme.{u}} {Q : X.Modules}

/-- A nonzero section over an affine open with noetherian sections has a multiple whose
annihilator is a prime ideal. -/
lemma exists_isPrime_annihilator {W : X.Opens} [IsNoetherianRing Γ(X, W)] (t : Γ(Q, W))
    (ht : t ≠ 0) :
    ∃ (b : Γ(X, W)) (P : Ideal Γ(X, W)), P.IsPrime ∧ ∀ c, c • (b • t) = 0 ↔ c ∈ P := by
  let N := Submodule.span Γ(X, W) {t}
  have hx : (⟨t, Submodule.mem_span_singleton_self t⟩ : N) ≠ 0 := fun h =>
    ht (congrArg Subtype.val h)
  obtain ⟨P, hP, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing Γ(X, W) _ hx
  obtain ⟨hPp, y, rfl⟩ := (isAssociatedPrime_iff).1 hP
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 y.2
  refine ⟨b, _, hPp, fun c => ?_⟩
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hb]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

/-- The vanishing ideal of the closure of a point of an affine open, on that affine open,
is the prime ideal of the point. -/
lemma vanishingIdeal_closure_fromSpec (V : X.affineOpens) (p : PrimeSpectrum Γ(X, V.1)) :
    (vanishingIdeal (Closeds.closure {V.2.fromSpec p})).ideal V = p.asIdeal := by
  rw [vanishingIdeal_ideal, Closeds.coe_closure,
    V.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      V.2.fromSpec.continuous,
    ← Set.image_singleton, Set.preimage_image_eq _ V.2.fromSpec.isOpenEmbedding.injective,
    PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton]

/-- A point of an affine open lies in a closed set if its prime contains the vanishing ideal. -/
lemma fromSpec_mem_of_le (V : X.affineOpens) (Zc : Closeds X) (p : PrimeSpectrum Γ(X, V.1))
    (h : (vanishingIdeal Zc).ideal V ≤ p.asIdeal) : V.2.fromSpec p ∈ Zc := by
  rw [vanishingIdeal_ideal] at h
  have hp : p ∈ PrimeSpectrum.zeroLocus
      (PrimeSpectrum.vanishingIdeal (V.2.fromSpec ⁻¹' (Zc : Set X)) : Set Γ(X, V.1)) := h
  rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    (Zc.isClosed.preimage V.2.fromSpec.continuous).closure_eq] at hp
  exact hp

variable (Q) in
/-- A closed set carrying a nonzero affine section killed by its vanishing ideal. -/
def Good (Zc : Closeds X) : Prop :=
  ∃ (V : X.affineOpens) (t : Γ(Q, V.1)), t ≠ 0 ∧
    ∀ c ∈ (vanishingIdeal Zc).ideal V, c • t = 0

/-- A nonzero affine section has a multiple with prime annihilator `p`; the closure of the
point `p` is then good. -/
lemma exists_good (V : X.affineOpens) [IsNoetherianRing Γ(X, V.1)] (t : Γ(Q, V.1))
    (ht : t ≠ 0) :
    ∃ (b : Γ(X, V.1)) (p : PrimeSpectrum Γ(X, V.1)),
      (∀ c, c • (b • t) = 0 ↔ c ∈ p.asIdeal) ∧ Good Q (Closeds.closure {V.2.fromSpec p}) := by
  obtain ⟨b, P, hP, hann⟩ := exists_isPrime_annihilator t ht
  refine ⟨b, ⟨P, hP⟩, hann, V, b • t, fun h0 => hP.ne_top ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one]
    exact (hann 1).1 (by rw [h0, smul_zero])
  · rw [vanishingIdeal_closure_fromSpec]
    exact fun c hc => (hann c).2 hc

/-- If `t` is killed by the vanishing ideal of `Zc` and `p` is the annihilator of a multiple
of `t`, then the closure of the point `p` lies in `Zc`. -/
lemma closure_le_of_annihilator (V : X.affineOpens) (t : Γ(Q, V.1)) (b : Γ(X, V.1))
    (p : PrimeSpectrum Γ(X, V.1)) (hann : ∀ c, c • (b • t) = 0 ↔ c ∈ p.asIdeal)
    {Zc : Closeds X} (hk : ∀ c ∈ (vanishingIdeal Zc).ideal V, c • t = 0) :
    Closeds.closure {V.2.fromSpec p} ≤ Zc := by
  have hx : V.2.fromSpec p ∈ Zc := by
    apply fromSpec_mem_of_le
    intro c hc
    apply (hann c).1
    rw [smul_comm, hk c hc, smul_zero]
  intro y hy
  exact closure_minimal (Set.singleton_subset_iff.2 hx) Zc.isClosed hy

/-- Every nonzero quasi-coherent module on a noetherian scheme has a section over an affine
open with prime annihilator `p`, such that the module is torsion free relative to the closure
of the point `p`: a section killed by the vanishing ideal which vanishes on all affine opens
inside the given affine open is zero. -/
theorem exists_minimal_witness [IsNoetherian X] [Q.IsQuasicoherent] (hQ : ¬ IsZero Q) :
    ∃ (U : X.affineOpens) (s : Γ(Q, U.1)) (p : PrimeSpectrum Γ(X, U.1)),
      (∀ c, c • s = 0 ↔ c ∈ p.asIdeal) ∧
      ∀ (W : X.Opens) (t : Γ(Q, W)),
        Killed (vanishingIdeal (Closeds.closure {U.2.fromSpec p})) t →
        (∀ (V : X.affineOpens) (hV : V.1 ≤ W ⊓ U.1), Cech.res (hV.trans inf_le_left) t = 0) →
        t = 0 := by
  classical
  have hne : ∃ (V : X.affineOpens) (t : Γ(Q, V.1)), t ≠ 0 := by
    by_contra h
    push Not at h
    apply hQ
    apply NoetherianVanishing.isZero_of_vanishesOn_top
    intro W _ t
    exact eq_zero_of_forall_affine t fun V hV => h V _
  obtain ⟨V₀, t₀, ht₀⟩ := hne
  have := IsLocallyNoetherian.component_noetherian V₀
  obtain ⟨b₀, p₀, -, hgood₀⟩ := exists_good V₀ t₀ ht₀
  obtain ⟨Zc, hZc, hmin⟩ := (wellFounded_lt (α := Closeds X)).has_min {Zc | Good Q Zc}
    ⟨_, hgood₀⟩
  obtain ⟨V, t, ht, hk⟩ := hZc
  have := IsLocallyNoetherian.component_noetherian V
  obtain ⟨b, p, hann, hgood⟩ := exists_good V t ht
  have hle := closure_le_of_annihilator V t b p hann hk
  have heq : Closeds.closure {V.2.fromSpec p} = Zc :=
    (lt_or_eq_of_le hle).resolve_left (hmin _ hgood)
  refine ⟨V, b • t, p, hann, ?_⟩
  intro W t' hk' hvan
  rw [heq] at hk'
  apply eq_zero_of_forall_affine t'
  intro V' hV'
  by_contra hne'
  have := IsLocallyNoetherian.component_noetherian V'
  obtain ⟨b', p', hann', hgood'⟩ := exists_good V' _ hne'
  have hle' := closure_le_of_annihilator V' _ b' p' hann' (fun c hc => hk' V' hV' c hc)
  have heq' : Closeds.closure {V'.2.fromSpec p'} = Zc :=
    (lt_or_eq_of_le hle').resolve_left (hmin _ hgood')
  have hx : V'.2.fromSpec p' = V.2.fromSpec p := by
    have h2 : closure ({V'.2.fromSpec p'} : Set X) = closure {V.2.fromSpec p} :=
      congrArg (fun C : Closeds X => (C : Set X)) (heq'.trans heq.symm)
    exact (inseparable_iff_closure_eq.2 h2).eq
  have hxV' : V.2.fromSpec p ∈ V'.1 := by
    have h := Set.mem_range_self (f := ⇑V'.2.fromSpec) p'
    rw [V'.2.range_fromSpec, hx] at h
    exact h
  have hxV : V.2.fromSpec p ∈ V.1 := by
    have h := Set.mem_range_self (f := ⇑V.2.fromSpec) p
    rw [V.2.range_fromSpec] at h
    exact h
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter V'.2 V.2 _ ⟨hxV', hxV⟩
  have hDle : X.basicOpen f ≤ W ⊓ V.1 :=
    le_inf ((X.basicOpen_le f).trans hV') (hfg ▸ X.basicOpen_le g)
  have h0 := hvan ⟨X.basicOpen f, V'.2.basicOpen f⟩ hDle
  have h1 : Cech.res (X.basicOpen_le f) (b' • Cech.res hV' t') = 0 := by
    rw [res_smul, Cech.res_res]
    change rres (X.basicOpen_le f) b' • Cech.res (hDle.trans inf_le_left) t' = 0
    rw [h0, smul_zero]
  obtain ⟨n, hn⟩ := (isLocalizingAt_of_isQuasicoherent V'.2 Q).exists_pow_smul_eq_zero f _ h1
  have hf : f ∈ p'.asIdeal := p'.isPrime.mem_of_pow_mem n ((hann' _).1 hn)
  have hx' : p' ∈ V'.2.fromSpec ⁻¹ᵁ X.basicOpen f := by
    change V'.2.fromSpec p' ∈ X.basicOpen f
    rw [hx]
    exact hxf
  rw [V'.2.fromSpec_preimage_basicOpen] at hx'
  exact hx' hf

end IntegralIdealFiltration

end Langlands.AlgebraicGeometry.Modules
