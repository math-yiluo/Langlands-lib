import Langlands.Representation.Character.SeparationStatement
import Langlands.Representation.CompactCoefficient.FixedLevelFiniteness
import Langlands.Representation.Hecke.CornerDetermination
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.SimpleModule.Basic

/-! # Character separation for irreducible admissible representations -/

noncomputable section

namespace Langlands

open MeasureTheory

universe uG uV uW

namespace CharacterSeparation

section Algebra

variable {A : Type*} [Ring A] [Algebra ℂ A]
variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
variable {N : Type*} [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]

/-- Two simple modules, finite-dimensional over `ℂ`, on which every algebra element has
the same trace are isomorphic. Otherwise the Jacobson density theorem for the semisimple
module `M × N` gives an element acting as the identity on `M` and as zero on `N`. -/
theorem nonempty_linearEquiv_of_trace_eq [FiniteDimensional ℂ M] [FiniteDimensional ℂ N]
    [IsSimpleModule A M] [IsSimpleModule A N]
    (h : ∀ r : A, LinearMap.trace ℂ M (DistribSMul.toLinearMap ℂ M r) =
      LinearMap.trace ℂ N (DistribSMul.toLinearMap ℂ N r)) :
    Nonempty (M ≃ₗ[A] N) := by
  by_contra hne
  have hMN : ∀ f : M →ₗ[A] N, f = 0 := fun f =>
    f.bijective_or_eq_zero.resolve_left fun hf => hne ⟨LinearEquiv.ofBijective f hf⟩
  have hNM : ∀ f : N →ₗ[A] M, f = 0 := fun f =>
    f.bijective_or_eq_zero.resolve_left fun hf => hne ⟨(LinearEquiv.ofBijective f hf).symm⟩
  have hsemi : IsSemisimpleModule A (M × N) := by
    have hsup := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl A M N))
      (IsSemisimpleModule.range (LinearMap.inr A M N))
    rw [LinearMap.sup_range_inl_inr] at hsup
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  have h1 : ∀ (φ : Module.End A (M × N)) (n : N), (φ (0, n)).1 = 0 := fun φ n =>
    LinearMap.congr_fun (hNM ((LinearMap.fst A M N).comp (φ.comp (LinearMap.inr A M N)))) n
  have h2 : ∀ (φ : Module.End A (M × N)) (m : M), (φ (m, 0)).2 = 0 := fun φ m =>
    LinearMap.congr_fun (hMN ((LinearMap.snd A M N).comp (φ.comp (LinearMap.inl A M N)))) m
  -- The projection onto `M` commutes with every `A`-endomorphism of `M × N`.
  let p : Module.End (Module.End A (M × N)) (M × N) :=
    { toFun := fun x => (x.1, 0)
      map_add' := fun x y => by simp
      map_smul' := fun φ x => by
        change ((φ x).1, (0 : N)) = φ (x.1, 0)
        have hx : x = (x.1, 0) + (0, x.2) := by simp
        refine Prod.ext ?_ (h2 φ x.1).symm
        conv_lhs => rw [hx]
        rw [map_add, Prod.fst_add, h1, add_zero] }
  let bM := Module.finBasis ℂ M
  let bN := Module.finBasis ℂ N
  classical
  obtain ⟨r, hr⟩ := jacobson_density p
    ((Finset.univ.image fun i => ((bM i, 0) : M × N)) ∪
      (Finset.univ.image fun j => ((0, bN j) : M × N)))
  have hrM : DistribSMul.toLinearMap ℂ M r = LinearMap.id := by
    refine bM.ext fun i => ?_
    have hi := hr (bM i, 0) (Finset.mem_union_left _ (Finset.mem_image_of_mem _
      (Finset.mem_univ i)))
    have := congrArg Prod.fst hi
    simpa [p] using this.symm
  have hrN : DistribSMul.toLinearMap ℂ N r = 0 := by
    refine bN.ext fun j => ?_
    have hj := hr (0, bN j) (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_univ j)))
    have := congrArg Prod.snd hj
    simpa [p] using this.symm
  have htr := h r
  rw [hrM, hrN, LinearMap.trace_id, map_zero, Nat.cast_eq_zero] at htr
  have : Nontrivial M := IsSimpleModule.nontrivial A M
  exact (Module.finrank_pos (R := ℂ) (M := M)).ne' htr

end Algebra

section Separation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- An irreducible representation has a nonzero carrier. -/
theorem nontrivial_of_isIrreducible {ρ : Representation ℂ G V} (hρirr : ρ.IsIrreducible) :
    Nontrivial V := by
  have := hρirr
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have : Subsingleton (Submodule ℂ V) := (Submodule.subsingleton_iff ℂ).mpr hV
  exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

omit [MeasurableSpace G] [BorelSpace G] in
/-- Two smooth vectors are fixed by a common compact open subgroup. -/
theorem exists_compactOpen_fixed {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (v : V) (w : W) :
    ∃ (K : OpenSubgroup G) (_ : IsCompact (K : Set G)),
      v ∈ fixedVectors ρ K.toSubgroup ∧ w ∈ fixedVectors σ K.toSubgroup := by
  obtain ⟨U, hU⟩ := hρ v
  obtain ⟨U', hU'⟩ := hσ w
  obtain ⟨K, hKU, hK, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ (U ⊓ U')
  exact ⟨K, hK, fun k => hU ⟨k, (hKU k.property).1⟩, fun k => hU' ⟨k, (hKU k.property).2⟩⟩

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- In an irreducible smooth representation, a nonzero `K`-fixed vector generates all
`K`-fixed vectors under the actual Hecke corner. -/
theorem exists_cornerAction_eq {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    (hρirr : ρ.IsIrreducible) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    {a : fixedVectors ρ K.toSubgroup} (ha : a ≠ 0) (b : fixedVectors ρ K.toSubgroup) :
    ∃ e : Hecke.HeckeAlgebra.Corner μ K hK, Hecke.cornerAction μ ρ hρ K hK e a = b := by
  have ha' : (a : V) ≠ 0 := fun h => ha (Subtype.ext h)
  obtain ⟨c, hc⟩ := Hecke.orbitCombination_surjective hρirr ha' (b : V)
  refine ⟨Hecke.translateCombination μ K hK c, ?_⟩
  rw [Hecke.cornerAction_translateCombination, hc, Hecke.fixedProjection_fixed]

/-- The character of an admissible representation on a corner element is the trace of
the corner action on the fixed vectors. -/
theorem distribution_corner (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (e : Hecke.HeckeAlgebra.Corner μ K hK) :
    Character.distribution μ ρ hρ
        (Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK e)) =
      LinearMap.trace ℂ (fixedVectors ρ K.toSubgroup) (Hecke.cornerAction μ ρ hρ.1 K hK e) := by
  have h := Character.distribution_eq_fixedVectors μ ρ hρ K (J := K.toSubgroup)
    (f := Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK e))
    e.property
  refine h.trans ?_
  congr 1

/-- Irreducible admissible representations with equal distribution characters are
equivalent. -/
theorem nonempty_equiv_of_distribution_eq {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hρ : IsAdmissible ρ) (hσ : IsAdmissible σ)
    (hρirr : ρ.IsIrreducible) (hσirr : σ.IsIrreducible)
    (hdist : Character.distribution μ ρ hρ = Character.distribution μ σ hσ) :
    Nonempty (ρ.Equiv σ) := by
  have := nontrivial_of_isIrreducible hρirr
  have := nontrivial_of_isIrreducible hσirr
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨K, hK, hvK, hwK⟩ := exists_compactOpen_fixed hρ.1 hσ.1 v w
  let _ := Hecke.cornerModule μ ρ hρ.1 K hK
  let _ := Hecke.cornerModule μ σ hσ.1 K hK
  have := Hecke.cornerModule_isScalarTower μ ρ hρ.1 K hK
  have := Hecke.cornerModule_isScalarTower μ σ hσ.1 K hK
  have := hρ.2 K
  have := hσ.2 K
  have hneρ : fixedVectors ρ K.toSubgroup ≠ ⊥ := fun h =>
    hv ((Submodule.mem_bot ℂ).mp (h ▸ hvK))
  have hneσ : fixedVectors σ K.toSubgroup ≠ ⊥ := fun h =>
    hw ((Submodule.mem_bot ℂ).mp (h ▸ hwK))
  have := CompactCoefficientClass.isSimpleModule_fixedVectors μ ρ hρ.1 K hK hρirr hneρ
  have := CompactCoefficientClass.isSimpleModule_fixedVectors μ σ hσ.1 K hK hσirr hneσ
  obtain ⟨φ⟩ := nonempty_linearEquiv_of_trace_eq
    (A := Hecke.HeckeAlgebra.Corner μ K hK)
    (M := fixedVectors ρ K.toSubgroup) (N := fixedVectors σ K.toSubgroup) fun r => by
      have hr := congrArg (fun T => T (Hecke.HeckeAlgebra.toTestFunction μ
        (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK r))) hdist
      simp only [distribution_corner] at hr
      exact hr
  let a : fixedVectors ρ K.toSubgroup := ⟨v, hvK⟩
  have ha : (a : V) ≠ 0 := hv
  have hb : ((φ a : fixedVectors σ K.toSubgroup) : W) ≠ 0 := by
    intro h
    apply ha
    have h0 : φ a = 0 := Subtype.ext h
    simpa using congrArg Subtype.val (φ.map_eq_zero_iff.mp h0)
  refine Hecke.nonempty_equiv_of_cornerAction_eq_zero_iff μ K hK hρ.1 hρirr hσ.1 hσirr
    a (φ a) ha hb fun e => ?_
  have hφ : φ (Hecke.cornerAction μ ρ hρ.1 K hK e a) =
      Hecke.cornerAction μ σ hσ.1 K hK e (φ a) := φ.map_smul e a
  rw [← hφ, φ.map_eq_zero_iff]

end Separation

end CharacterSeparation

/-- Bernstein--Zelevinsky (1976), Corollary 2.20: irreducible admissible representations
have equal distribution characters exactly when they are equivalent. -/
theorem characterSeparation : CharacterSeparationStatement.{uG, uV, uW} := by
  intro G _ _ _ _ _ _ _ _ μ _ _ V _ _ W _ _ ρ σ hρ hσ hρirr hσirr
  refine ⟨fun hdist => ?_, fun ⟨E, hE⟩ =>
    Character.distribution_eq_of_equivariant μ ρ hρ σ hσ E hE⟩
  obtain ⟨e⟩ := CharacterSeparation.nonempty_equiv_of_distribution_eq μ hρ hσ hρirr hσirr hdist
  exact ⟨e.toLinearEquiv, fun g v => LinearMap.congr_fun (e.isIntertwining' g) v⟩

end Langlands
