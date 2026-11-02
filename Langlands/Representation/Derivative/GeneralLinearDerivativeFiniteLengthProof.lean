import Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthStatement
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
import Langlands.Representation.Derivative.DerivativeEquivTransport
import Langlands.Representation.Derivative.ProductDerivativesFiniteLength
import Langlands.Representation.Classification.IrreducibleProductEmbedding
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Filtration.RepresentationLength

/-!
# Finite-length preservation by the general-linear derivatives

An exact functor between smooth representation categories that sends every
irreducible representation to one of finite length sends every finite-length
representation to one of finite length, by induction on the length. An irreducible
representation of `GL_N`, `N > 0`, embeds in a normalized product of supercuspidal
representations; the derivative is exact, so the derivative of the irreducible
representation embeds in the derivative of the product.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV uG uH

/-! ## Reduction to irreducible inputs -/

section Reduction

variable {G : Type uG} [Group G] [TopologicalSpace G] {H : Type uH} [Group H] [TopologicalSpace H]

theorem hasFiniteLength_iff_repLength_ne_top (A : SmoothRep.{0, uG, uV} ℂ G) :
    A.HasFiniteLength ↔ repLength A.representation ≠ ⊤ :=
  Module.length_ne_top_iff.symm

/-- An irreducible representation has length one. -/
theorem hasFiniteLength_of_isIrreducible {A : SmoothRep.{0, uG, uV} ℂ G}
    (hA : A.IsIrreducible) : A.HasFiniteLength := by
  rw [hasFiniteLength_iff_repLength_ne_top, repLength_eq_one_iff.mpr hA]
  exact ENat.one_ne_top

omit [TopologicalSpace G] in
/-- A nonzero representation that is not irreducible has an invariant subspace
other than `0` and the whole space. -/
theorem exists_ne_bot_ne_top_of_not_isIrreducible {V : Type uV} [AddCommGroup V]
    [Module ℂ V] [Nontrivial V] {ρ : Representation ℂ G V} (h : ¬ ρ.IsIrreducible) :
    ∃ S : Subrepresentation ρ, S ≠ ⊥ ∧ S ≠ ⊤ := by
  by_contra hS
  push Not at hS
  apply h
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    intro h'
    have hx' : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h'] at hx'
    exact hx ((Submodule.mem_bot ℂ).mp hx')
  exact { toNontrivial := ⟨⟨⊥, ⊤, hne⟩⟩
          eq_bot_or_eq_top := fun S => (em (S = ⊥)).imp_right (hS S) }

/-- The image of a representation with zero carrier under an exact functor has zero
carrier. -/
theorem map_subsingleton_of_exact
    {J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H}
    (hJ : Mirabolic.MapsShortExactIntertwiners J) (A : SmoothRep.{0, uG, uV} ℂ G)
    [Subsingleton A] : Subsingleton (J.obj A) := by
  have hA : LinearMap.range (SmoothRep.hom (𝟙 A)).toLinearMap =
      LinearMap.ker (SmoothRep.hom (𝟙 A)).toLinearMap :=
    @Subsingleton.elim _ ((Submodule.subsingleton_iff ℂ).mpr inferInstance) _ _
  have h := (hJ A A A (𝟙 A) (𝟙 A) (fun _ _ h => h) (fun x => ⟨x, rfl⟩) hA).2.1
  have hx : ∀ x : J.obj A, x = 0 := by
    intro x
    have hmem : x ∈ LinearMap.range (SmoothRep.hom (J.map (𝟙 A))).toLinearMap :=
      ⟨x, by rw [J.map_id]; rfl⟩
    rw [h, LinearMap.mem_ker] at hmem
    rw [J.map_id] at hmem
    exact hmem
  exact ⟨fun x y => (hx x).trans (hx y).symm⟩

/-- An exact functor that sends every irreducible representation to one of finite
length sends every finite-length representation to one of finite length. -/
theorem map_hasFiniteLength_of_isIrreducible
    {J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H}
    (hJ : Mirabolic.MapsShortExactIntertwiners J)
    (hirr : ∀ A : SmoothRep.{0, uG, uV} ℂ G, A.IsIrreducible → (J.obj A).HasFiniteLength)
    (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.HasFiniteLength) :
    (J.obj A).HasFiniteLength := by
  suffices H : ∀ n : ℕ, ∀ A : SmoothRep.{0, uG, uV} ℂ G,
      repLength A.representation = n → (J.obj A).HasFiniteLength by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ((hasFiniteLength_iff_repLength_ne_top A).mp hA)
    exact H n A hn.symm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn
  by_cases h0 : n = 0
  · have hz : repLength A.representation = 0 := by rw [hn, h0, Nat.cast_zero]
    have : Subsingleton A := repLength_eq_zero_iff.mp hz
    have := map_subsingleton_of_exact hJ A
    rw [hasFiniteLength_iff_repLength_ne_top, repLength_eq_zero_iff.mpr this]
    exact ENat.zero_ne_top
  have hpos : 0 < repLength A.representation := by
    rw [hn]
    exact_mod_cast Nat.pos_of_ne_zero h0
  have : Nontrivial A := repLength_pos_iff.mp hpos
  by_cases hirrA : A.IsIrreducible
  · exact hirr A hirrA
  obtain ⟨S, hS0, hS1⟩ := exists_ne_bot_ne_top_of_not_isIrreducible hirrA
  let i := SmoothRep.subtype A S
  let q := SmoothRep.mkQ A S
  have hi : Function.Injective (SmoothRep.hom i) := SmoothRep.subtype_injective A S
  have hq : Function.Surjective (SmoothRep.hom q) := SmoothRep.mkQ_surjective A S
  have hex : LinearMap.range (SmoothRep.hom i).toLinearMap =
      LinearMap.ker (SmoothRep.hom q).toLinearMap :=
    (Submodule.range_subtype S.toSubmodule).trans (Submodule.ker_mkQ S.toSubmodule).symm
  have hlen := repLength_eq_add_of_exact (SmoothRep.hom i) (SmoothRep.hom q) hi hq hex
  rw [hn] at hlen
  have ha0 : repLength (SmoothRep.subrepresentation A S).representation ≠ 0 := by
    rw [ne_eq, repLength_eq_zero_iff]
    intro hsub
    exact hS0 (Subrepresentation.toSubmodule_injective
      (Submodule.subsingleton_iff_eq_bot.mp hsub))
  have hb0 : repLength (SmoothRep.quotient A S).representation ≠ 0 := by
    rw [ne_eq, repLength_eq_zero_iff]
    intro hquot
    exact hS1 (Subrepresentation.toSubmodule_injective
      ((Submodule.Quotient.subsingleton_iff).mp hquot))
  have haT : repLength (SmoothRep.subrepresentation A S).representation ≠ ⊤ := by
    intro h
    rw [h, top_add] at hlen
    exact ENat.natCast_ne_top n hlen
  have hbT : repLength (SmoothRep.quotient A S).representation ≠ ⊤ := by
    intro h
    rw [h, add_top] at hlen
    exact ENat.natCast_ne_top n hlen
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp haT
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hbT
  rw [← ha, ← hb] at hlen
  rw [← ha] at ha0
  rw [← hb] at hb0
  have hnab : n = a + b := by exact_mod_cast hlen
  have ha0' : a ≠ 0 := by exact_mod_cast ha0
  have hb0' : b ≠ 0 := by exact_mod_cast hb0
  have hJS := ih a (by omega) _ ha.symm
  have hJQ := ih b (by omega) _ hb.symm
  obtain ⟨hJi, hJex, hJq⟩ := hJ _ _ _ i q hi hq hex
  have hlenJ := repLength_eq_add_of_exact _ _ hJi hJq hJex
  rw [hasFiniteLength_iff_repLength_ne_top] at hJS hJQ ⊢
  rw [hlenJ]
  exact WithTop.add_ne_top.mpr ⟨hJS, hJQ⟩

end Reduction

/-! ## The irreducible case and the assembly -/

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The derivative of an irreducible representation has finite length, given finite
length of the derivatives of normalized products of supercuspidal representations at
carrier universe `max uF uV`. -/
theorem generalLinearDerivative_hasFiniteLength_of_isIrreducible
    (hP : letI := T.topology
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ} (B : BlockShape n), 0 < n →
        ∀ (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
          (∀ i, (σ i).IsIrreducible ∧ IsSupercuspidal (σ i).representation) →
            ∀ (k : ℕ) (hk : k ≤ n),
              ((generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj
                ((T.normalizedProductInductionFunctor B).obj σ)).HasFiniteLength)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ) (hk : k ≤ N)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier))
    (hA : letI := T.topology; A.IsIrreducible) :
    letI := T.topology
    ((generalLinearDerivative.{uF, uV} T ψ N k hk).obj A).HasFiniteLength := by
  let _ := T.topology
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : k = 0 := Nat.le_zero.mp hk
    exact hasFiniteLength_of_isIrreducible hA
  obtain ⟨B, C, j, hj⟩ :=
    Classification.irreducible_supercuspidalProduct_embedding.{uF, uV, max uF uV}
      F T N hN A hA
  let P := (T.normalizedProductInductionFunctor B).obj (fun i => (C i).obj)
  let A' := SmoothRep.universeLift.{uF} A
  let e := SmoothRep.universeLiftEquiv.{uF} A
  let j' : A' ⟶ P := SmoothRep.ofHom (j.comp e.symm.toIntertwiningMap)
  have hj' : Function.Injective (SmoothRep.hom j') := hj.comp e.symm.injective
  have hD := generalLinearDerivativeExactness.{uF, max uF uV} F T ψ N k hk
  have hinj := (hD _ _ _ j' (SmoothRep.mkQ P (SmoothRep.hom j').range) hj'
    (SmoothRep.mkQ_surjective _ _) (Submodule.ker_mkQ _).symm).1
  have hPfin := hP ψ B hN (fun i => (C i).obj) (fun i => (C i).property) k hk
  have hA' : ((generalLinearDerivative.{uF, max uF uV} T ψ N k hk).obj A').HasFiniteLength :=
    IsFiniteLength.of_injective hPfin
      (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (SmoothRep.hom ((generalLinearDerivative.{uF, max uF uV} T ψ N k hk).map j'))) hinj
  exact (generalLinearDerivative_hasFiniteLength_iff_of_equiv T ψ N k hk A A' e).mpr hA'

/-- The statement, given finite length of the derivatives of normalized products of
supercuspidal representations at carrier universe `max uF uV`. -/
theorem generalLinearDerivativeFiniteLength_of_products
    (hP : letI := T.topology
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ} (B : BlockShape n), 0 < n →
        ∀ (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
          (∀ i, (σ i).IsIrreducible ∧ IsSupercuspidal (σ i).representation) →
            ∀ (k : ℕ) (hk : k ≤ n),
              ((generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj
                ((T.normalizedProductInductionFunctor B).obj σ)).HasFiniteLength) :
    GeneralLinearDerivativeFiniteLengthStatement.{uF, uV} F T := by
  let _ := T.topology
  intro ψ N k hk A hA
  exact map_hasFiniteLength_of_isIrreducible
    (generalLinearDerivativeExactness.{uF, uV} F T ψ N k hk)
    (generalLinearDerivative_hasFiniteLength_of_isIrreducible F T hP ψ N k hk) A hA

/-- Every general-linear derivative sends finite-length smooth representations to
finite-length smooth representations. -/
theorem generalLinearDerivativeFiniteLength :
    GeneralLinearDerivativeFiniteLengthStatement.{uF, uV} F T :=
  generalLinearDerivativeFiniteLength_of_products F T
    (fun ψ {_} B hn σ hσ k hk => productDerivativesFiniteLength.{uF, uV} T ψ B hn σ hσ k hk)

end Langlands.Derivative
