import Langlands.VirtualRepresentation.ExactInductionTwist
import Langlands.Weil.Representation.SubquotientContinuity

/-!
# Mackey's formula on continuous exact virtual groups

For a finite-index subgroup `H` of `G`, a homomorphism `ι : L → G` and a finite
family of double-coset representatives `x u` for `H \ G / ι(L)`, the restriction
along `ι` of a representation induced from `H` is equivalent to the product over
`u` of the representations induced from `S u = ι⁻¹(x u⁻¹ H x u)` of the
conjugated restrictions. On continuous exact virtual groups this gives the sum
formula; compare Serre (1977), §7.3, Proposition 22.
-/

noncomputable section

set_option autoImplicit false

universe uK uG uV

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

section Pi

variable {L : Type uG} [Group L] [TopologicalSpace L] {U : Type*}
  (V : ContinuousObjects.{uG, uV} L) (W : U → ContinuousObjects.{uG, uV} L)
  (e : V.val ≃ₗ[ℂ] ((u : U) → (W u).val))
  (he : ∀ (ℓ : L) (v : V.val) (u : U),
    e (V.val.representation ℓ v) u = (W u).val.representation ℓ (e v u))

/-- The invariant subspace of vectors whose coordinates outside `s` vanish. -/
private def piSupport (s : Finset U) : Subrepresentation V.val.representation where
  toSubmodule :=
    { carrier := {v | ∀ u, u ∉ s → e v u = 0}
      add_mem' := fun {a b} ha hb u hu => by
        simp only [map_add, Pi.add_apply, ha u hu, hb u hu, add_zero]
      zero_mem' := fun u _ => by simp
      smul_mem' := fun c v hv u hu => by
        simp only [map_smul, Pi.smul_apply, hv u hu, smul_zero] }
  apply_mem_toSubmodule ℓ v hv u hu := by
    rw [he, show e v u = 0 from hv u hu, map_zero]

private theorem mem_piSupport {s : Finset U} {v : V.val} :
    v ∈ (piSupport V W e he s).toSubmodule ↔ ∀ u, u ∉ s → e v u = 0 := Iff.rfl

private theorem class_piSupport_empty :
    ofRepresentation _ (continuousSubrepresentation V (piSupport V W e he ∅)) = 0 := by
  let B := continuousSubrepresentation V (piSupport V W e he ∅)
  have h0 : ∀ a : V.val, a ∈ (piSupport V W e he ∅).toSubmodule → a = 0 := fun a ha =>
    e.injective (funext fun u => by rw [map_zero]; exact ha u (Finset.notMem_empty u))
  have hsub : Subsingleton B.val := ⟨by
    rintro ⟨v, hv⟩ ⟨w, hw⟩
    exact Subtype.ext ((h0 v hv).trans (h0 w hw).symm)⟩
  let f : B.val.representation.IntertwiningMap B.val.representation := 0
  have h : IsShortExact f f := by
    refine ⟨fun _ _ _ => Subsingleton.elim _ _, fun a => ⟨0, Subsingleton.elim _ _⟩, ?_⟩
    ext a
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  have hadd := ofRepresentation_shortExact
    (fun C : FiniteRepresentation.{0, uG, uV} ℂ L => C.IsContinuous)
    (A := B) (B := B) (C := B) h
  exact add_eq_left.mp hadd.symm

private theorem class_piSupport_insert [DecidableEq U] {a : U} {s : Finset U} (ha : a ∉ s) :
    ofRepresentation _ (continuousSubrepresentation V (piSupport V W e he (insert a s))) =
      ofRepresentation _ (continuousSubrepresentation V (piSupport V W e he s)) +
        ofRepresentation _ (W a) := by
  have hle : (piSupport V W e he s).toSubmodule ≤ (piSupport V W e he (insert a s)).toSubmodule :=
    fun v hv u hu => hv u (fun h => hu (Finset.mem_insert_of_mem h))
  let f : (piSupport V W e he s).toRepresentation.IntertwiningMap
      (piSupport V W e he (insert a s)).toRepresentation :=
    { toLinearMap := Submodule.inclusion hle
      isIntertwining' _ := rfl }
  let g : (piSupport V W e he (insert a s)).toRepresentation.IntertwiningMap
      (W a).val.representation :=
    { toLinearMap := (LinearMap.proj a).comp
        (e.toLinearMap.comp (piSupport V W e he (insert a s)).toSubmodule.subtype)
      isIntertwining' ℓ := by
        ext v
        exact he ℓ v.1 a }
  apply ofRepresentation_shortExact _ (f := f) (g := g)
  refine ⟨Submodule.inclusion_injective hle, ?_, ?_⟩
  · intro w
    refine ⟨⟨e.symm (Pi.single a w), ?_⟩, ?_⟩
    · intro u hu
      have hne : u ≠ a := by
        rintro rfl
        exact hu (Finset.mem_insert_self _ s)
      rw [LinearEquiv.apply_symm_apply, Pi.single_eq_of_ne hne]
    · change e (e.symm (Pi.single a w)) a = w
      rw [LinearEquiv.apply_symm_apply, Pi.single_eq_same]
  · ext ⟨v, hv⟩
    constructor
    · rintro ⟨⟨w, hw⟩, hwv⟩
      have hvw : w = v := congrArg Subtype.val hwv
      subst hvw
      exact hw a ha
    · intro hg
      have hva : e v a = 0 := hg
      refine ⟨⟨v, fun u hu => ?_⟩, rfl⟩
      by_cases hua : u = a
      · exact hua ▸ hva
      · exact hv u (fun h => (Finset.mem_insert.mp h).elim hua hu)

include he in
/-- A continuous representation with an equivariant linear equivalence onto a
finite product of continuous representations has, in the continuous exact virtual
group, the class of the sum of the factors. The proof filters by the subspaces of
vectors supported on a growing set of coordinates; no equivariant splitting is
used beyond the given product structure. -/
theorem ofRepresentation_eq_sum_of_equiv_pi [Fintype U] :
    ofRepresentation _ V = ∑ u, ofRepresentation _ (W u) := by
  classical
  have key : ∀ s : Finset U,
      ofRepresentation _ (continuousSubrepresentation V (piSupport V W e he s)) =
        ∑ u ∈ s, ofRepresentation _ (W u) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact class_piSupport_empty V W e he
    | insert a s ha ih =>
      rw [class_piSupport_insert V W e he ha, ih, Finset.sum_insert ha, add_comm]
  rw [← key Finset.univ]
  apply ofRepresentation_eq_of_equiv
  exact
    { toLinearMap :=
        { toFun := fun v => ⟨v, fun u hu => absurd (Finset.mem_univ u) hu⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' _ := rfl
      invFun := fun v => v.1
      left_inv _ := rfl
      right_inv _ := rfl }

end Pi

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.FiniteRepresentation

section Mackey

variable {K : Type uK} [Field K] {G : Type uG} [Group G] (H : Subgroup G)
  {L : Type uG} [Group L] (ι : L →* G) {U : Type*}
  (x : U → G) (S : U → Subgroup L)
  (κ : ∀ u, S u →* H)
  (hκ : ∀ u (s : S u), (κ u s : G) = x u * ι s * (x u)⁻¹)

/-- Mackey's coordinates: an `H`-equivariant function on `G` is sent to its
restrictions to the double cosets `H x u ι(L)`, read as functions on `L`. -/
def mackeyMap (A : FiniteRepresentation.{uK, uG, uV} K H) :
    Representation.coindV H.subtype A.representation →ₗ[K]
      ((u : U) → Representation.coindV (S u).subtype (restrict (κ u) A).representation) where
  toFun f u :=
    ⟨fun ℓ => f.1 (x u * ι ℓ), fun s ℓ => by
      have h1 : x u * ι ((S u).subtype s * ℓ) = (H.subtype (κ u s)) * (x u * ι ℓ) := by
        simp only [Subgroup.coe_subtype, map_mul, hκ u s, mul_assoc, inv_mul_cancel_left]
      change f.1 (x u * ι ((S u).subtype s * ℓ)) = A.representation (κ u s) (f.1 (x u * ι ℓ))
      rw [h1]
      exact f.2 (κ u s) (x u * ι ℓ)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem mackeyMap_apply (A : FiniteRepresentation.{uK, uG, uV} K H)
    (f : Representation.coindV H.subtype A.representation) (u : U) (ℓ : L) :
    (mackeyMap H ι x S κ hκ A f u).1 ℓ = f.1 (x u * ι ℓ) := rfl

/-- The Mackey coordinates intertwine the restricted induced action with the
product of the induced actions. -/
theorem mackeyMap_intertwines [H.FiniteIndex] [∀ u, (S u).FiniteIndex]
    (A : FiniteRepresentation.{uK, uG, uV} K H) (ℓ₀ : L)
    (f : Representation.coindV H.subtype A.representation) (u : U) :
    mackeyMap H ι x S κ hκ A
        ((restrict ι (induce H A)).representation ℓ₀ f) u =
      (induce (S u) (restrict (κ u) A)).representation ℓ₀ (mackeyMap H ι x S κ hκ A f u) := by
  apply Subtype.ext
  funext ℓ
  change f.1 (x u * ι ℓ * ι ℓ₀) = f.1 (x u * ι (ℓ * ℓ₀))
  rw [map_mul, mul_assoc]

variable (hS : ∀ u (ℓ : L), x u * ι ℓ * (x u)⁻¹ ∈ H → ℓ ∈ S u)
  (hcover : ∀ g : G, ∃ (h : H) (u : U) (ℓ : L), g = h * (x u * ι ℓ))
  (hdisj : ∀ (h h' : H) (u u' : U) (ℓ ℓ' : L),
    (h : G) * (x u * ι ℓ) = h' * (x u' * ι ℓ') → u = u')

include hS hcover hdisj in
/-- The Mackey coordinates are bijective: the double cosets `H x u ι(L)` cover `G`
and are pairwise distinct, and `S u` is the stabilizer of the double coset
structure. -/
theorem mackeyMap_bijective (A : FiniteRepresentation.{uK, uG, uV} K H) :
    Function.Bijective (mackeyMap H ι x S κ hκ A) := by
  classical
  constructor
  · intro f f' hff
    apply Subtype.ext
    funext g
    obtain ⟨h, u, ℓ, rfl⟩ := hcover g
    have hu := congrArg (fun F => (F u).1 ℓ) hff
    change f.1 (x u * ι ℓ) = f'.1 (x u * ι ℓ) at hu
    change f.1 (H.subtype h * (x u * ι ℓ)) = f'.1 (H.subtype h * (x u * ι ℓ))
    rw [f.2 h, f'.2 h, hu]
  · intro F
    obtain ⟨Fv, hFv⟩ : ∃ Fv : U → L → A, ∀ u ℓ, Fv u ℓ = (F u).1 ℓ := ⟨_, fun _ _ => rfl⟩
    have hFeq : ∀ u (s : S u) (ℓ : L),
        Fv u ((s : L) * ℓ) = A.representation (κ u s) (Fv u ℓ) := by
      intro u s ℓ
      rw [hFv, hFv]
      exact (F u).2 s ℓ
    -- two decompositions of the same element give the same value
    have key : ∀ (h h' : H) (u u' : U) (ℓ ℓ' : L),
        (h : G) * (x u * ι ℓ) = h' * (x u' * ι ℓ') →
          A.representation h (Fv u ℓ) = A.representation h' (Fv u' ℓ') := by
      intro h h' u u' ℓ ℓ' e1
      obtain rfl : u = u' := hdisj h h' u u' ℓ ℓ' e1
      have hconj : x u * ι (ℓ * ℓ'⁻¹) * (x u)⁻¹ = (h : G)⁻¹ * h' := by
        rw [map_mul, map_inv]
        calc x u * (ι ℓ * (ι ℓ')⁻¹) * (x u)⁻¹
            = (h : G)⁻¹ * ((h : G) * (x u * ι ℓ)) * (x u * ι ℓ')⁻¹ := by group
          _ = (h : G)⁻¹ * h' := by rw [e1]; group
      have hmem : x u * ι (ℓ * ℓ'⁻¹) * (x u)⁻¹ ∈ H := by
        rw [hconj]
        exact H.mul_mem (H.inv_mem h.2) h'.2
      let s : S u := ⟨ℓ * ℓ'⁻¹, hS u _ hmem⟩
      have hks : κ u s = h⁻¹ * h' := Subtype.ext ((hκ u s).trans hconj)
      have hF := hFeq u s ℓ'
      rw [show (s : L) * ℓ' = ℓ from inv_mul_cancel_right ℓ ℓ', hks] at hF
      rw [hF, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    let dec : G → H × U × L := fun g =>
      (Classical.choose (hcover g), Classical.choose (Classical.choose_spec (hcover g)),
        Classical.choose (Classical.choose_spec (Classical.choose_spec (hcover g))))
    have hdec : ∀ g, g = ((dec g).1 : G) * (x (dec g).2.1 * ι (dec g).2.2) := fun g =>
      Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hcover g)))
    let f₀ : G → A := fun g => A.representation (dec g).1 (Fv (dec g).2.1 (dec g).2.2)
    have hwell : ∀ (h : H) (u : U) (ℓ : L),
        f₀ ((h : G) * (x u * ι ℓ)) = A.representation h (Fv u ℓ) := fun h u ℓ =>
      key _ _ _ _ _ _ (hdec ((h : G) * (x u * ι ℓ))).symm
    refine ⟨⟨f₀, fun h g => ?_⟩, ?_⟩
    · obtain ⟨h₁, u, ℓ, rfl⟩ := hcover g
      change f₀ ((h : G) * ((h₁ : G) * (x u * ι ℓ))) =
        A.representation h (f₀ ((h₁ : G) * (x u * ι ℓ)))
      rw [← mul_assoc, ← Subgroup.coe_mul, hwell, hwell, map_mul, Module.End.mul_apply]
    · funext u
      apply Subtype.ext
      funext ℓ
      change f₀ (x u * ι ℓ) = (F u).1 ℓ
      rw [← hFv]
      have := hwell 1 u ℓ
      rw [OneMemClass.coe_one, one_mul, map_one, Module.End.one_apply] at this
      exact this

/-- Mackey's equivalence, as a linear equivalence of the actual function spaces. -/
def mackeyEquiv (A : FiniteRepresentation.{uK, uG, uV} K H) :
    Representation.coindV H.subtype A.representation ≃ₗ[K]
      ((u : U) → Representation.coindV (S u).subtype (restrict (κ u) A).representation) :=
  LinearEquiv.ofBijective (mackeyMap H ι x S κ hκ A)
    (mackeyMap_bijective H ι x S κ hκ hS hcover hdisj A)

theorem mackeyEquiv_apply (A : FiniteRepresentation.{uK, uG, uV} K H)
    (f : Representation.coindV H.subtype A.representation) :
    mackeyEquiv H ι x S κ hκ hS hcover hdisj A f = mackeyMap H ι x S κ hκ A f :=
  LinearEquiv.ofBijective_apply _ _

end Mackey

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) [H.FiniteIndex] (hH : IsOpen (H : Set G))
  {L : Type uG} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  (ι : L →ₜ* G) {U : Type*} [Fintype U]
  (x : U → G) (S : U → Subgroup L) [∀ u, (S u).FiniteIndex]
  (hSo : ∀ u, IsOpen (S u : Set L))
  (κ : ∀ u, S u →ₜ* H)
  (hκ : ∀ u (s : S u), (κ u s : G) = x u * ι s * (x u)⁻¹)
  (hS : ∀ u (ℓ : L), x u * ι ℓ * (x u)⁻¹ ∈ H → ℓ ∈ S u)
  (hcover : ∀ g : G, ∃ (h : H) (u : U) (ℓ : L), g = h * (x u * ι ℓ))
  (hdisj : ∀ (h h' : H) (u u' : U) (ℓ ℓ' : L),
    (h : G) * (x u * ι ℓ) = h' * (x u' * ι ℓ') → u = u')

include hκ hS hcover hdisj in
/-- Mackey's formula on continuous exact virtual groups: restriction along `ι`
of the induction from `H` is the sum over the double-coset representatives `x u`
of the inductions from `S u` of the restrictions along the conjugations `κ u`. -/
theorem continuousRestrict_continuousInduce
    (y : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ H => A.IsContinuous)) :
    continuousRestrict ι (continuousInduce H hH y) =
      ∑ u, continuousInduce (S u) (hSo u) (continuousRestrict (κ u) y) := by
  have h :
      (continuousRestrict.{uG, uG, max uG uV} ι).comp (continuousInduce H hH) =
        ∑ u, (continuousInduce (S u) (hSo u)).comp (continuousRestrict (κ u)) := by
    apply hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      rw [LinearMap.sum_apply]
      change restrict _ _ _ _ (induce H _ _ _ (ofRepresentation _ A)) =
        ∑ u, induce (S u) _ _ _ (restrict _ _ _ _ (ofRepresentation _ A))
      simp only [restrict_ofRepresentation, induce_ofRepresentation]
      exact ofRepresentation_eq_sum_of_equiv_pi _ _
        (mackeyEquiv H ι.toMonoidHom x S (fun u => (κ u).toMonoidHom) hκ hS hcover hdisj A.val)
        (fun ℓ₀ f u => mackeyMap_intertwines H ι.toMonoidHom x S
          (fun u => (κ u).toMonoidHom) hκ A.val ℓ₀ f u)
  have hy := LinearMap.congr_fun h y
  simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using hy

end Langlands.VirtualRepresentation.ExactGrothendieckGroup
