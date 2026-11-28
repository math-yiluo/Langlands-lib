import Langlands.Correspondence.HenniartCloseFieldsRouteStatement
import Langlands.Correspondence.HenniartGaloisDictionaryProof
import Langlands.Correspondence.HenniartLocalWeilSwanBreak
import Langlands.Correspondence.HenniartWeilSwanBreak
import Langlands.Weil.Representation.FilteredQuotientClassTransport
import Langlands.LocalFactor.Ramification.Herbrand.LocalAbsoluteInertiaProof
import Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof

/-!
# Close-fields orbit counts from the filtered Galois quotients

This file proves `Langlands.Henniart.closeFieldsTwistCountFromGaloisQuotient`: a topological
isomorphism of the absolute Galois groups of a p-adic field `F` and of the Laurent-series
field `X` over its residue field, modulo their absolute upper ramification groups of index the
absolute ramification index `e`, compatible with the upper filtrations up to `e`, gives
`T_F(k + 1, s) = T_X(k + 1, s)` for `s < (k + 1) e` (Henniart 1988, §5.1).

The classes counted are transported through the given quotient isomorphism:

* `galoisRefinedStratumEquivOfQuotient` is a bijection of refined Galois strata for any two
  local fields whose filtered Galois quotients are isomorphic, when each filtration starts with
  absolute inertia, Swan exponents are the rank times the infimum of the triviality parameters,
  and the classes of the stratum are trivial on the group of index `e`.
* The section `PullbackSwan` deduces these Galois-side hypotheses from Weil-side ones; the
  section `Padic` checks the Weil-side ones for `F` (with the p-adic absolute upper filtration)
  and for `X` (with the local absolute upper filtration), and concludes.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Henniart.LocalNumerical

open FiniteRepresentation VirtualRepresentation

universe uG uH u₁ v₁ u₂ v₂ uK uΩ u uW

section CharacterTransfer

variable {G : Type uG} {H : Type uH} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  {N : Subgroup G} {M : Subgroup H} [N.Normal] [M.Normal]

/-- A continuous character trivial on a normal subgroup, as a character of the quotient. -/
def quotientCharacter (χ : G →ₜ* ℂˣ) (h : N ≤ χ.toMonoidHom.ker) : (G ⧸ N) →ₜ* ℂˣ :=
  ⟨QuotientGroup.lift N χ.toMonoidHom h,
    (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr χ.continuous⟩

/-- Transfer of a character trivial on `N` through a topological isomorphism of quotients. -/
def transferCharacter (φ : (G ⧸ N) ≃ₜ* (H ⧸ M)) (χ : G →ₜ* ℂˣ)
    (h : N ≤ χ.toMonoidHom.ker) : H →ₜ* ℂˣ :=
  ((quotientCharacter χ h).comp (φ.symm : (H ⧸ M) →ₜ* (G ⧸ N))).comp
    ⟨QuotientGroup.mk' M, QuotientGroup.continuous_mk⟩

theorem transferCharacter_apply (φ : (G ⧸ N) ≃ₜ* (H ⧸ M)) (χ : G →ₜ* ℂˣ)
    (h : N ≤ χ.toMonoidHom.ker) {g : G} {x : H}
    (hgx : φ (QuotientGroup.mk' N g) = QuotientGroup.mk' M x) :
    transferCharacter φ χ h x = χ g := by
  change quotientCharacter χ h (φ.symm (QuotientGroup.mk' M x)) = χ g
  rw [← hgx, φ.symm_apply_apply]
  rfl

theorem map_quotient_symm_eq (φ : (G ⧸ N) ≃ₜ* (H ⧸ M)) {I : Subgroup G} {J : Subgroup H}
    (hφ : (I.map (QuotientGroup.mk' N)).map φ.toMulEquiv.toMonoidHom =
      J.map (QuotientGroup.mk' M)) :
    (J.map (QuotientGroup.mk' M)).map φ.symm.toMulEquiv.toMonoidHom =
      I.map (QuotientGroup.mk' N) := by
  rw [← hφ, Subgroup.map_map]
  have hcomp : φ.symm.toMulEquiv.toMonoidHom.comp φ.toMulEquiv.toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext φ.symm_apply_apply
  rw [hcomp, Subgroup.map_id]

theorem transferCharacter_eq_one (φ : (G ⧸ N) ≃ₜ* (H ⧸ M)) {I : Subgroup G} {J : Subgroup H}
    (hφ : (I.map (QuotientGroup.mk' N)).map φ.toMulEquiv.toMonoidHom =
      J.map (QuotientGroup.mk' M))
    (χ : G →ₜ* ℂˣ) (h : N ≤ χ.toMonoidHom.ker) (hχ : ∀ g ∈ I, χ g = 1) :
    ∀ x ∈ J, transferCharacter φ χ h x = 1 := by
  intro x hx
  have hmem : QuotientGroup.mk' M x ∈
      (I.map (QuotientGroup.mk' N)).map φ.toMulEquiv.toMonoidHom := by
    rw [hφ]
    exact Subgroup.mem_map_of_mem _ hx
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hq
  rw [transferCharacter_apply φ χ h hqx]
  exact hχ g hg

end CharacterTransfer

section TrivialityParameters

variable {G : Type uG} {H : Type uH} [Group G] [Group H]

theorem mem_trivialityParameters {U : ℝ → Subgroup G}
    {c : IsomorphismClasses.{0, uG, uW} ℂ G} {r : ℝ} :
    r ∈ trivialityParameters U c ↔ 0 ≤ r ∧ c.IsTrivialOn (U r) :=
  Iff.rfl

variable [TopologicalSpace G] [TopologicalSpace H]

/-- Below the cutoff the quotient transport matches the filtrations, and above it both
classes are trivial; so the triviality parameters agree. -/
theorem trivialityParameters_transport {U : ℝ → Subgroup G} {V : ℝ → Subgroup H}
    (hU : Antitone U) (hV : Antitone V) {e : ℝ} [(U e).Normal] [(V e).Normal]
    (φ : (G ⧸ U e) ≃ₜ* (H ⧸ V e))
    (hφ : ∀ r : ℝ, 0 ≤ r → r ≤ e →
      ((U r).map (QuotientGroup.mk' (U e))).map φ.toMulEquiv.toMonoidHom =
        (V r).map (QuotientGroup.mk' (V e)))
    {n : ℕ} (c : ContinuousIrreducibleClasses.TrivialOn.{uG, uW} (U e) n) :
    trivialityParameters V
        (forgetPropertyClass _ (continuousIrreducibleQuotientTransport φ n c).val.val) =
      trivialityParameters U (forgetPropertyClass _ c.val.val) := by
  ext r
  refine and_congr_right fun hr => ?_
  by_cases hre : r ≤ e
  · exact continuousIrreducibleQuotientTransport_isTrivialOn_iff φ c (U r) (V r) (hφ r hr hre)
  · exact iff_of_true
      (IsomorphismClasses.isTrivialOn_of_le _ (hV (le_of_not_ge hre))
        (continuousIrreducibleQuotientTransport φ n c).property)
      (IsomorphismClasses.isTrivialOn_of_le _ (hU (le_of_not_ge hre)) c.property)

end TrivialityParameters

section GaloisTransport

variable {K₁ : Type u₁} [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁]
    [IsNonarchimedeanLocalField K₁]
    {Ω₁ : Type v₁} [Field Ω₁] [Algebra K₁ Ω₁] [IsSepClosure K₁ Ω₁]
    {K₂ : Type u₂} [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂]
    [IsNonarchimedeanLocalField K₂]
    {Ω₂ : Type v₂} [Field Ω₂] [Algebra K₂ Ω₂] [IsSepClosure K₂ Ω₂]


section Characters

variable {N₁ : Subgroup (Ω₁ ≃ₐ[K₁] Ω₁)} {N₂ : Subgroup (Ω₂ ≃ₐ[K₂] Ω₂)} [N₁.Normal] [N₂.Normal]

/-- An unramified Galois character transferred through an isomorphism of quotients
that matches the images of absolute inertia. -/
def unramifiedTransfer (φ : ((Ω₁ ≃ₐ[K₁] Ω₁) ⧸ N₁) ≃ₜ* ((Ω₂ ≃ₐ[K₂] Ω₂) ⧸ N₂))
    (hN₁ : N₁ ≤ (LocalGalois.SepClosed.absoluteInertia K₁ Ω₁))
    (hφ : ((LocalGalois.SepClosed.absoluteInertia K₁ Ω₁).map (QuotientGroup.mk' N₁)).map
        φ.toMulEquiv.toMonoidHom =
      (LocalGalois.SepClosed.absoluteInertia K₂ Ω₂).map (QuotientGroup.mk' N₂))
    (χ : galoisUnramifiedCharacters K₁ Ω₁) : galoisUnramifiedCharacters K₂ Ω₂ :=
  ⟨transferCharacter φ χ.val (fun g hg => MonoidHom.mem_ker.mpr (χ.property ⟨g, hN₁ hg⟩)),
    fun i => transferCharacter_eq_one φ hφ χ.val _ (fun g hg => χ.property ⟨g, hg⟩)
      i.val i.property⟩

/-- The unramified Galois characters of the two fields correspond through an isomorphism
of quotients that matches the images of absolute inertia. -/
def unramifiedEquiv (φ : ((Ω₁ ≃ₐ[K₁] Ω₁) ⧸ N₁) ≃ₜ* ((Ω₂ ≃ₐ[K₂] Ω₂) ⧸ N₂))
    (hN₁ : N₁ ≤ (LocalGalois.SepClosed.absoluteInertia K₁ Ω₁))
    (hN₂ : N₂ ≤ (LocalGalois.SepClosed.absoluteInertia K₂ Ω₂))
    (hφ : ((LocalGalois.SepClosed.absoluteInertia K₁ Ω₁).map (QuotientGroup.mk' N₁)).map
        φ.toMulEquiv.toMonoidHom =
      (LocalGalois.SepClosed.absoluteInertia K₂ Ω₂).map (QuotientGroup.mk' N₂)) :
    galoisUnramifiedCharacters K₁ Ω₁ ≃ galoisUnramifiedCharacters K₂ Ω₂ where
  toFun := unramifiedTransfer φ hN₁ hφ
  invFun := unramifiedTransfer φ.symm hN₂ (map_quotient_symm_eq φ hφ)
  left_inv χ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro g
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N₂ (φ (QuotientGroup.mk' N₁ g))
    have h1 : φ.symm (QuotientGroup.mk' N₂ x) = QuotientGroup.mk' N₁ g := by
      rw [hx, φ.symm_apply_apply]
    exact (transferCharacter_apply φ.symm _ _ h1).trans (transferCharacter_apply φ _ _ hx.symm)
  right_inv χ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N₁ (φ.symm (QuotientGroup.mk' N₂ x))
    have h1 : φ (QuotientGroup.mk' N₁ g) = QuotientGroup.mk' N₂ x := by
      rw [hg, φ.apply_symm_apply]
    exact (transferCharacter_apply φ _ _ h1).trans (transferCharacter_apply φ.symm _ _ hg.symm)

/-- Twisting by an unramified character commutes with the quotient transport, the
character being replaced by its transfer. -/
theorem galoisUnramifiedTwist_transport {k : ℕ}
    (φ : ((Ω₁ ≃ₐ[K₁] Ω₁) ⧸ N₁) ≃ₜ* ((Ω₂ ≃ₐ[K₂] Ω₂) ⧸ N₂))
    (hN₁ : N₁ ≤ (LocalGalois.SepClosed.absoluteInertia K₁ Ω₁))
    (hN₂ : N₂ ≤ (LocalGalois.SepClosed.absoluteInertia K₂ Ω₂))
    (hφ : ((LocalGalois.SepClosed.absoluteInertia K₁ Ω₁).map (QuotientGroup.mk' N₁)).map
        φ.toMulEquiv.toMonoidHom =
      (LocalGalois.SepClosed.absoluteInertia K₂ Ω₂).map (QuotientGroup.mk' N₂))
    (c : ContinuousIrreducibleClasses.TrivialOn.{v₁, uW} N₁ (k + 1))
    (χ : galoisUnramifiedCharacters K₁ Ω₁) :
    ∃ c' : ContinuousIrreducibleClasses.TrivialOn.{v₁, uW} N₁ (k + 1),
      c'.val = galoisUnramifiedTwist K₁ Ω₁ k χ c.val ∧
      (continuousIrreducibleQuotientTransport φ (k + 1) c').val =
        galoisUnramifiedTwist K₂ Ω₂ k (unramifiedEquiv φ hN₁ hN₂ hφ χ)
          (continuousIrreducibleQuotientTransport φ (k + 1) c).val := by
  have hker : N₁ ≤ χ.val.toMonoidHom.ker :=
    fun g hg => MonoidHom.mem_ker.mpr (χ.property ⟨g, hN₁ hg⟩)
  let χq : ((Ω₂ ≃ₐ[K₂] Ω₂) ⧸ N₂) →ₜ* ℂˣ :=
    (quotientCharacter χ.val hker).comp (φ.symm : ((Ω₂ ≃ₐ[K₂] Ω₂) ⧸ N₂) →ₜ* ((Ω₁ ≃ₐ[K₁] Ω₁) ⧸ N₁))
  have hχ : (χq.comp (φ : ((Ω₁ ≃ₐ[K₁] Ω₁) ⧸ N₁) →ₜ* ((Ω₂ ≃ₐ[K₂] Ω₂) ⧸ N₂))).comp
      ⟨QuotientGroup.mk' N₁, QuotientGroup.continuous_mk⟩ = χ.val := by
    apply ContinuousMonoidHom.ext
    intro g
    change quotientCharacter χ.val hker (φ.symm (φ (QuotientGroup.mk' N₁ g))) = χ.val g
    rw [φ.symm_apply_apply]
    rfl
  refine ⟨ContinuousIrreducibleClasses.TrivialOn.twistEquiv
    (χq.comp (φ : ((Ω₁ ≃ₐ[K₁] Ω₁) ⧸ N₁) →ₜ* ((Ω₂ ≃ₐ[K₂] Ω₂) ⧸ N₂))) (k + 1) c, ?_, ?_⟩
  · rw [ContinuousIrreducibleClasses.TrivialOn.twistEquiv_val]
    exact congrArg (fun ψ => continuousIrreducibleTwistEquiv ψ (k + 1) c.val) hχ
  · rw [continuousIrreducibleQuotientTransport_twist,
      ContinuousIrreducibleClasses.TrivialOn.twistEquiv_val]
    rfl

/-- The quotient transport preserves Galois torsion numbers. -/
theorem galoisTorsionNumber_transport {k : ℕ} (φ : ((Ω₁ ≃ₐ[K₁] Ω₁) ⧸ N₁) ≃ₜ* ((Ω₂ ≃ₐ[K₂] Ω₂) ⧸ N₂))
    (hN₁ : N₁ ≤ (LocalGalois.SepClosed.absoluteInertia K₁ Ω₁))
    (hN₂ : N₂ ≤ (LocalGalois.SepClosed.absoluteInertia K₂ Ω₂))
    (hφ : ((LocalGalois.SepClosed.absoluteInertia K₁ Ω₁).map (QuotientGroup.mk' N₁)).map
        φ.toMulEquiv.toMonoidHom =
      (LocalGalois.SepClosed.absoluteInertia K₂ Ω₂).map (QuotientGroup.mk' N₂))
    (c : ContinuousIrreducibleClasses.TrivialOn.{v₁, uW} N₁ (k + 1)) :
    galoisTorsionNumber K₂ Ω₂ (k := k) (continuousIrreducibleQuotientTransport φ (k + 1) c).val =
      galoisTorsionNumber K₁ Ω₁ (k := k) c.val := by
  let E := continuousIrreducibleQuotientTransport.{v₁, v₂, uW} φ (k + 1)
  unfold galoisTorsionNumber
  refine (Nat.card_congr (Equiv.subtypeEquiv (unramifiedEquiv φ hN₁ hN₂ hφ) fun χ => ?_)).symm
  obtain ⟨c', hc', hEc'⟩ := galoisUnramifiedTwist_transport φ hN₁ hN₂ hφ c χ
  rw [← hc', ← hEc']
  constructor
  · intro h
    exact congrArg (fun x => (E x).val) (Subtype.ext h)
  · intro h
    exact congrArg Subtype.val (E.injective (Subtype.ext h))

/-- The quotient transport preserves and reflects unramified-twist equivalence. -/
theorem galoisUnramifiedOrbitClass_transport_iff {k : ℕ}
    (φ : ((Ω₁ ≃ₐ[K₁] Ω₁) ⧸ N₁) ≃ₜ* ((Ω₂ ≃ₐ[K₂] Ω₂) ⧸ N₂))
    (hN₁ : N₁ ≤ (LocalGalois.SepClosed.absoluteInertia K₁ Ω₁))
    (hN₂ : N₂ ≤ (LocalGalois.SepClosed.absoluteInertia K₂ Ω₂))
    (hφ : ((LocalGalois.SepClosed.absoluteInertia K₁ Ω₁).map (QuotientGroup.mk' N₁)).map
        φ.toMulEquiv.toMonoidHom =
      (LocalGalois.SepClosed.absoluteInertia K₂ Ω₂).map (QuotientGroup.mk' N₂))
    (a b : ContinuousIrreducibleClasses.TrivialOn.{v₁, uW} N₁ (k + 1)) :
    galoisUnramifiedOrbitClass K₁ Ω₁ ⟨k.succPNat, a.val⟩ =
        galoisUnramifiedOrbitClass K₁ Ω₁ ⟨k.succPNat, b.val⟩ ↔
      galoisUnramifiedOrbitClass K₂ Ω₂
          ⟨k.succPNat, (continuousIrreducibleQuotientTransport φ (k + 1) a).val⟩ =
        galoisUnramifiedOrbitClass K₂ Ω₂
          ⟨k.succPNat, (continuousIrreducibleQuotientTransport φ (k + 1) b).val⟩ := by
  let E := continuousIrreducibleQuotientTransport.{v₁, v₂, uW} φ (k + 1)
  rw [galoisUnramifiedOrbitClass_eq_iff K₁ Ω₁, galoisUnramifiedOrbitClass_eq_iff K₂ Ω₂]
  refine (unramifiedEquiv φ hN₁ hN₂ hφ).exists_congr fun χ => ?_
  obtain ⟨b', hb', hEb'⟩ := galoisUnramifiedTwist_transport φ hN₁ hN₂ hφ b χ
  change (⟨k.succPNat, galoisUnramifiedTwist K₁ Ω₁ k χ b.val⟩ :
      Weil.IrreducibleBasis.{v₁, uW} (Ω₁ ≃ₐ[K₁] Ω₁)) = ⟨k.succPNat, a.val⟩ ↔
    (⟨k.succPNat, galoisUnramifiedTwist K₂ Ω₂ k (unramifiedEquiv φ hN₁ hN₂ hφ χ) (E b).val⟩ :
      Weil.IrreducibleBasis.{v₂, uW} (Ω₂ ≃ₐ[K₂] Ω₂)) = ⟨k.succPNat, (E a).val⟩
  rw [← hb', ← hEb']
  constructor
  · intro h
    have hval : b'.val = a.val := (Sigma.mk.inj h).2.eq
    exact congrArg
      (fun x => (⟨k.succPNat, (E x).val⟩ : Weil.IrreducibleBasis.{v₂, uW} (Ω₂ ≃ₐ[K₂] Ω₂)))
      (Subtype.ext hval)
  · intro h
    have hval : (E b').val = (E a).val := (Sigma.mk.inj h).2.eq
    exact congrArg
      (fun x => (⟨k.succPNat, x.val⟩ : Weil.IrreducibleBasis.{v₁, uW} (Ω₁ ≃ₐ[K₁] Ω₁)))
      (E.injective (Subtype.ext hval))

end Characters

section Strata

variable {U₁ : ℝ → Subgroup (Ω₁ ≃ₐ[K₁] Ω₁)} {U₂ : ℝ → Subgroup (Ω₂ ≃ₐ[K₂] Ω₂)} {e : ℝ}
  [hNU₁ : (U₁ e).Normal] [hNU₂ : (U₂ e).Normal]

/-- If both filtrations start with absolute inertia, the compatibility at index zero
matches the images of absolute inertia. -/
theorem inertia_map_eq_of_filtration (φ : ((Ω₁ ≃ₐ[K₁] Ω₁) ⧸ U₁ e) ≃ₜ* ((Ω₂ ≃ₐ[K₂] Ω₂) ⧸ U₂ e))
    (he : 0 ≤ e)
    (hφ : ∀ r : ℝ, 0 ≤ r → r ≤ e →
      ((U₁ r).map (QuotientGroup.mk' (U₁ e))).map φ.toMulEquiv.toMonoidHom =
        (U₂ r).map (QuotientGroup.mk' (U₂ e)))
    (hI₁ : U₁ 0 = LocalGalois.SepClosed.absoluteInertia K₁ Ω₁)
    (hI₂ : U₂ 0 = LocalGalois.SepClosed.absoluteInertia K₂ Ω₂) :
    ((LocalGalois.SepClosed.absoluteInertia K₁ Ω₁).map (QuotientGroup.mk' (U₁ e))).map
        φ.toMulEquiv.toMonoidHom =
      (LocalGalois.SepClosed.absoluteInertia K₂ Ω₂).map (QuotientGroup.mk' (U₂ e)) := by
  rw [← hI₁, ← hI₂]
  exact hφ 0 le_rfl he

/-- If on both sides the Swan exponent is the rank times the infimum of the triviality
parameters, the quotient transport preserves Swan exponents. -/
theorem hasGaloisSwan_transport_iff {k s : ℕ}
    (φ : ((Ω₁ ≃ₐ[K₁] Ω₁) ⧸ U₁ e) ≃ₜ* ((Ω₂ ≃ₐ[K₂] Ω₂) ⧸ U₂ e))
    (hU₁ : Antitone U₁) (hU₂ : Antitone U₂)
    (hφ : ∀ r : ℝ, 0 ≤ r → r ≤ e →
      ((U₁ r).map (QuotientGroup.mk' (U₁ e))).map φ.toMulEquiv.toMonoidHom =
        (U₂ r).map (QuotientGroup.mk' (U₂ e)))
    (hS₁ : ∀ ρ : IrreducibleGaloisClass.{u₁, v₁, uW} K₁ Ω₁ k.succPNat,
      HasGaloisSwan K₁ Ω₁ ρ s ↔ (s : ℝ) = ((k + 1 : ℕ) : ℝ) *
        sInf (trivialityParameters U₁ (forgetPropertyClass _ ρ.val)))
    (hS₂ : ∀ ρ : IrreducibleGaloisClass.{u₂, v₂, uW} K₂ Ω₂ k.succPNat,
      HasGaloisSwan K₂ Ω₂ ρ s ↔ (s : ℝ) = ((k + 1 : ℕ) : ℝ) *
        sInf (trivialityParameters U₂ (forgetPropertyClass _ ρ.val)))
    (c : ContinuousIrreducibleClasses.TrivialOn.{v₁, uW} (U₁ e) (k + 1)) :
    HasGaloisSwan K₂ Ω₂ (continuousIrreducibleQuotientTransport φ (k + 1) c).val s ↔
      HasGaloisSwan K₁ Ω₁ c.val s := by
  refine (hS₂ _).trans (Iff.trans ?_ (hS₁ c.val).symm)
  rw [trivialityParameters_transport hU₁ hU₂ φ hφ c]

/-- The refined Galois strata of two local fields correspond when their filtered Galois
quotients are isomorphic, provided each filtration starts with absolute inertia, Swan
exponents are computed from the filtrations, and the classes of the stratum are trivial on
the groups of index `e`. -/
def galoisRefinedStratumEquivOfQuotient {k s : ℕ} (f : ℕ)
    (φ : ((Ω₁ ≃ₐ[K₁] Ω₁) ⧸ U₁ e) ≃ₜ* ((Ω₂ ≃ₐ[K₂] Ω₂) ⧸ U₂ e))
    (he : 0 ≤ e) (hU₁ : Antitone U₁) (hU₂ : Antitone U₂)
    (hI₁ : U₁ 0 = LocalGalois.SepClosed.absoluteInertia K₁ Ω₁)
    (hI₂ : U₂ 0 = LocalGalois.SepClosed.absoluteInertia K₂ Ω₂)
    (hφ : ∀ r : ℝ, 0 ≤ r → r ≤ e →
      ((U₁ r).map (QuotientGroup.mk' (U₁ e))).map φ.toMulEquiv.toMonoidHom =
        (U₂ r).map (QuotientGroup.mk' (U₂ e)))
    (hS₁ : ∀ ρ : IrreducibleGaloisClass.{u₁, v₁, uW} K₁ Ω₁ k.succPNat,
      HasGaloisSwan K₁ Ω₁ ρ s ↔ (s : ℝ) = ((k + 1 : ℕ) : ℝ) *
        sInf (trivialityParameters U₁ (forgetPropertyClass _ ρ.val)))
    (hS₂ : ∀ ρ : IrreducibleGaloisClass.{u₂, v₂, uW} K₂ Ω₂ k.succPNat,
      HasGaloisSwan K₂ Ω₂ ρ s ↔ (s : ℝ) = ((k + 1 : ℕ) : ℝ) *
        sInf (trivialityParameters U₂ (forgetPropertyClass _ ρ.val)))
    (hB₁ : ∀ ρ : IrreducibleGaloisClass.{u₁, v₁, uW} K₁ Ω₁ k.succPNat,
      HasGaloisSwan K₁ Ω₁ ρ s → (forgetPropertyClass _ ρ.val).IsTrivialOn (U₁ e))
    (hB₂ : ∀ ρ : IrreducibleGaloisClass.{u₂, v₂, uW} K₂ Ω₂ k.succPNat,
      HasGaloisSwan K₂ Ω₂ ρ s → (forgetPropertyClass _ ρ.val).IsTrivialOn (U₂ e)) :
    galoisRefinedStratum.{u₁, v₁, uW} K₁ Ω₁ k s f ≃
      galoisRefinedStratum.{u₂, v₂, uW} K₂ Ω₂ k s f := by
  have hN₁ : U₁ e ≤ LocalGalois.SepClosed.absoluteInertia K₁ Ω₁ := (hU₁ he).trans hI₁.le
  have hN₂ : U₂ e ≤ LocalGalois.SepClosed.absoluteInertia K₂ Ω₂ := (hU₂ he).trans hI₂.le
  have hφI := inertia_map_eq_of_filtration φ he hφ hI₁ hI₂
  let E := continuousIrreducibleQuotientTransport.{v₁, v₂, uW} φ (k + 1)
  let A := {c : ContinuousIrreducibleClasses.TrivialOn.{v₁, uW} (U₁ e) (k + 1) //
    HasGaloisSwan K₁ Ω₁ c.val s ∧ galoisTorsionNumber K₁ Ω₁ (k := k) c.val = f}
  let to₁ (c : A) : galoisRefinedStratum.{u₁, v₁, uW} K₁ Ω₁ k s f :=
    ⟨galoisUnramifiedOrbitClass K₁ Ω₁ ⟨k.succPNat, c.val.val⟩, ⟨c.val.val, rfl, c.property⟩⟩
  let to₂ (c : A) : galoisRefinedStratum.{u₂, v₂, uW} K₂ Ω₂ k s f :=
    ⟨galoisUnramifiedOrbitClass K₂ Ω₂ ⟨k.succPNat, (E c.val).val⟩,
      ⟨(E c.val).val, rfl, (hasGaloisSwan_transport_iff φ hU₁ hU₂ hφ hS₁ hS₂ c.val).mpr
        c.property.1, (galoisTorsionNumber_transport φ hN₁ hN₂ hφI c.val).trans c.property.2⟩⟩
  refine equivOfSameFibers to₁ to₂ ?_ ?_ ?_
  · rintro ⟨x, ρ, hρx, hρs, hρf⟩
    exact ⟨⟨⟨ρ, hB₁ ρ hρs⟩, hρs, hρf⟩, Subtype.ext hρx⟩
  · rintro ⟨x, ρ, hρx, hρs, hρf⟩
    let b : ContinuousIrreducibleClasses.TrivialOn.{v₂, uW} (U₂ e) (k + 1) := ⟨ρ, hB₂ ρ hρs⟩
    let a := E.symm b
    have hab : E a = b := E.apply_symm_apply b
    have hsa : HasGaloisSwan K₁ Ω₁ a.val s := by
      apply (hasGaloisSwan_transport_iff φ hU₁ hU₂ hφ hS₁ hS₂ a).mp
      change HasGaloisSwan K₂ Ω₂ (E a).val s
      rw [hab]
      exact hρs
    have hfa : galoisTorsionNumber K₁ Ω₁ (k := k) a.val = f := by
      rw [← galoisTorsionNumber_transport φ hN₁ hN₂ hφI a]
      change galoisTorsionNumber K₂ Ω₂ (k := k) (E a).val = f
      rw [hab]
      exact hρf
    refine ⟨⟨a, hsa, hfa⟩, Subtype.ext ?_⟩
    change galoisUnramifiedOrbitClass K₂ Ω₂ ⟨k.succPNat, (E a).val⟩ = x
    rw [hab]
    exact hρx
  · intro a b
    have heq := galoisUnramifiedOrbitClass_transport_iff φ hN₁ hN₂ hφI a.val b.val
    constructor
    · intro h
      exact Subtype.ext (heq.mp (congrArg Subtype.val h))
    · intro h
      exact Subtype.ext (heq.mpr (congrArg Subtype.val h))

end Strata

end GaloisTransport

section PullbackSwan

variable {K : Type uK} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {Ω : Type uΩ} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]

/-- Absolute inertia lies in the image of the Weil group. -/
theorem absoluteInertia_le_range_localProjection :
    LocalGalois.SepClosed.absoluteInertia K Ω ≤
      (Weil.Local.SepClosed.localProjection K Ω).toMonoidHom.range :=
  fun g hg => ⟨Weil.Local.SepClosed.localInertiaInclusion K Ω ⟨g, hg⟩, rfl⟩

/-- For a filtration inside absolute inertia, the triviality parameters of a Galois class
are those of its Weil pullback for the preimage filtration. -/
theorem trivialityParameters_restrictClass (U : ℝ → Subgroup (Ω ≃ₐ[K] Ω))
    (hU : ∀ r : ℝ, 0 ≤ r → U r ≤ LocalGalois.SepClosed.absoluteInertia K Ω)
    (c : IsomorphismClasses.{0, uΩ, uW} ℂ (Ω ≃ₐ[K] Ω)) :
    trivialityParameters
        (fun r => (U r).comap (Weil.Local.SepClosed.localProjection K Ω).toMonoidHom)
        (restrictClass (Weil.Local.SepClosed.localProjection K Ω).toMonoidHom c) =
      trivialityParameters U c := by
  ext r
  rw [mem_trivialityParameters, mem_trivialityParameters]
  refine and_congr_right fun hr => ?_
  rw [restrictClass_isTrivialOn_iff, Subgroup.map_comap_eq_self
    ((hU r hr).trans absoluteInertia_le_range_localProjection)]

/-- If Weil Swan exponents are computed from the preimage of a filtration inside absolute
inertia, Galois Swan exponents are computed from the filtration itself. -/
theorem hasGaloisSwan_iff_of_hasWeilSwan_iff {k s : ℕ} (U : ℝ → Subgroup (Ω ≃ₐ[K] Ω))
    (hU : ∀ r : ℝ, 0 ≤ r → U r ≤ LocalGalois.SepClosed.absoluteInertia K Ω)
    (hW : ∀ σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat,
      HasWeilSwan K Ω σ s ↔ (s : ℝ) = ((k + 1 : ℕ) : ℝ) * sInf (trivialityParameters
        (fun r => (U r).comap (Weil.Local.SepClosed.localProjection K Ω).toMonoidHom)
        (weilClassForget K Ω σ)))
    (ρ : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat) :
    HasGaloisSwan K Ω ρ s ↔ (s : ℝ) = ((k + 1 : ℕ) : ℝ) *
      sInf (trivialityParameters U (forgetPropertyClass _ ρ.val)) := by
  obtain ⟨σ, hσ, huniq⟩ := (galoisPullbackBijection.{uK, uΩ, uW} K Ω k).1 ρ
  have hforget : weilClassForget K Ω σ =
      restrictClass (Weil.Local.SepClosed.localProjection K Ω).toMonoidHom
        (forgetPropertyClass _ ρ.val) := hσ
  rw [← trivialityParameters_restrictClass U hU, ← hforget]
  constructor
  · rintro ⟨σ', hσ', hs⟩
    rw [huniq σ' hσ'] at hs
    exact (hW σ).mp hs
  · intro h
    exact ⟨σ, hσ, (hW σ).mpr h⟩

/-- If the Weil pullbacks of the given Swan exponent are trivial on the preimage of a
member of a filtration inside absolute inertia, so are the Galois classes on the member. -/
theorem isTrivialOn_of_hasGaloisSwan {k s : ℕ} (U : ℝ → Subgroup (Ω ≃ₐ[K] Ω))
    (hU : ∀ r : ℝ, 0 ≤ r → U r ≤ LocalGalois.SepClosed.absoluteInertia K Ω)
    {e : ℝ} (he : 0 ≤ e)
    (hB : ∀ σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat, HasWeilSwan K Ω σ s →
      (weilClassForget K Ω σ).IsTrivialOn
        ((U e).comap (Weil.Local.SepClosed.localProjection K Ω).toMonoidHom))
    (ρ : IrreducibleGaloisClass.{uK, uΩ, uW} K Ω k.succPNat) (hρ : HasGaloisSwan K Ω ρ s) :
    (forgetPropertyClass _ ρ.val).IsTrivialOn (U e) := by
  obtain ⟨σ, hσ, hs⟩ := hρ
  have h := hB σ hs
  have hforget : weilClassForget K Ω σ =
      restrictClass (Weil.Local.SepClosed.localProjection K Ω).toMonoidHom
        (forgetPropertyClass _ ρ.val) := hσ
  rw [hforget, restrictClass_isTrivialOn_iff, Subgroup.map_comap_eq_self
    ((hU e he).trans absoluteInertia_le_range_localProjection)] at h
  exact h

/-- The class last break is the infimum of the triviality parameters of the preimage of
the absolute upper filtration. -/
theorem classLastBreak_eq_sInf_trivialityParameters
    (c : IsomorphismClasses.{0, uΩ, uW} ℂ (Weil.Local.SepClosed.localWeilGroup K Ω)) :
    VirtualRepresentation.LocalWeil.SepClosed.Ramification.classLastBreak K Ω c =
      sInf (trivialityParameters
        (fun r => (Ramification.Local.localAbsoluteUpperRamificationGroup K Ω r).comap
          (Weil.Local.SepClosed.localProjection K Ω).toMonoidHom) c) :=
  Quotient.inductionOn c fun _ => rfl

/-- The Swan exponent of an irreducible Weil class is the rank times the infimum of its
triviality parameters for the preimage of the absolute upper filtration. -/
theorem hasWeilSwan_iff_trivialityParameters {k s : ℕ}
    (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat) :
    HasWeilSwan K Ω σ s ↔ (s : ℝ) = ((k + 1 : ℕ) : ℝ) * sInf (trivialityParameters
      (fun r => (Ramification.Local.localAbsoluteUpperRamificationGroup K Ω r).comap
        (Weil.Local.SepClosed.localProjection K Ω).toMonoidHom) (weilClassForget K Ω σ)) := by
  rw [hasWeilSwan_iff_eq_weilSwanConductor, weilSwanConductor,
    classLastBreak_eq_sInf_trivialityParameters]
  rfl

/-- Below rank times a positive cutoff, an irreducible Weil class of that Swan exponent is
trivial on the preimage of the absolute upper group at the cutoff. -/
theorem isTrivialOn_of_hasWeilSwan {k s : ℕ} {e : ℝ} (he : 0 < e)
    (hs : (s : ℝ) < ((k + 1 : ℕ) : ℝ) * e)
    (σ : IrreducibleWeilClass.{uK, uΩ, uW} K Ω k.succPNat) (hσ : HasWeilSwan K Ω σ s) :
    (weilClassForget K Ω σ).IsTrivialOn
      ((Ramification.Local.localAbsoluteUpperRamificationGroup K Ω e).comap
        (Weil.Local.SepClosed.localProjection K Ω).toMonoidHom) := by
  obtain ⟨A, hA⟩ := Quotient.exists_rep (weilClassForget K Ω σ)
  change classOf A = weilClassForget K Ω σ at hA
  have htriv := (isTrivialAt_iff_of_hasWeilSwan K Ω hA hσ he).mpr hs
  rw [← hA, classOf_isTrivialOn]
  exact htriv

end PullbackSwan

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

private local instance padicValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
private local instance padicTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
private local instance padicLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
private local instance padicCharZero : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

/-- On a p-adic field, the Swan exponent of an irreducible Weil class is the rank times the
infimum of its triviality parameters for the preimage of the p-adic absolute upper
filtration. -/
theorem padic_hasWeilSwan_iff_trivialityParameters {k s : ℕ}
    (σ : IrreducibleWeilClass.{u, u, uW} F.Carrier (AlgebraicClosure F.Carrier) k.succPNat) :
    HasWeilSwan F.Carrier (AlgebraicClosure F.Carrier) σ s ↔ (s : ℝ) = ((k + 1 : ℕ) : ℝ) *
      sInf (trivialityParameters
        (fun r => (Ramification.Padic.absoluteUpperRamificationGroup F r).comap
          (Weil.Local.SepClosed.localProjection F.Carrier
            (AlgebraicClosure F.Carrier)).toMonoidHom)
        (weilClassForget F.Carrier (AlgebraicClosure F.Carrier) σ)) := by
  obtain ⟨A, hA⟩ :=
    Quotient.exists_rep (weilClassForget F.Carrier (AlgebraicClosure F.Carrier) σ)
  change classOf A = weilClassForget F.Carrier (AlgebraicClosure F.Carrier) σ at hA
  have h := Numerical.hasWeilSwan_iff_eq_rank_mul_lastBreak (s := s) F (σ := σ) hA
  rw [← hA]
  exact h

/-- On a p-adic field with absolute ramification index `e`, an irreducible Weil class of
rank `k + 1` and Swan exponent `s < (k + 1) e` is trivial on the preimage of the p-adic
absolute upper group of index `e`. -/
theorem padic_isTrivialOn_of_hasWeilSwan {k s : ℕ}
    (hs : s < (k + 1) * F.canonicalTopologicalData.ramificationIndex)
    (σ : IrreducibleWeilClass.{u, u, uW} F.Carrier (AlgebraicClosure F.Carrier) k.succPNat)
    (hσ : HasWeilSwan F.Carrier (AlgebraicClosure F.Carrier) σ s) :
    (weilClassForget F.Carrier (AlgebraicClosure F.Carrier) σ).IsTrivialOn
      ((Ramification.Padic.absoluteUpperRamificationGroup F
          (F.canonicalTopologicalData.ramificationIndex : ℝ)).comap
        (Weil.Local.SepClosed.localProjection F.Carrier
          (AlgebraicClosure F.Carrier)).toMonoidHom) := by
  obtain ⟨A, hA⟩ :=
    Quotient.exists_rep (weilClassForget F.Carrier (AlgebraicClosure F.Carrier) σ)
  change classOf A = weilClassForget F.Carrier (AlgebraicClosure F.Carrier) σ at hA
  have hs' : (s : ℝ) < ((k + 1 : ℕ) : ℝ) *
      (F.canonicalTopologicalData.ramificationIndex : ℝ) := by
    exact_mod_cast hs
  have hb : (0 : ℝ) < F.canonicalTopologicalData.ramificationIndex := by
    exact_mod_cast F.canonicalTopologicalData.ramificationIndex_pos
  have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  have heq := (Numerical.hasWeilSwan_iff_eq_rank_mul_lastBreak F (σ := σ) hA).mp hσ
  have hlt := (mul_lt_mul_iff_of_pos_left hpos).mp (heq ▸ hs')
  have hAcont := (Numerical.weilRepresentative_continuous_irreducible F (σ := σ) hA).1
  have htriv := (Ramification.HerbrandBridge.lastBreak_lt_iff_isTrivialAt F A hAcont hb).mp hlt
  rw [← hA, classOf_isTrivialOn]
  exact htriv

attribute [local instance] LocalField.Laurent.valuativeRel

local notation "X" => LaurentSeries (Weil.Local.localResidueField F)
local notation "ΩX" => SeparableClosure (LaurentSeries (Weil.Local.localResidueField F))
local notation "e" => (F.canonicalTopologicalData.ramificationIndex : ℝ)

/-- A filtered isomorphism of the absolute Galois quotients at the absolute ramification
index `e` of a p-adic field and of the Laurent-series field over its residue field gives
equal torsion-number-one Weil orbit counts `T(k + 1, s)` for `s < (k + 1) e`. -/
theorem weilTwistIrreducibleCount_eq_of_galoisQuotient (k s : ℕ)
    (hs : s < (k + 1) * F.canonicalTopologicalData.ramificationIndex)
    (φ : (Field.absoluteGaloisGroup F.Carrier ⧸
        Ramification.Padic.absoluteUpperRamificationGroup F e) ≃ₜ*
      ((ΩX ≃ₐ[X] ΩX) ⧸ Ramification.Local.localAbsoluteUpperRamificationGroup X ΩX e))
    (hφ : ∀ v : ℝ, 0 ≤ v → v ≤ e →
      Subgroup.map φ.toMulEquiv.toMonoidHom
          (Subgroup.map (QuotientGroup.mk' (Ramification.Padic.absoluteUpperRamificationGroup F e))
            (Ramification.Padic.absoluteUpperRamificationGroup F v)) =
        Subgroup.map
          (QuotientGroup.mk' (Ramification.Local.localAbsoluteUpperRamificationGroup X ΩX e))
          (Ramification.Local.localAbsoluteUpperRamificationGroup X ΩX v)) :
    Numerical.weilTwistIrreducibleCount.{u, uW} F k s =
      weilTwistIrreducibleCount.{u, u, uW} X ΩX k s := by
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < e := by
    exact_mod_cast F.canonicalTopologicalData.ramificationIndex_pos
  have hs' : (s : ℝ) < ((k + 1 : ℕ) : ℝ) * e := by exact_mod_cast hs
  have hUK : Antitone (Ramification.Padic.absoluteUpperRamificationGroup F) :=
    Ramification.Padic.absoluteUpperRamificationGroup_antitone F
  have hUX : Antitone (Ramification.Local.localAbsoluteUpperRamificationGroup X ΩX) :=
    Ramification.Local.localAbsoluteUpperRamificationGroup_antitone X ΩX
  have hIK : Ramification.Padic.absoluteUpperRamificationGroup F 0 =
      LocalGalois.SepClosed.absoluteInertia F.Carrier (AlgebraicClosure F.Carrier) :=
    Ramification.HerbrandBridge.absoluteUpperCanonicalInertia F
  have hIX : Ramification.Local.localAbsoluteUpperRamificationGroup X ΩX 0 =
      LocalGalois.SepClosed.absoluteInertia X ΩX :=
    Ramification.Local.absoluteUpperInertia X ΩX
  have hUK' : ∀ r : ℝ, 0 ≤ r → Ramification.Padic.absoluteUpperRamificationGroup F r ≤
      LocalGalois.SepClosed.absoluteInertia F.Carrier (AlgebraicClosure F.Carrier) :=
    fun r hr => (hUK hr).trans hIK.le
  have hUX' : ∀ r : ℝ, 0 ≤ r → Ramification.Local.localAbsoluteUpperRamificationGroup X ΩX r ≤
      LocalGalois.SepClosed.absoluteInertia X ΩX :=
    fun r hr => (hUX hr).trans hIX.le
  let E := galoisRefinedStratumEquivOfQuotient.{u, u, u, u, uW}
    (K₁ := F.Carrier) (Ω₁ := AlgebraicClosure F.Carrier) (K₂ := X) (Ω₂ := ΩX)
    (k := k) (s := s) (hNU₁ := Ramification.Padic.absoluteUpperRamificationGroup_normal F e)
    1 φ he hUK hUX hIK hIX hφ
    (hasGaloisSwan_iff_of_hasWeilSwan_iff _ hUK'
      (padic_hasWeilSwan_iff_trivialityParameters F))
    (hasGaloisSwan_iff_of_hasWeilSwan_iff _ hUX' hasWeilSwan_iff_trivialityParameters)
    (isTrivialOn_of_hasGaloisSwan _ hUK' he (padic_isTrivialOn_of_hasWeilSwan F hs))
    (isTrivialOn_of_hasGaloisSwan _ hUX' he (isTrivialOn_of_hasWeilSwan hpos hs'))
  change (weilRefinedStratum.{u, u, uW} F.Carrier (AlgebraicClosure F.Carrier) k s 1).encard =
    (weilRefinedStratum.{u, u, uW} X ΩX k s 1).encard
  rw [← (weilGaloisOrbitEquiv F.Carrier (AlgebraicClosure F.Carrier)).injective.encard_image,
    weilGaloisOrbitEquiv_image_weilRefinedStratum,
    ← (weilGaloisOrbitEquiv X ΩX).injective.encard_image,
    weilGaloisOrbitEquiv_image_weilRefinedStratum]
  exact Set.encard_congr E

end Padic

end Langlands.Henniart.LocalNumerical

namespace Langlands.Henniart

universe u uW

/-- The filtered absolute Galois quotient comparison of close fields implies the equality
of torsion-number-one Weil orbit counts below the absolute ramification index. -/
theorem closeFieldsTwistCountFromGaloisQuotient :
    CloseFieldsTwistCountFromGaloisQuotientStatement.{u, uW} := by
  intro hQ p _ F k s hs
  obtain ⟨φ, hφ⟩ := hQ p F
  exact LocalNumerical.weilTwistIrreducibleCount_eq_of_galoisQuotient F k s hs φ hφ

end Langlands.Henniart
