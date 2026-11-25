import Langlands.LocalFactor.Ramification.CloseFieldsStatement
import Langlands.LocalFactor.Ramification.CloseFieldsGaloisQuotientProof
import Langlands.Weil.AlgebraicProof

/-!
# Proof of the close-fields comparison of Weil quotients

For a `p`-adic field `F` with absolute ramification index `e` and `X = k((t))` over the residue
field `k` of `F`, the quotients `W_F/W_F^e` and `W_X/W_X^e` of the local Weil groups are isomorphic
as topological groups, compatibly with the upper filtrations up to `e` and with the degrees. The
Weil groups are pullbacks of the residue degrees along the integers; the isomorphism is obtained
from the Galois one, which preserves residue degrees.
-/

noncomputable section

namespace Langlands.Ramification.Local

universe u

section PullbackQuotient

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  (d : Γ →ₜ* Weil.ProfiniteIntegers) (N : Subgroup Γ) [N.Normal]
  (hN : N ≤ d.toMonoidHom.ker)

/-- A degree `d : Γ → Ẑ` on the quotient `Γ/N`, for `N` in its kernel. -/
def quotientDegree : Γ ⧸ N →ₜ* Weil.ProfiniteIntegers where
  toMonoidHom := QuotientGroup.lift N d.toMonoidHom hN
  continuous_toFun := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr (by exact d.continuous)

omit [IsTopologicalGroup Γ] in
theorem quotientDegree_mk (g : Γ) : quotientDegree d N hN (QuotientGroup.mk g) = d g := rfl

/-- The map `(g, n) ↦ (gN, n)` from the pullback of `d` to the pullback of the degree of `Γ/N`. -/
def pullbackQuotientHom : Weil.Pullback d →ₜ* Weil.Pullback (quotientDegree d N hN) where
  toFun w := ⟨((QuotientGroup.mk (w : Γ × Weil.Degree).1 : Γ ⧸ N), (w : Γ × Weil.Degree).2), w.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    ((QuotientGroup.continuous_mk.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

omit [IsTopologicalGroup Γ] in
theorem pullbackQuotientHom_surjective : Function.Surjective (pullbackQuotientHom d N hN) := by
  rintro ⟨⟨q, n⟩, hq⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨⟨(g, n), hq⟩, rfl⟩

omit [IsTopologicalGroup Γ] in
/-- The kernel of `(g, n) ↦ (gN, n)` is the preimage of `N`: an element of the pullback over `N`
has degree `0`, the Frobenius map of the integers being injective. -/
theorem pullbackQuotientHom_ker :
    N.comap (Weil.projection d).toMonoidHom = (pullbackQuotientHom d N hN).toMonoidHom.ker := by
  ext w
  rw [MonoidHom.mem_ker, Subgroup.mem_comap]
  constructor
  · intro hw
    have h1 : d (w : Γ × Weil.Degree).1 = 1 := hN hw
    have h2 : d (w : Γ × Weil.Degree).1 = Weil.frobenius (w : Γ × Weil.Degree).2 := w.2
    have h3 : (w : Γ × Weil.Degree).2 = 1 :=
      Weil.frobenius_injective (by rw [← h2, h1, map_one])
    apply Subtype.ext
    exact Prod.ext ((QuotientGroup.eq_one_iff _).mpr hw) h3
  · intro hw
    have h := congrArg (fun z : Weil.Pullback (quotientDegree d N hN) =>
      (z : (Γ ⧸ N) × Weil.Degree).1) hw
    exact (QuotientGroup.eq_one_iff _).mp h

/-- `(g, n) ↦ (gN, n)` is open: the image of the trace of an open set `O` of `Γ × ℤ` is the trace
of the image of `O`, since the degree is constant on the cosets of `N`. -/
theorem pullbackQuotientHom_isOpenMap : IsOpenMap (pullbackQuotientHom d N hN) := by
  intro V hV
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hV
  refine isOpen_induced_iff.mpr ⟨Prod.map (QuotientGroup.mk : Γ → Γ ⧸ N) id '' O,
    (QuotientGroup.isOpenMap_coe.prodMap IsOpenMap.id) O hO, ?_⟩
  ext ⟨⟨q, n⟩, hq⟩
  constructor
  · rintro ⟨⟨g, m⟩, hgO, hgm⟩
    have h1 : (QuotientGroup.mk g : Γ ⧸ N) = q := congrArg Prod.fst hgm
    have h2 : m = n := congrArg Prod.snd hgm
    subst h1 h2
    exact ⟨⟨(g, m), hq⟩, hgO, rfl⟩
  · rintro ⟨w, hwO, hw⟩
    exact ⟨(w : Γ × Weil.Degree), hwO, congrArg Subtype.val hw⟩

/-- **Pullback of a quotient.** For `N` a normal subgroup in the kernel of `d`, the quotient of the
pullback of `d` by the preimage of `N` is the pullback of the degree of `Γ/N`, as topological
groups. -/
def pullbackQuotientEquiv : (Weil.Pullback d ⧸ N.comap (Weil.projection d).toMonoidHom) ≃ₜ*
    Weil.Pullback (quotientDegree d N hN) :=
  let e := QuotientGroup.liftEquiv (N.comap (Weil.projection d).toMonoidHom)
    (pullbackQuotientHom_surjective d N hN) (pullbackQuotientHom_ker d N hN)
  have hcont : Continuous e :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (pullbackQuotientHom d N hN).continuous
  have hopen : IsOpenMap e := by
    intro U hU
    rw [← Set.image_preimage_eq U QuotientGroup.mk_surjective, Set.image_image]
    exact pullbackQuotientHom_isOpenMap d N hN _ (hU.preimage QuotientGroup.continuous_mk)
  { toMulEquiv := e
    continuous_toFun := hcont
    continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen).symm.continuous }

theorem pullbackQuotientEquiv_mk (w : Weil.Pullback d) :
    (pullbackQuotientEquiv d N hN (QuotientGroup.mk w) : (Γ ⧸ N) × Weil.Degree) =
      (QuotientGroup.mk (w : Γ × Weil.Degree).1, (w : Γ × Weil.Degree).2) := rfl

end PullbackQuotient

section PullbackCongr

variable {Γ₁ Γ₂ : Type*} [Group Γ₁] [TopologicalSpace Γ₁] [Group Γ₂] [TopologicalSpace Γ₂]
  (d₁ : Γ₁ →ₜ* Weil.ProfiniteIntegers) (d₂ : Γ₂ →ₜ* Weil.ProfiniteIntegers)

theorem pullbackCongr_mem (φ : Γ₁ →* Γ₂) (h : ∀ g, d₂ (φ g) = d₁ g) (w : Weil.Pullback d₁) :
    (φ (w : Γ₁ × Weil.Degree).1, (w : Γ₁ × Weil.Degree).2) ∈ Weil.pullbackSubgroup d₂ := by
  change d₂ (φ (w : Γ₁ × Weil.Degree).1) = Weil.frobenius (w : Γ₁ × Weil.Degree).2
  rw [h]
  exact w.2

/-- A topological isomorphism compatible with the degrees induces a topological isomorphism of the
pullbacks, `(g, n) ↦ (φ g, n)`. -/
def pullbackCongr (φ : Γ₁ ≃ₜ* Γ₂) (h : ∀ g, d₂ (φ g) = d₁ g) :
    Weil.Pullback d₁ ≃ₜ* Weil.Pullback d₂ where
  toFun w := ⟨_, pullbackCongr_mem d₁ d₂ φ.toMulEquiv.toMonoidHom h w⟩
  invFun w := ⟨_, pullbackCongr_mem d₂ d₁ φ.symm.toMulEquiv.toMonoidHom
    (fun g => by
      change d₁ (φ.symm g) = d₂ g
      rw [← h, φ.apply_symm_apply]) w⟩
  left_inv w := Subtype.ext (Prod.ext (φ.symm_apply_apply _) rfl)
  right_inv w := Subtype.ext (Prod.ext (φ.apply_symm_apply _) rfl)
  map_mul' v w := Subtype.ext (Prod.ext (map_mul φ _ _) rfl)
  continuous_toFun :=
    ((φ.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((φ.symm.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

theorem pullbackCongr_apply (φ : Γ₁ ≃ₜ* Γ₂) (h : ∀ g, d₂ (φ g) = d₁ g) (w : Weil.Pullback d₁) :
    (pullbackCongr d₁ d₂ φ h w : Γ₂ × Weil.Degree) =
      (φ (w : Γ₁ × Weil.Degree).1, (w : Γ₁ × Weil.Degree).2) := rfl

end PullbackCongr

section WeilQuotient

variable {Γ₁ Γ₂ : Type*} [Group Γ₁] [TopologicalSpace Γ₁] [IsTopologicalGroup Γ₁]
  [Group Γ₂] [TopologicalSpace Γ₂] [IsTopologicalGroup Γ₂]
  (d₁ : Γ₁ →ₜ* Weil.ProfiniteIntegers) (d₂ : Γ₂ →ₜ* Weil.ProfiniteIntegers)
  (F₁ : ℝ → Subgroup Γ₁) (F₂ : ℝ → Subgroup Γ₂) (x : ℝ) [(F₁ x).Normal] [(F₂ x).Normal]

/-- **Weil quotients from Galois quotients.** Let `d_i : Γ_i → Ẑ` be degrees, `F_i` filtrations
with `F_i x` normal and contained in the kernel of `d_i`, and `φ : Γ₁/F₁ x ≃ Γ₂/F₂ x` a
topological isomorphism carrying the image of `F₁ y` onto that of `F₂ y` for `a₀ ≤ y ≤ x` and
preserving degrees. Then the quotients of the pullbacks `W_i` of the `d_i` by the preimages of
`F_i x` are isomorphic as topological groups, compatibly with the preimages of the `F_i y` and with
the degrees. -/
theorem exists_weilQuotientIso (hN₁ : F₁ x ≤ d₁.toMonoidHom.ker) (hN₂ : F₂ x ≤ d₂.toMonoidHom.ker)
    (φ : (Γ₁ ⧸ F₁ x) ≃ₜ* (Γ₂ ⧸ F₂ x))
    (hdeg : ∀ g₁ g₂, φ (QuotientGroup.mk g₁) = QuotientGroup.mk g₂ → d₁ g₁ = d₂ g₂) {a₀ : ℝ}
    (hanti₁ : ∀ y, y ≤ x → F₁ x ≤ F₁ y) (hanti₂ : ∀ y, y ≤ x → F₂ x ≤ F₂ y)
    (hφ : ∀ y, a₀ ≤ y → y ≤ x →
      ((F₁ y).map (QuotientGroup.mk' (F₁ x))).map φ.toMulEquiv.toMonoidHom =
        (F₂ y).map (QuotientGroup.mk' (F₂ x))) :
    ∃ ψ : (Weil.Pullback d₁ ⧸ (F₁ x).comap (Weil.projection d₁).toMonoidHom) ≃ₜ*
        (Weil.Pullback d₂ ⧸ (F₂ x).comap (Weil.projection d₂).toMonoidHom),
      (∀ y, a₀ ≤ y → y ≤ x →
        (((F₁ y).comap (Weil.projection d₁).toMonoidHom).map
          (QuotientGroup.mk' ((F₁ x).comap (Weil.projection d₁).toMonoidHom))).map
            ψ.toMulEquiv.toMonoidHom =
          ((F₂ y).comap (Weil.projection d₂).toMonoidHom).map
            (QuotientGroup.mk' ((F₂ x).comap (Weil.projection d₂).toMonoidHom))) ∧
      ∀ (w : Weil.Pullback d₁) (w' : Weil.Pullback d₂),
        ψ (QuotientGroup.mk' _ w) = QuotientGroup.mk' _ w' → Weil.degree d₁ w = Weil.degree d₂ w' := by
  let D₁ := quotientDegree d₁ (F₁ x) hN₁
  let D₂ := quotientDegree d₂ (F₂ x) hN₂
  have hD : ∀ q, D₂ (φ q) = D₁ q := by
    intro q
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g₂, hg₂⟩ := QuotientGroup.mk_surjective (φ (QuotientGroup.mk g₁))
    rw [← hg₂]
    exact (hdeg g₁ g₂ hg₂.symm).symm
  let ψ := (pullbackQuotientEquiv d₁ (F₁ x) hN₁).trans
    ((pullbackCongr D₁ D₂ φ hD).trans (pullbackQuotientEquiv d₂ (F₂ x) hN₂).symm)
  have hψ : ∀ (w : Weil.Pullback d₁) (w' : Weil.Pullback d₂),
      ψ (QuotientGroup.mk w) = QuotientGroup.mk w' ↔
        (φ (QuotientGroup.mk (w : Γ₁ × Weil.Degree).1) = QuotientGroup.mk (w' : Γ₂ × Weil.Degree).1 ∧
          (w : Γ₁ × Weil.Degree).2 = (w' : Γ₂ × Weil.Degree).2) := by
    intro w w'
    change (pullbackQuotientEquiv d₂ (F₂ x) hN₂).symm (pullbackCongr D₁ D₂ φ hD
      (pullbackQuotientEquiv d₁ (F₁ x) hN₁ (QuotientGroup.mk w))) = QuotientGroup.mk w' ↔ _
    rw [ContinuousMulEquiv.symm_apply_eq, Subtype.ext_iff, pullbackCongr_apply,
      pullbackQuotientEquiv_mk, pullbackQuotientEquiv_mk, Prod.mk.injEq]
  refine ⟨ψ, fun y hy hyx => ?_, fun w w' h => ((hψ w w').mp h).2⟩
  ext q
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨w', hw'⟩ := QuotientGroup.mk_surjective (ψ (QuotientGroup.mk w))
    have h := ((hψ w w').mp hw'.symm).1
    have hmem : φ (QuotientGroup.mk (w : Γ₁ × Weil.Degree).1) ∈
        (F₂ y).map (QuotientGroup.mk' (F₂ x)) := by
      rw [← hφ y hy hyx]
      exact ⟨_, ⟨_, hw, rfl⟩, rfl⟩
    rw [h] at hmem
    obtain ⟨g, hg, hgw⟩ := hmem
    have hn : g⁻¹ * (w' : Γ₂ × Weil.Degree).1 ∈ F₂ x := QuotientGroup.eq.mp hgw
    have hw'y := (F₂ y).mul_mem hg (hanti₂ y hyx hn)
    rw [mul_inv_cancel_left] at hw'y
    exact ⟨w', hw'y, hw'⟩
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (ψ.symm (QuotientGroup.mk w'))
    have h := ((hψ w w').mp (by rw [hw, ψ.apply_symm_apply])).1
    have hmem : (QuotientGroup.mk (w' : Γ₂ × Weil.Degree).1 : Γ₂ ⧸ F₂ x) ∈
        (F₂ y).map (QuotientGroup.mk' (F₂ x)) := ⟨_, hw', rfl⟩
    rw [← h, ← hφ y hy hyx] at hmem
    obtain ⟨_, ⟨g, hg, rfl⟩, hgq⟩ := hmem
    have hgw : (QuotientGroup.mk g : Γ₁ ⧸ F₁ x) = QuotientGroup.mk (w : Γ₁ × Weil.Degree).1 :=
      φ.injective hgq
    have hn : g⁻¹ * (w : Γ₁ × Weil.Degree).1 ∈ F₁ x := QuotientGroup.eq.mp hgw
    have hwy := (F₁ y).mul_mem hg (hanti₁ y hyx hn)
    rw [mul_inv_cancel_left] at hwy
    refine ⟨QuotientGroup.mk w, ⟨w, hwy, rfl⟩, ?_⟩
    change ψ (QuotientGroup.mk w) = QuotientGroup.mk w'
    rw [hw, ψ.apply_symm_apply]

end WeilQuotient

section Weil

attribute [local instance] LocalField.Laurent.valuativeRel padicWeilUpperGroup_normal
  sepClosedWeilUpperGroup_normal

set_option maxHeartbeats 400000 in
/-- **The close-fields comparison of Weil quotients** (Deligne), from the Galois comparison
with residue degrees. -/
theorem closeFieldsWeilQuotient : CloseFieldsWeilQuotientStatement.{u} := by
  intro p _ F
  obtain ⟨φ, hφ, hdeg, hNK, hNX⟩ := exists_closeFieldsGaloisQuotient F
  obtain ⟨ψ, hψ, hdegψ⟩ := exists_weilQuotientIso (Weil.Local.localResidueDegree F)
    (Weil.Local.SepClosed.localResidueDegree (LaurentSeries (Weil.Local.localResidueField F))
      (SeparableClosure (LaurentSeries (Weil.Local.localResidueField F))))
    (Padic.absoluteUpperRamificationGroup F)
    (localAbsoluteUpperRamificationGroup (LaurentSeries (Weil.Local.localResidueField F))
      (SeparableClosure (LaurentSeries (Weil.Local.localResidueField F))))
    _ hNK hNX φ hdeg (fun y hy => Padic.absoluteUpperRamificationGroup_antitone F hy)
    (fun y hy => localAbsoluteUpperRamificationGroup_antitone _ _ hy) hφ
  exact ⟨ψ, hψ, hdegψ⟩

end Weil

end Langlands.Ramification.Local
