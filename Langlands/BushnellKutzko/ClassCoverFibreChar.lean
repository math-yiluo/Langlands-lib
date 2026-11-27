import Langlands.BushnellKutzko.ClassCoverRefine
import Langlands.BushnellKutzko.UnitFiltrationQuotient
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Covering simple-character classes: characters of a fibre of restriction -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- **BK93 (1.1.5)–(1.1.6) and BK94 p. 120.** Let `ψ_F` be trivial on `𝔭_F` and nontrivial on
`𝔬_F`. A character of a subgroup of `U^{k+1}(𝔄)` that is trivial on its intersection with
`U^{k+2}(𝔄)` is `ψ_e` for some `e ∈ 𝔓^{-(k+1)}`. -/
theorem exists_elementCharacter_of_trivial_succ (ψF : AddChar F ℂ)
    (hψ : IsBKAdditiveCharacter ψF) (L : LatticeChain 𝒪[F] F V) (k : ℕ) (H : Subgroup G)
    (hH : H ≤ L.unitFiltration (k + 1)) (χ : H →* ℂˣ)
    (hχ : ∀ h : H, (h : G) ∈ L.unitFiltration (k + 2) → χ h = 1) :
    ∃ e ∈ L.endFiltration (-((k + 1 : ℕ) : ℤ)),
      ∀ h : H, (χ h : ℂ) = elementCharacter (traceCharacter ψF) e h := by
  let f := L.unitFiltrationToQuotient (i := k + 1) (j := k + 2) (by omega)
  have : Finite ((L.endFiltration ((k + 1 : ℕ) : ℤ)) ⧸
      (L.endFiltration ((k + 2 : ℕ) : ℤ)).comap (L.endFiltration ((k + 1 : ℕ) : ℤ)).subtype) :=
    finite_endFiltrationQuotient L _ _ (by push_cast; omega)
  let H' : Subgroup (L.unitFiltration (k + 1)) := H.subgroupOf (L.unitFiltration (k + 1))
  let χ' : H' →* ℂˣ := χ.comp (Subgroup.subgroupOfEquivOfLe hH).toMonoidHom
  let fH := f.comp H'.subtype
  have hker : fH.ker ≤ χ'.ker := by
    intro x hx
    have hx' := (L.mem_ker_unitFiltrationToQuotient (i := k + 1) (j := k + 2) (by omega)
      (H'.subtype x)).mp hx
    exact hχ _ hx'
  let χbar : fH.range →* ℂˣ := (QuotientGroup.lift fH.ker χ' hker).comp
    (QuotientGroup.quotientKerEquivRange fH).symm.toMonoidHom
  have hne : NeZero (Monoid.exponent (Multiplicative ((L.endFiltration ((k + 1 : ℕ) : ℤ)) ⧸
      (L.endFiltration ((k + 2 : ℕ) : ℤ)).comap
        (L.endFiltration ((k + 1 : ℕ) : ℤ)).subtype))) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨η, hη⟩ := MonoidHom.domRestrict_surjective (M := ℂ) fH.range χbar
  let χfull : L.unitFiltration (k + 1) →* ℂˣ := η.comp f
  obtain ⟨-, -, hdual⟩ := (additiveDuality F V L ψF hψ.1 hψ.2).2 (k + 1) k (by omega)
    (by omega)
  obtain ⟨e, he, hev⟩ := hdual χfull (fun g hg => by
    change η (f g) = 1
    rw [(L.mem_ker_unitFiltrationToQuotient (i := k + 1) (j := k + 2) (by omega) g).mpr hg,
      map_one])
  refine ⟨e, he, fun h => ?_⟩
  let h' : H' := ⟨⟨h, hH h.2⟩, h.2⟩
  have h1 : (χ h : ℂ) = (χbar ⟨fH h', h', rfl⟩ : ℂ) := by
    have hs : (QuotientGroup.quotientKerEquivRange fH).symm ⟨fH h', h', rfl⟩ =
        QuotientGroup.mk h' := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change (χ h : ℂ) = (QuotientGroup.lift fH.ker χ' hker
      ((QuotientGroup.quotientKerEquivRange fH).symm ⟨fH h', h', rfl⟩) : ℂ)
    rw [hs, QuotientGroup.lift_mk]
    rfl
  have h2 : χbar ⟨fH h', h', rfl⟩ = η (fH h') := by
    rw [← hη]
    rfl
  rw [h1, h2]
  exact hev ⟨h, hH h.2⟩

end Langlands.BushnellKutzko
