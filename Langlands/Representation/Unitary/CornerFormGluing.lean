import Langlands.Representation.Hecke.CornerDetermination
import Langlands.Representation.Hecke.UnimodularStar
import Langlands.Representation.Unitary.Basic

/-!
# Gluing corner-invariant forms on fixed vectors into an invariant inner product

Let `ρ` be a smooth complex representation of a topological group with a two-sided,
inversion-invariant Haar measure, and let `K₀` be a compact open subgroup. Suppose that for
every compact open `K ≤ K₀` the fixed space `ρ^K` carries a positive definite Hermitian
form for which the corner involution `f ↦ f*`, `f*(x) = conj (f x⁻¹)`, is the adjoint of
the corner action, and that these forms restrict compatibly. Then `ρ` is unitarizable.
This is steps 4 and 5 of the outline in
`Langlands/Representation/Unitary/CharacterLimitSubquotientsStatement.md`, after the
normalization step.
-/

noncomputable section

namespace Langlands

open MeasureTheory MeasureTheory.Measure
open HarmonicAnalysis (SchwartzBruhat)
open scoped ComplexConjugate

universe uG uV

namespace Hecke

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- Right translation of the test function moves the inverse group action onto the input
vector, for a right-invariant Haar measure. -/
theorem integratedAction_rightTranslate_of_isMulRightInvariant [IsMulRightInvariant μ]
    (g : G) (f : SchwartzBruhat G) (v : V) :
    integratedAction μ ρ hρ (TestFunction.rightTranslate g f) v =
      integratedAction μ ρ hρ f (ρ g⁻¹ v) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro L
  rw [map_sub, sub_eq_zero, integratedAction_dual, integratedAction_dual]
  change (∫ x, f (x * g) * L (ρ x v) ∂μ) = _
  rw [← integral_mul_right_eq_self (fun x => f (x * g) * L (ρ x v)) g⁻¹]
  simp only [inv_mul_cancel_right, map_mul, Module.End.mul_apply]

variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The involution of a left translate of the normalized indicator is the corresponding
right translate. -/
theorem star_leftTranslate_normalizedIndicator (g : G) :
    star ((HeckeAlgebra.toTestFunction μ).symm (TestFunction.leftTranslate g
      (HeckeAlgebra.toTestFunction μ (HeckeAlgebra.normalizedIndicator μ K hK)))) =
    (HeckeAlgebra.toTestFunction μ).symm (TestFunction.rightTranslate g
      (HeckeAlgebra.toTestFunction μ (HeckeAlgebra.normalizedIndicator μ K hK))) := by
  ext x
  rw [HeckeAlgebra.star_apply]
  change conj (HeckeAlgebra.normalizedIndicator μ K hK (g⁻¹ * x⁻¹)) =
    HeckeAlgebra.normalizedIndicator μ K hK (x * g)
  have h := congrArg (fun f : HeckeAlgebra μ => f (x * g))
    (HeckeAlgebra.star_normalizedIndicator μ K hK)
  simp only [HeckeAlgebra.star_apply, mul_inv_rev] at h
  exact h

variable [IsMulRightInvariant μ] [IsInvInvariant μ]

/-- The corner involution commutes with the corner projection `f ↦ e_K f e_K`. -/
theorem Corner.star_project (h : HeckeAlgebra μ) :
    star (HeckeAlgebra.Corner.project μ K hK h) =
      HeckeAlgebra.Corner.project μ K hK (star h) := by
  apply HeckeAlgebra.Corner.toHeckeAlgebra_injective
  rw [HeckeAlgebra.Corner.toHeckeAlgebra_star, HeckeAlgebra.Corner.toHeckeAlgebra_project,
    HeckeAlgebra.Corner.toHeckeAlgebra_project]
  simp only [star_mul, HeckeAlgebra.star_normalizedIndicator, mul_assoc]

/-- The involution of the translate element `translateCornerElement μ K hK g` acts on
`K`-fixed vectors as `ρ g⁻¹` followed by the projection to `K`-fixed vectors. -/
theorem cornerAction_star_translateCornerElement (u : fixedVectors ρ K.toSubgroup) (g : G) :
    cornerAction μ ρ hρ K hK (star (translateCornerElement μ K hK g)) u =
      fixedProjection μ ρ hρ K hK (ρ g⁻¹ u) := by
  rw [translateCornerElement, Corner.star_project, star_leftTranslate_normalizedIndicator,
    cornerAction_project]
  apply Subtype.ext
  have h : heckeAction μ ρ hρ ((HeckeAlgebra.toTestFunction μ).symm
      (TestFunction.rightTranslate g (HeckeAlgebra.toTestFunction μ
        (HeckeAlgebra.normalizedIndicator μ K hK)))) (u : V) =
      heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) (ρ g⁻¹ u) := by
    rw [heckeAction_apply, LinearEquiv.apply_symm_apply,
      integratedAction_rightTranslate_of_isMulRightInvariant]
    rfl
  rw [fixedProjection_apply, fixedProjection_apply, h,
    heckeAction_normalizedIndicator_idempotent]

end Hecke

namespace CornerFormGluing

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V)

/-- The open subgroup `g K g⁻¹`, consisting of the `x` with `g⁻¹ x g ∈ K`. -/
def conjOpenSubgroup (g : G) (K : OpenSubgroup G) : OpenSubgroup G :=
  K.comap (MulAut.conj g⁻¹).toMonoidHom (by
    change Continuous fun x => g⁻¹ * x * g⁻¹⁻¹
    fun_prop)

theorem mem_conjOpenSubgroup {g : G} {K : OpenSubgroup G} {x : G} :
    x ∈ conjOpenSubgroup g K ↔ g⁻¹ * x * g ∈ K := by
  simp [conjOpenSubgroup, OpenSubgroup.mem_comap]

omit [IsTopologicalGroup G] in
/-- Fixed vectors of a subgroup are fixed by every smaller subgroup. -/
theorem mem_fixedVectors_of_le {K L : OpenSubgroup G} (hLK : L ≤ K) {v : V}
    (hv : v ∈ fixedVectors ρ K.toSubgroup) : v ∈ fixedVectors ρ L.toSubgroup :=
  fun l => hv ⟨l, hLK l.property⟩

/-- A translate `ρ g v` of a `K`-fixed vector is fixed by `g K g⁻¹`. -/
theorem mem_fixedVectors_conj {K : OpenSubgroup G} {v : V}
    (hv : v ∈ fixedVectors ρ K.toSubgroup) (g : G) :
    ρ g v ∈ fixedVectors ρ (conjOpenSubgroup g K).toSubgroup := by
  intro x
  have hx : g⁻¹ * (x : G) * g ∈ K := mem_conjOpenSubgroup.mp x.property
  have h := hv ⟨_, hx⟩
  change ρ (g⁻¹ * (x : G) * g) v = v at h
  change ρ (x : G) (ρ g v) = ρ g v
  calc ρ (x : G) (ρ g v) = ρ g (ρ (g⁻¹ * (x : G) * g) v) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
    _ = ρ g v := by rw [h]

/-- An open subgroup of a compact open subgroup is compact. -/
theorem isCompact_of_le {K₀ K : OpenSubgroup G} (hK₀ : IsCompact (K₀ : Set G))
    (hKK₀ : K ≤ K₀) : IsCompact (K : Set G) :=
  hK₀.of_isClosed_subset K.isClosed hKK₀

variable (hρ : IsSmooth ρ) {K₀ : OpenSubgroup G} (hK₀ : IsCompact (K₀ : Set G))
variable (b : ∀ K : OpenSubgroup G, IsCompact (K : Set G) → K ≤ K₀ →
  InnerProductSpace.Core ℂ (fixedVectors ρ K.toSubgroup))

/-- An open subgroup fixing `v`, chosen once and for all by smoothness. -/
def stabilizer (v : V) : OpenSubgroup G := Classical.choose (hρ v)

omit [IsTopologicalGroup G] in
theorem mem_fixedVectors_stabilizer (v : V) :
    v ∈ fixedVectors ρ (stabilizer ρ hρ v).toSubgroup :=
  Classical.choose_spec (hρ v)

/-- The level of a pair: the compact open subgroup `K₀ ∩ stab v ∩ stab w`. -/
def pairLevel (K₀ : OpenSubgroup G) (v w : V) : OpenSubgroup G :=
  K₀ ⊓ stabilizer ρ hρ v ⊓ stabilizer ρ hρ w

omit [IsTopologicalGroup G] in
theorem pairLevel_le (v w : V) : pairLevel ρ hρ K₀ v w ≤ K₀ :=
  inf_le_left.trans inf_le_left

omit [IsTopologicalGroup G] in
theorem left_mem_pairLevel (v w : V) :
    v ∈ fixedVectors ρ (pairLevel ρ hρ K₀ v w).toSubgroup :=
  mem_fixedVectors_of_le ρ (inf_le_left.trans inf_le_right)
    (mem_fixedVectors_stabilizer ρ hρ v)

omit [IsTopologicalGroup G] in
theorem right_mem_pairLevel (v w : V) :
    w ∈ fixedVectors ρ (pairLevel ρ hρ K₀ v w).toSubgroup :=
  mem_fixedVectors_of_le ρ inf_le_right (mem_fixedVectors_stabilizer ρ hρ w)

/-- The glued form: evaluate the form of the level of the pair. -/
def gluedInner (v w : V) : ℂ :=
  (b (pairLevel ρ hρ K₀ v w) (isCompact_of_le hK₀ (pairLevel_le ρ hρ v w))
    (pairLevel_le ρ hρ v w)).inner
    ⟨v, left_mem_pairLevel ρ hρ v w⟩ ⟨w, right_mem_pairLevel ρ hρ v w⟩

variable {ρ b}

/-- Compatibility of the family identifies the glued form with the form at any admissible
level fixing both vectors. -/
theorem gluedInner_eq
    (hcompat : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hKK₀ : K ≤ K₀)
      (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) (hLK₀ : L ≤ K₀) (hLK : L ≤ K)
      (v w : fixedVectors ρ K.toSubgroup),
      (b L hL hLK₀).inner ⟨v, mem_fixedVectors_of_le ρ hLK v.property⟩
        ⟨w, mem_fixedVectors_of_le ρ hLK w.property⟩ = (b K hK hKK₀).inner v w)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hKK₀ : K ≤ K₀)
    (v w : fixedVectors ρ K.toSubgroup) :
    gluedInner ρ hρ hK₀ b v w = (b K hK hKK₀).inner v w := by
  set P := pairLevel ρ hρ K₀ (v : V) (w : V)
  have hPK₀ : P ≤ K₀ := pairLevel_le ρ hρ _ _
  have hJK : K ⊓ P ≤ K := inf_le_left
  have hJP : K ⊓ P ≤ P := inf_le_right
  have hJK₀ : K ⊓ P ≤ K₀ := hJK.trans hKK₀
  have hJ : IsCompact ((K ⊓ P : OpenSubgroup G) : Set G) := isCompact_of_le hK₀ hJK₀
  have h1 := hcompat K hK hKK₀ (K ⊓ P) hJ hJK₀ hJK v w
  have h2 := hcompat P (isCompact_of_le hK₀ hPK₀) hPK₀ (K ⊓ P) hJ hJK₀ hJP
    ⟨v, left_mem_pairLevel ρ hρ _ _⟩ ⟨w, right_mem_pairLevel ρ hρ _ _⟩
  exact h2.symm.trans h1

/-- `gluedInner_eq` for vectors given together with their membership proofs. -/
theorem gluedInner_eq_of_mem
    (hcompat : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hKK₀ : K ≤ K₀)
      (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) (hLK₀ : L ≤ K₀) (hLK : L ≤ K)
      (v w : fixedVectors ρ K.toSubgroup),
      (b L hL hLK₀).inner ⟨v, mem_fixedVectors_of_le ρ hLK v.property⟩
        ⟨w, mem_fixedVectors_of_le ρ hLK w.property⟩ = (b K hK hKK₀).inner v w)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hKK₀ : K ≤ K₀) {v w : V}
    (hv : v ∈ fixedVectors ρ K.toSubgroup) (hw : w ∈ fixedVectors ρ K.toSubgroup) :
    gluedInner ρ hρ hK₀ b v w = (b K hK hKK₀).inner ⟨v, hv⟩ ⟨w, hw⟩ :=
  gluedInner_eq hρ hK₀ hcompat K hK hKK₀ ⟨v, hv⟩ ⟨w, hw⟩

variable (ρ) in
/-- A compact open level below `K₀` fixing three given vectors. -/
def tripleLevel (K₀ : OpenSubgroup G) (u v w : V) : OpenSubgroup G :=
  pairLevel ρ hρ K₀ u v ⊓ stabilizer ρ hρ w

omit [IsTopologicalGroup G] in
theorem tripleLevel_le (u v w : V) : tripleLevel ρ hρ K₀ u v w ≤ K₀ :=
  inf_le_left.trans (pairLevel_le ρ hρ u v)

omit [IsTopologicalGroup G] in
theorem mem_tripleLevel_left (u v w : V) :
    u ∈ fixedVectors ρ (tripleLevel ρ hρ K₀ u v w).toSubgroup :=
  mem_fixedVectors_of_le ρ inf_le_left (left_mem_pairLevel ρ hρ u v)

omit [IsTopologicalGroup G] in
theorem mem_tripleLevel_middle (u v w : V) :
    v ∈ fixedVectors ρ (tripleLevel ρ hρ K₀ u v w).toSubgroup :=
  mem_fixedVectors_of_le ρ inf_le_left (right_mem_pairLevel ρ hρ u v)

omit [IsTopologicalGroup G] in
theorem mem_tripleLevel_right (u v w : V) :
    w ∈ fixedVectors ρ (tripleLevel ρ hρ K₀ u v w).toSubgroup :=
  mem_fixedVectors_of_le ρ inf_le_right (mem_fixedVectors_stabilizer ρ hρ w)

variable (ρ b) in
/-- The glued positive definite Hermitian form on `V`. -/
abbrev gluedCore
    (hcompat : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hKK₀ : K ≤ K₀)
      (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) (hLK₀ : L ≤ K₀) (hLK : L ≤ K)
      (v w : fixedVectors ρ K.toSubgroup),
      (b L hL hLK₀).inner ⟨v, mem_fixedVectors_of_le ρ hLK v.property⟩
        ⟨w, mem_fixedVectors_of_le ρ hLK w.property⟩ = (b K hK hKK₀).inner v w) :
    InnerProductSpace.Core ℂ V where
  inner := gluedInner ρ hρ hK₀ b
  conj_inner_symm v w := by
    have hP := pairLevel_le ρ hρ (K₀ := K₀) v w
    have hPc := isCompact_of_le hK₀ hP
    rw [gluedInner_eq_of_mem hρ hK₀ hcompat _ hPc hP (right_mem_pairLevel ρ hρ v w)
      (left_mem_pairLevel ρ hρ v w)]
    exact (b _ hPc hP).conj_inner_symm _ _
  re_inner_nonneg v := (b _ _ _).re_inner_nonneg _
  add_left u v w := by
    have hT := tripleLevel_le hρ (K₀ := K₀) u v w
    have hTc := isCompact_of_le hK₀ hT
    have hu := mem_tripleLevel_left hρ (K₀ := K₀) u v w
    have hv := mem_tripleLevel_middle hρ (K₀ := K₀) u v w
    have hw := mem_tripleLevel_right hρ (K₀ := K₀) u v w
    rw [gluedInner_eq_of_mem hρ hK₀ hcompat _ hTc hT (add_mem hu hv) hw,
      gluedInner_eq_of_mem hρ hK₀ hcompat _ hTc hT hu hw,
      gluedInner_eq_of_mem hρ hK₀ hcompat _ hTc hT hv hw]
    exact (b _ hTc hT).add_left ⟨u, hu⟩ ⟨v, hv⟩ ⟨w, hw⟩
  smul_left v w c := by
    have hP := pairLevel_le ρ hρ (K₀ := K₀) v w
    have hPc := isCompact_of_le hK₀ hP
    have hv := left_mem_pairLevel ρ hρ (K₀ := K₀) v w
    have hw := right_mem_pairLevel ρ hρ (K₀ := K₀) v w
    rw [gluedInner_eq_of_mem hρ hK₀ hcompat _ hPc hP (Submodule.smul_mem _ c hv) hw,
      gluedInner_eq_of_mem hρ hK₀ hcompat _ hPc hP hv hw]
    exact (b _ hPc hP).smul_left ⟨v, hv⟩ ⟨w, hw⟩ c
  definite v hv := by
    have h := (b _ _ _).definite _ hv
    exact congrArg Subtype.val h

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  [IsMulRightInvariant μ] [IsInvInvariant μ]

include hK₀ in
/-- **Gluing.** If for every compact open `K ≤ K₀` the fixed space `ρ^K` carries a
positive definite Hermitian form for which the corner involution is the adjoint of the
corner action, and these forms are compatible under restriction to smaller levels, then
`ρ` is unitarizable. -/
theorem isUnitarizable_of_compatibleCornerForms
    (hstar : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hKK₀ : K ≤ K₀)
      (f : Hecke.HeckeAlgebra.Corner μ K hK) (x y : fixedVectors ρ K.toSubgroup),
      (b K hK hKK₀).inner (Hecke.cornerAction μ ρ hρ K hK f x) y =
        (b K hK hKK₀).inner x (Hecke.cornerAction μ ρ hρ K hK (star f) y))
    (hcompat : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hKK₀ : K ≤ K₀)
      (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) (hLK₀ : L ≤ K₀) (hLK : L ≤ K)
      (v w : fixedVectors ρ K.toSubgroup),
      (b L hL hLK₀).inner ⟨v, mem_fixedVectors_of_le ρ hLK v.property⟩
        ⟨w, mem_fixedVectors_of_le ρ hLK w.property⟩ = (b K hK hKK₀).inner v w) :
    IsUnitarizable ρ := by
  refine ⟨{ toInnerProductCore := gluedCore ρ hρ hK₀ b hcompat, invariant := ?_ }⟩
  intro g v w
  change gluedInner ρ hρ hK₀ b (ρ g v) (ρ g w) = gluedInner ρ hρ hK₀ b v w
  set K := pairLevel ρ hρ K₀ v w
  have hKK₀ : K ≤ K₀ := pairLevel_le ρ hρ v w
  set L := K ⊓ conjOpenSubgroup g K
  have hLK : L ≤ K := inf_le_left
  have hLK₀ : L ≤ K₀ := hLK.trans hKK₀
  have hL : IsCompact (L : Set G) := isCompact_of_le hK₀ hLK₀
  have hv : v ∈ fixedVectors ρ L.toSubgroup :=
    mem_fixedVectors_of_le ρ hLK (left_mem_pairLevel ρ hρ v w)
  have hw : w ∈ fixedVectors ρ L.toSubgroup :=
    mem_fixedVectors_of_le ρ hLK (right_mem_pairLevel ρ hρ v w)
  have hgv : ρ g v ∈ fixedVectors ρ L.toSubgroup :=
    mem_fixedVectors_of_le ρ inf_le_right
      (mem_fixedVectors_conj ρ (left_mem_pairLevel ρ hρ v w) g)
  have hgw : ρ g w ∈ fixedVectors ρ L.toSubgroup :=
    mem_fixedVectors_of_le ρ inf_le_right
      (mem_fixedVectors_conj ρ (right_mem_pairLevel ρ hρ v w) g)
  set f := Hecke.translateCornerElement μ L hL g
  have hf : Hecke.cornerAction μ ρ hρ L hL f ⟨v, hv⟩ = ⟨ρ g v, hgv⟩ := by
    rw [Hecke.cornerAction_translateCornerElement]
    exact Hecke.fixedProjection_fixed μ ρ hρ L hL ⟨ρ g v, hgv⟩
  have hfs : Hecke.cornerAction μ ρ hρ L hL (star f) ⟨ρ g w, hgw⟩ = ⟨w, hw⟩ := by
    rw [Hecke.cornerAction_star_translateCornerElement]
    have hw' : ρ g⁻¹ (ρ g w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    simp only [hw']
    exact Hecke.fixedProjection_fixed μ ρ hρ L hL ⟨w, hw⟩
  rw [gluedInner_eq_of_mem hρ hK₀ hcompat L hL hLK₀ hgv hgw,
    gluedInner_eq_of_mem hρ hK₀ hcompat L hL hLK₀ hv hw, ← hf, hstar, hfs]

end CornerFormGluing

end Langlands
