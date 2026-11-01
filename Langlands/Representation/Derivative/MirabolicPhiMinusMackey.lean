import Langlands.Representation.Derivative.MirabolicPlus
import Langlands.Representation.Derivative.MirabolicMinusExactnessProof
import Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
import Langlands.Representation.Jacquet.LocalizationTransport

/-!
# Unnormalized `Φ⁻` through the plus subgroup, and the two-orbit sequence

Unnormalized `Φ⁻` of a representation of `P_(t+2)` only uses its restriction
to the plus subgroup `Q = P_(t+1) V_(t+2)`. This file defines the same
character localization for arbitrary representations of `Q`, by the kernel of
`plusProjection` and the restriction of `thetaPlus`, with `P_(t+1)` acting
through `plusSuccessor`, and identifies it with `Φ⁻` after restriction. It is
exact on short exact sequences with smooth middle term. Applied to the
published closed-subgroup Mackey filtration of a compact induction from a
closed subgroup `H` of `P_(t+2)` with two ordered `(H, Q)` orbits, it gives a
natural short exact sequence whose middle term is unnormalized `Φ⁻` of the
compact induction and whose outer terms are the localized orbit pieces.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

universe uF uV uR uG uC vC

/-! ## Transport of pointwise short exactness along isomorphisms -/

section Exact

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C]

/-- Pointwise short exactness of a pair of natural transformations is preserved by
composing with natural isomorphisms at the three positions. -/
theorem exact_comp_isos {A B D A' B' D' : C ⥤ Rep.{uV} R G}
    (i : A ⟶ B) (q : B ⟶ D) (eA : A' ≅ A) (eB : B ≅ B') (eD : D ≅ D')
    (h : ∀ X, Function.Injective (i.app X).hom ∧
      LinearMap.range (i.app X).hom.toLinearMap = LinearMap.ker (q.app X).hom.toLinearMap ∧
      Function.Surjective (q.app X).hom) :
    ∀ X, Function.Injective ((eA.hom ≫ i ≫ eB.hom).app X).hom ∧
      LinearMap.range ((eA.hom ≫ i ≫ eB.hom).app X).hom.toLinearMap =
        LinearMap.ker ((eB.inv ≫ q ≫ eD.hom).app X).hom.toLinearMap ∧
      Function.Surjective ((eB.inv ≫ q ≫ eD.hom).app X).hom := by
  intro X
  obtain ⟨hi, hex, hq⟩ := h X
  have a₁ : ∀ x, (eA.inv.app X).hom ((eA.hom.app X).hom x) = x :=
    fun x => Rep.inv_hom_apply _ _ (eA.app X) x
  have a₂ : ∀ x, (eA.hom.app X).hom ((eA.inv.app X).hom x) = x :=
    fun x => Rep.hom_inv_apply _ _ (eA.app X) x
  have b₁ : ∀ x, (eB.inv.app X).hom ((eB.hom.app X).hom x) = x :=
    fun x => Rep.inv_hom_apply _ _ (eB.app X) x
  have b₂ : ∀ x, (eB.hom.app X).hom ((eB.inv.app X).hom x) = x :=
    fun x => Rep.hom_inv_apply _ _ (eB.app X) x
  have d₁ : ∀ x, (eD.inv.app X).hom ((eD.hom.app X).hom x) = x :=
    fun x => Rep.inv_hom_apply _ _ (eD.app X) x
  have d₂ : ∀ x, (eD.hom.app X).hom ((eD.inv.app X).hom x) = x :=
    fun x => Rep.hom_inv_apply _ _ (eD.app X) x
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    change (eB.hom.app X).hom ((i.app X).hom ((eA.hom.app X).hom x)) =
      (eB.hom.app X).hom ((i.app X).hom ((eA.hom.app X).hom y)) at hxy
    have h₁ := congrArg (eB.inv.app X).hom hxy
    rw [b₁, b₁] at h₁
    have h₂ := congrArg (eA.inv.app X).hom (hi h₁)
    rwa [a₁, a₁] at h₂
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      change (eD.hom.app X).hom ((q.app X).hom ((eB.inv.app X).hom ((eB.hom.app X).hom
        ((i.app X).hom ((eA.hom.app X).hom y))))) = 0
      rw [b₁]
      have hk : (i.app X).hom ((eA.hom.app X).hom y) ∈
          LinearMap.ker (q.app X).hom.toLinearMap := by
        rw [← hex]
        exact ⟨_, rfl⟩
      have hk' : (q.app X).hom ((i.app X).hom ((eA.hom.app X).hom y)) = 0 := hk
      rw [hk', map_zero]
    · intro hx
      change (eD.hom.app X).hom ((q.app X).hom ((eB.inv.app X).hom x)) = 0 at hx
      have h₀ : (q.app X).hom ((eB.inv.app X).hom x) = 0 := by
        have h₁ := congrArg (eD.inv.app X).hom hx
        rwa [d₁, map_zero] at h₁
      have hmem : (eB.inv.app X).hom x ∈ LinearMap.range (i.app X).hom.toLinearMap := by
        rw [hex]
        exact h₀
      obtain ⟨y, hy⟩ := hmem
      refine ⟨(eA.inv.app X).hom y, ?_⟩
      change (eB.hom.app X).hom ((i.app X).hom ((eA.hom.app X).hom ((eA.inv.app X).hom y))) = x
      rw [a₂]
      change (eB.hom.app X).hom ((i.app X).hom.toLinearMap y) = x
      rw [hy, b₂]
  · intro z
    obtain ⟨y, hy⟩ := hq ((eD.inv.app X).hom z)
    refine ⟨(eB.hom.app X).hom y, ?_⟩
    change (eD.hom.app X).hom ((q.app X).hom ((eB.inv.app X).hom ((eB.hom.app X).hom y))) = z
    rw [b₁, hy, d₂]

end Exact

/-! ## The radical of the plus subgroup -/

section Kernel

variable (t : ℕ) (R : Type uR) [CommRing R]

/-- The radical `V_(t+2)` of `Q = P_(t+1) V_(t+2)`, as the kernel of `plusProjection`. -/
abbrev plusKernel : Subgroup (plusSubgroup t R) :=
  (plusProjection (n := t) (F := R)).ker

/-- The successor copy of `P_(t+1)` inside `Q`. -/
abbrev plusSuccessorRange : Subgroup (plusSubgroup t R) :=
  (plusSuccessor (n := t) (F := R)).range

/-- The successor map into its range. -/
abbrev plusSuccessorToRange : mirabolic t R →* plusSuccessorRange t R :=
  (plusSuccessor (n := t) (F := R)).rangeRestrict

/-- The kernel is normal, so every element of `Q` normalizes it. -/
theorem plusSuccessorRange_le_normalizer :
    plusSuccessorRange t R ≤ Subgroup.normalizer (plusKernel t R : Set (plusSubgroup t R)) := by
  intro g _
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top g

variable {t R}

theorem plusKernel_val_mem (u : plusKernel t R) : u.val.val ∈ radical (t + 1) R :=
  (projection_eq_one_iff u.val.val).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp u.property))

/-- The kernel identified with the actual radical, on underlying matrices. -/
def plusKernelEquiv : plusKernel t R ≃* radical (t + 1) R where
  toFun u := ⟨u.val.val, plusKernel_val_mem u⟩
  invFun u := ⟨plusRadical u, MonoidHom.mem_ker.mpr (plusProjection_plusRadical u)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem plusKernelEquiv_val (u : plusKernel t R) :
    (plusKernelEquiv u).val = u.val.val := rfl

section Topology

variable [TopologicalSpace R]

theorem continuous_plusKernelEquiv : Continuous (plusKernelEquiv (t := t) (R := R)) :=
  continuous_induced_rng.mpr (show Continuous (fun u : plusKernel t R => u.val.val) from
    continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_plusKernelEquiv_symm :
    Continuous (plusKernelEquiv (t := t) (R := R)).symm :=
  continuous_induced_rng.mpr (continuous_induced_rng.mpr continuous_subtype_val)

theorem continuous_plusSuccessorToRange :
    Continuous (plusSuccessorToRange t R) :=
  continuous_induced_rng.mpr (continuous_induced_rng.mpr continuous_successor)

end Topology

end Kernel

section Character

variable {R : Type uR} [CommRing R] [TopologicalSpace R] (ψ : UnitaryAdditiveCharacter R) (t : ℕ)

/-- The restriction of `thetaPlus` to the kernel of `plusProjection`. -/
def plusKernelTheta : plusKernel t R →* ℂˣ :=
  (thetaPlus ψ t).comp (plusKernel t R).subtype

/-- On the kernel, the character is the published radical character. -/
theorem plusKernelTheta_apply (u : plusKernel t R) :
    plusKernelTheta ψ t u = theta ψ t (plusKernelEquiv u) := rfl

/-- The character is the restriction of a character of `Q`, hence conjugation invariant. -/
theorem plusKernelTheta_isInvariant :
    Jacquet.Localization.IsInvariant (plusKernel t R) (plusSuccessorRange t R)
      (plusSuccessorRange_le_normalizer t R) (plusKernelTheta ψ t) := by
  intro m u
  change thetaPlus ψ t ((m : plusSubgroup t R) * (u : plusSubgroup t R) *
    (m : plusSubgroup t R)⁻¹) = thetaPlus ψ t (u : plusSubgroup t R)
  rw [map_mul, map_mul, map_inv, mul_comm (thetaPlus ψ t (m : plusSubgroup t R)),
    mul_inv_cancel_right]

/-- Unnormalized `Φ⁻` for representations of `Q`: the `thetaPlus`-localized
quotient by the kernel of `plusProjection`, with `P_(t+1)` acting through
`plusSuccessor`. -/
def plusPhiLocalization : Rep.{uV} ℂ (plusSubgroup t R) ⥤ Rep.{uV} ℂ (mirabolic t R) :=
  Jacquet.Localization.functor (plusKernel t R) (plusKernelTheta ψ t) (plusSuccessorRange t R)
      (plusSuccessorRange_le_normalizer t R) (plusKernelTheta_isInvariant ψ t) ⋙
    Rep.resFunctor (plusSuccessorToRange t R)

/-- The object carrier is the actual character-localized quotient. -/
theorem plusPhiLocalization_obj_carrier (A : Rep.{uV} ℂ (plusSubgroup t R)) :
    ((plusPhiLocalization ψ t).obj A : Type uV) =
      Jacquet.Localization.Coinvariants A.ρ (plusKernel t R) (plusKernelTheta ψ t) := rfl

/-- `g • [v] = [successor g • v]`. -/
theorem plusPhiLocalization_action (A : Rep.{uV} ℂ (plusSubgroup t R)) (g : mirabolic t R)
    (v : A) :
    ((plusPhiLocalization ψ t).obj A).ρ g
        (Jacquet.Localization.mk A.ρ (plusKernel t R) (plusKernelTheta ψ t) v) =
      Jacquet.Localization.mk A.ρ (plusKernel t R) (plusKernelTheta ψ t)
        (A.ρ (plusSuccessor g) v) := rfl

/-- Maps send `[v]` to `[f v]`. -/
theorem plusPhiLocalization_map_mk {A B : Rep.{uV} ℂ (plusSubgroup t R)} (f : A ⟶ B) (v : A) :
    ((plusPhiLocalization ψ t).map f).hom
        (Jacquet.Localization.mk A.ρ (plusKernel t R) (plusKernelTheta ψ t) v) =
      Jacquet.Localization.mk B.ρ (plusKernel t R) (plusKernelTheta ψ t) (f.hom v) := rfl

end Character

/-! ## Comparison with `Φ⁻` and exactness -/

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Restricting to `Q` and localizing gives the actual unnormalized `Φ⁻` carrier: the
two relation spans agree through `plusKernelEquiv`, classes go to classes. -/
def plusPhiLocalizationEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (t + 1) F.Carrier)) :
    letI := T.topology
    Representation.Equiv
      ((SmoothRep.toRep ⋙ Rep.resFunctor (plusSubgroup t F.Carrier).subtype ⋙
        plusPhiLocalization ψ t).obj A).ρ
      ((phiMinusUnnormalized T ψ t ⋙ SmoothRep.toRep).obj A).ρ :=
  letI := T.topology
  Representation.Equiv.mk
    (Jacquet.Localization.transportEquiv (A.representation.comp (plusSubgroup t F.Carrier).subtype)
      A.representation (plusKernel t F.Carrier) (radical (t + 1) F.Carrier)
      (plusKernelTheta ψ t) (T.mirabolicTheta ψ t) plusKernelEquiv (LinearEquiv.refl ℂ A)
      (fun _ _ => rfl) (fun _ => rfl))
    (fun _ => LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun _ => rfl)

/-- The identification sends the class of `v` to its class. -/
theorem plusPhiLocalizationEquiv_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic (t + 1) F.Carrier))
    (v : letI := T.topology; A) :
    letI := T.topology
    plusPhiLocalizationEquiv T ψ t A
        (Jacquet.Localization.mk (A.representation.comp (plusSubgroup t F.Carrier).subtype)
          (plusKernel t F.Carrier) (plusKernelTheta ψ t) v) =
      phiMinusQuotient T ψ t A v := rfl

/-- Unnormalized `Φ⁻` factors naturally through restriction to `Q`. -/
def plusPhiLocalizationIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ) :
    letI := T.topology
    SmoothRep.toRep ⋙ Rep.resFunctor (plusSubgroup t F.Carrier).subtype ⋙
        plusPhiLocalization.{uV, uF} ψ t ≅
      phiMinusUnnormalized T ψ t ⋙ SmoothRep.toRep :=
  letI := T.topology
  NatIso.ofComponents (fun A => Rep.mkIso (plusPhiLocalizationEquiv T ψ t A)) (by
    intro A B f
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact Submodule.Quotient.induction_on _ x fun _ => rfl)

private theorem isLocallyConstant_of_isOpen_ker {G : Type uG} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) :
    IsLocallyConstant (fun g => (χ g : ℂ)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun y : G => y * x⁻¹) ⁻¹' (χ.ker : Set G),
    hχ.preimage (continuous_id.mul continuous_const), ?_, ?_⟩
  · simp
  · intro y hy
    change χ (y * x⁻¹) = 1 at hy
    have heq : χ y = χ x := mul_inv_eq_one.mp (by
      simpa only [map_mul, map_inv] using hy)
    exact congrArg (fun z : ℂˣ => (z : ℂ)) heq

/-- The localization on `Q` preserves short exact sequences with smooth middle term. -/
theorem plusPhiLocalization_exact (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ)
    {A B C : Rep.{uV} ℂ (plusSubgroup t F.Carrier)} (i : A ⟶ B) (q : B ⟶ C)
    (hi : Function.Injective i.hom) (hq : Function.Surjective q.hom)
    (hex : LinearMap.range i.hom.toLinearMap = LinearMap.ker q.hom.toLinearMap)
    (hB : letI := T.topology; IsSmooth B.ρ) :
    letI := T.topology
    Function.Injective ((plusPhiLocalization ψ t).map i).hom ∧
      LinearMap.range ((plusPhiLocalization ψ t).map i).hom.toLinearMap =
        LinearMap.ker ((plusPhiLocalization ψ t).map q).hom.toLinearMap ∧
      Function.Surjective ((plusPhiLocalization ψ t).map q).hom := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (t + 1 + 1)
  have hU : Jacquet.Localization.IsLimitOfCompactSubgroups (plusKernel t F.Carrier) := by
    intro K hK
    obtain ⟨L, hL, hKL⟩ := radical_isLimitOfCompactSubgroups F T (t + 1)
      (plusKernelEquiv '' K) (hK.image continuous_plusKernelEquiv)
    refine ⟨L.map plusKernelEquiv.symm.toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_map]
      exact hL.image continuous_plusKernelEquiv_symm
    · intro c hc
      exact ⟨plusKernelEquiv c, hKL ⟨c, hc, rfl⟩, plusKernelEquiv.symm_apply_apply c⟩
  have hθ : IsLocallyConstant (fun u : plusKernel t F.Carrier => (plusKernelTheta ψ t u : ℂ)) :=
    (isLocallyConstant_of_isOpen_ker _ (T.mirabolicTheta_isOpen_ker ψ t)).comp_continuous
      continuous_plusKernelEquiv
  exact (Jacquet.Localization.characterLocalizationExactness
    (G := plusSubgroup t F.Carrier) (V := A) (W := B) (X := C)).2
      (plusKernel t F.Carrier) hU (plusKernelTheta ψ t) hθ (plusSuccessorRange t F.Carrier)
      (plusSuccessorRange_le_normalizer t F.Carrier) (plusKernelTheta_isInvariant ψ t)
      A.ρ B.ρ C.ρ i.hom q.hom hi hq hex hB

/-! ## The two-orbit sequence -/

set_option maxHeartbeats 800000 in
/-- Localizing the published two-step Mackey sequence of a compact induction
from a closed subgroup `H` of `P_(t+2)`, restricted to `Q`, with two ordered
orbits. -/
theorem exists_exact_plusPhiLocalization (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ)
    (H : Subgroup (mirabolic (t + 1) F.Carrier))
    (hH : letI := T.topology; IsClosed (H : Set (mirabolic (t + 1) F.Carrier)))
    (s : letI := T.topology; letI := T.generalLinearTopologicalGroup (t + 1 + 1)
      Geometric.OrderedDoubleCosets H (plusSubgroup t F.Carrier) 2) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (t + 1 + 1)
    ∃ (i : Geometric.orbitPiece.{0, uF, uV} (R := ℂ) H (plusSubgroup t F.Carrier)
          (s.representative 0) ⋙ plusPhiLocalization ψ t ⟶
        Geometric.restrictedCompactInduction H (plusSubgroup t F.Carrier) ⋙
          plusPhiLocalization ψ t)
      (q : Geometric.restrictedCompactInduction.{0, uF, uV} (R := ℂ) H
          (plusSubgroup t F.Carrier) ⋙ plusPhiLocalization ψ t ⟶
        Geometric.orbitPiece H (plusSubgroup t F.Carrier) (s.representative 1) ⋙
          plusPhiLocalization ψ t),
      ∀ X, Function.Injective (i.app X).hom ∧
        LinearMap.range (i.app X).hom.toLinearMap = LinearMap.ker (q.app X).hom.toLinearMap ∧
        Function.Surjective (q.app X).hom := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (t + 1 + 1)
  let := T.fieldT2
  let := T.generalLinearNonarchimedean (t + 1 + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1 + 1)
  let := T.generalLinearT2Space (t + 1 + 1)
  let := T.generalLinearSigmaCompactSpace (t + 1 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := t + 1) (F := F.Carrier)
  have : NonarchimedeanGroup (mirabolic (t + 1) F.Carrier) :=
    { is_nonarchimedean := fun U hU => by
        rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hU
        obtain ⟨V, hV, hVU⟩ := hU
        obtain ⟨L, hL⟩ := NonarchimedeanGroup.is_nonarchimedean V (by simpa using hV)
        exact ⟨OpenSubgroup.comap (mirabolic (t + 1) F.Carrier).subtype
          continuous_subtype_val L, fun x hx => hVU (hL hx)⟩ }
  have : SigmaCompactSpace (mirabolic (t + 1) F.Carrier) :=
    (GeneralLinear.Mirabolic.isClosed (n := t + 1) (F := F.Carrier)).sigmaCompactSpace
  have hQ : IsClosed (plusSubgroup t F.Carrier : Set (mirabolic (t + 1) F.Carrier)) :=
    plusSubgroup_isClosed
  have hM := Geometric.closedSubgroupMackeyFiltration.{uF, uV}
    (mirabolic (t + 1) F.Carrier) H (plusSubgroup t F.Carrier) hH hQ 2 s
  obtain ⟨e₀⟩ := hM 0
  obtain ⟨e₁⟩ := hM 1
  obtain ⟨i, q, h⟩ := RepFunctorFiltration.exists_exact_of_two _ e₀ e₁
  refine ⟨Functor.whiskerRight i (plusPhiLocalization ψ t),
    Functor.whiskerRight q (plusPhiLocalization ψ t), fun X => ?_⟩
  obtain ⟨hi, hex, hq⟩ := h X
  exact plusPhiLocalization_exact T ψ t (i.app X) (q.app X) hi hq hex
    (isSmooth_comp (plusSubgroup t F.Carrier).subtype continuous_subtype_val
      (Induction.compactInduced_smooth H X.obj.ρ))

set_option maxHeartbeats 800000 in
/-- The same sequence with the middle term written as unnormalized `Φ⁻` of the
compact induction. -/
theorem exists_exact_phiMinusUnnormalized_compactInduction (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (t : ℕ)
    (H : Subgroup (mirabolic (t + 1) F.Carrier))
    (hH : letI := T.topology; IsClosed (H : Set (mirabolic (t + 1) F.Carrier)))
    (s : letI := T.topology; letI := T.generalLinearTopologicalGroup (t + 1 + 1)
      Geometric.OrderedDoubleCosets H (plusSubgroup t F.Carrier) 2) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (t + 1 + 1)
    ∃ (i : Geometric.orbitPiece.{0, uF, uV} (R := ℂ) H (plusSubgroup t F.Carrier)
          (s.representative 0) ⋙ plusPhiLocalization ψ t ⟶
        (SmoothRep.toRep ⋙ Induction.compactInductionFunctor H) ⋙
          phiMinusUnnormalized T ψ t ⋙ SmoothRep.toRep)
      (q : (SmoothRep.toRep ⋙ Induction.compactInductionFunctor.{0, uF, uV} (R := ℂ) H) ⋙
          phiMinusUnnormalized T ψ t ⋙ SmoothRep.toRep ⟶
        Geometric.orbitPiece H (plusSubgroup t F.Carrier) (s.representative 1) ⋙
          plusPhiLocalization ψ t),
      ∀ X, Function.Injective (i.app X).hom ∧
        LinearMap.range (i.app X).hom.toLinearMap = LinearMap.ker (q.app X).hom.toLinearMap ∧
        Function.Surjective (q.app X).hom := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (t + 1 + 1)
  obtain ⟨i, q, h⟩ := exists_exact_plusPhiLocalization.{uF, uV} T ψ t H hH s
  let eB : Geometric.restrictedCompactInduction.{0, uF, uV} (R := ℂ) H
        (plusSubgroup t F.Carrier) ⋙ plusPhiLocalization ψ t ≅
      (SmoothRep.toRep ⋙ Induction.compactInductionFunctor.{0, uF, uV} (R := ℂ) H) ⋙
        phiMinusUnnormalized T ψ t ⋙ SmoothRep.toRep :=
    Functor.isoWhiskerLeft (SmoothRep.toRep ⋙ Induction.compactInductionFunctor H)
      (plusPhiLocalizationIso.{uF, max uF uV} T ψ t)
  refine ⟨(Iso.refl _).hom ≫ i ≫ eB.hom, eB.inv ≫ q ≫ (Iso.refl _).hom, ?_⟩
  exact exact_comp_isos i q (Iso.refl _) eB (Iso.refl _) h

end Padic

end Langlands.Derivative.Mirabolic
