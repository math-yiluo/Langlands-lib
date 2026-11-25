/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpen
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpenNormal
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusConjugacy
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusRestriction
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.RestrictionWeilGroup
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic

/-!
# The Weil group of a curve over a finite field

Let `p : C₀ ⟶ Spec 𝔽_q` be a curve which is geometrically connected. This file constructs a
`AlgebraicGeometry.WeilGroup` of `C₀` (`AlgebraicGeometry.WeilGroup.ofFundamentalGroup`): the
Weil group `W(C₀, s) ⊆ π₁(C₀, s) × ℤ` of a fundamental group `π₁(C₀, s)` at a geometric point
`s` with values in `𝔽̄_q`, with the topology induced from `π₁(C₀, s) × ℤ`, `ℤ` being discrete. In
this topology the geometric part `ker deg` is open and is the subspace
`ker (π₁(C₀, s) → Gal(𝔽̄_q / 𝔽_q))` of the profinite group `π₁(C₀, s)`.

The degree is surjective since the geometric Frobenius lifts to `π₁(C₀, s)`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_smul_eq_geometricFrobenius`), and the local
Frobenius at a closed point `x` is a Frobenius element at `x`, of degree `e_x`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_isFrobeniusElement`).

## Main definitions

- `AlgebraicGeometry.WeilGroup.ofFundamentalGroup`: the Weil group of a geometrically connected
  curve over a finite field.
- `AlgebraicGeometry.WeilGroup.restrictionOfPath`: the restriction of Weil groups along an open
  immersion of curves.
- `AlgebraicGeometry.WeilGroup.toStandard`: every Weil group is isomorphic to the one built from
  its base point and fundamental group.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry

namespace Scheme.FiniteEtale

section Topology

variable {K : Type u} [Field K] [Finite K] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of K))
  [GeometricallyConnected p] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X₀)
  (G : Type u) [Group G] [∀ P, MulAction G ((fiber s).obj P)] [TopologicalSpace G]

/-- The degree map of the Weil group is continuous for the topology induced from
`π₁(X₀, s) × ℤ`. -/
lemma continuous_weilGroupDeg : Continuous (weilGroupDeg p s G) :=
  continuous_snd.comp continuous_subtype_val

/-- The geometric part `ker deg` of the Weil group is open. -/
lemma isOpen_ker_weilGroupDeg :
    IsOpen ((weilGroupDeg p s G).ker : Set (weilGroup p s G)) :=
  (isOpen_discrete {(1 : Multiplicative ℤ)}).preimage (continuous_weilGroupDeg p s G)

/-- The inclusion of the geometric part `ker deg` of the Weil group into `π₁(X₀, s)` is an
embedding. -/
lemma isEmbedding_ker_weilGroupDeg :
    Topology.IsEmbedding fun g : (weilGroupDeg p s G).ker ↦ (g.1 : G × Multiplicative ℤ).1 := by
  have hι : Topology.IsEmbedding fun g : (weilGroupDeg p s G).ker ↦
      (g.1 : G × Multiplicative ℤ) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have heq : (fun g : (weilGroupDeg p s G).ker ↦ (g.1 : G × Multiplicative ℤ)) =
      (fun g : G ↦ (g, (1 : Multiplicative ℤ))) ∘
        fun g : (weilGroupDeg p s G).ker ↦ (g.1 : G × Multiplicative ℤ).1 := by
    funext g
    exact Prod.ext rfl g.2
  refine ⟨Topology.IsInducing.of_comp (continuous_fst.comp hι.continuous)
    (continuous_id.prodMk continuous_const) (heq ▸ hι.isInducing), fun g h hgh ↦ ?_⟩
  exact hι.injective (Prod.ext hgh ((MonoidHom.mem_ker.1 g.2).trans (MonoidHom.mem_ker.1 h.2).symm))

open scoped FintypeCatDiscrete in
/-- The geometric part `ker deg` of the Weil group is compact: it is the closed subset of the
compact group `π₁(X₀, s)` of the elements acting trivially on the constant covers. -/
lemma isCompact_ker_weilGroupDeg [CompactSpace G] [∀ P, ContinuousSMul G ((fiber s).obj P)] :
    IsCompact ((weilGroupDeg p s G).ker : Set (weilGroup p s G)) := by
  let T : Set G := {g | ∀ (A : FiniteEtaleAlgebra K) (y : (fiber s).obj (constantCover p A)),
    g • y = y}
  have hT : IsClosed T := by
    simp only [T, Set.ofPred_forall]
    exact isClosed_iInter fun A ↦ isClosed_iInter fun y ↦
      isClosed_eq (continuous_id.smul continuous_const) continuous_const
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  convert (hT.isCompact.prod isCompact_singleton : IsCompact (T ×ˢ {(1 : Multiplicative ℤ)}))
  ext ⟨g, n⟩
  simp only [Set.mem_image, SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_prod,
    Set.mem_singleton_iff, T]
  constructor
  · rintro ⟨w, hw, hwe⟩
    obtain rfl : (w : G × Multiplicative ℤ).1 = g := congrArg Prod.fst hwe
    obtain rfl : (w : G × Multiplicative ℤ).2 = n := congrArg Prod.snd hwe
    have h1 : (w : G × Multiplicative ℤ).2 = 1 := hw
    refine ⟨fun A y ↦ ?_, h1⟩
    rw [(mem_weilGroup_iff p s G).1 w.2 A y, h1]
    simp
  · rintro ⟨hg, rfl⟩
    refine ⟨⟨(g, 1), (mem_weilGroup_iff p s G).2 fun A y ↦ ?_⟩, rfl, rfl⟩
    simpa using hg A y

end Topology

end Scheme.FiniteEtale

/-- A nonempty quasi-compact scheme locally of finite type over a finite field `K` has a point
with values in the algebraic closure of `K`: the residue field at a closed point is finite over
`K`. -/
lemma Scheme.Hom.nonempty_algebraicClosure_point {K : Type u} [Field K] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p] [QuasiCompact p] [Nonempty C] :
    Nonempty (Spec (.of (AlgebraicClosure K)) ⟶ C) := by
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := C)).exists_closed_singleton Set.univ_nonempty
  let := (p.residueFieldAlgebraMap x).toAlgebra
  have := p.finite_residueField_of_isClosed x hx
  let ι := IsAlgClosed.lift (M := AlgebraicClosure K) (R := K) (S := C.residueField x)
  exact ⟨Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ C.fromSpecResidueField x⟩

namespace WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} (p : C ⟶ Spec (.of K)) [IsCurve p]
  [GeometricallyConnected p] (s : Spec (.of (AlgebraicClosure K)) ⟶ C)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]

open Scheme.FiniteEtale

variable [ConnectedSpace C] [IsFundamentalGroup (fiber s) G]

omit [Finite K] [IsCurve p] [GeometricallyConnected p] in
/-- A choice of Frobenius element of `π₁(C₀, s)` at a closed point `x`. -/
noncomputable def frobeniusElement (x : C.finitePoints) : G :=
  have : Finite (C.residueField x.1) := x.2
  (exists_isFrobeniusElement s G x.1).choose

omit [Finite K] [IsCurve p] [GeometricallyConnected p] in
lemma isFrobeniusElement_frobeniusElement (x : C.finitePoints) :
    have : Finite (C.residueField x.1) := x.2
    IsFrobeniusElement s G x.1 (frobeniusElement s G x) :=
  have : Finite (C.residueField x.1) := x.2
  (exists_isFrobeniusElement s G x.1).choose_spec

/-- The local Frobenius at a closed point `x`, as an element of the Weil group of degree `e_x`. -/
noncomputable def weilFrobenius (x : C.finitePoints) : weilGroup p s G :=
  have : Finite (C.residueField x.1) := x.2
  ⟨(frobeniusElement s G x, Multiplicative.ofAdd (p.degreeOver x.1 : ℤ)),
    (isFrobeniusElement_frobeniusElement s G x).mem_weilGroup p⟩

/-- **The Weil group of a geometrically connected curve over a finite field**, built from a
fundamental group `G = π₁(C₀, s)` at a geometric point `s` with values in `𝔽̄_q`: the subgroup
`W(C₀, s) ⊆ π₁(C₀, s) × ℤ` with the induced topology, the local Frobenius at a closed point
being a chosen Frobenius element. (blueprint `definition-weil-representation--1`,
`situation-weil`) -/
noncomputable def ofFundamentalGroup : WeilGroup p :=
  have : TotallyDisconnectedSpace G :=
    (toAutHomeo (fiber s) G).symm.totallyDisconnectedSpace
  have hcont : ∀ P, ContinuousSMul G ((fiber s).obj P) := fun P ↦
    IsFundamentalGroup.continuous_smul P
  let γ := (exists_mem_weilGroup_snd_eq_one p s G).choose
  have hγ := (exists_mem_weilGroup_snd_eq_one p s G).choose_spec
  { carrier := weilGroup p s G
    deg := weilGroupDeg p s G
    deg_surjective := fun n ↦ ⟨⟨(γ, Multiplicative.ofAdd 1), hγ⟩ ^ n.toAdd, by
      rw [map_zpow]
      change (Multiplicative.ofAdd 1) ^ n.toAdd = n
      rw [← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]⟩
    isOpen_ker := isOpen_ker_weilGroupDeg p s G
    compactSpace_ker := isCompact_iff_compactSpace.mp (isCompact_ker_weilGroupDeg p s G)
    totallyDisconnectedSpace_ker := inferInstance
    frobeniusLift := ⟨(γ, Multiplicative.ofAdd 1), hγ⟩
    deg_frobeniusLift := rfl
    frobenius := weilFrobenius p s G
    deg_frobenius _ := rfl
    basePoint := s
    fundamentalGroup := G
    weilGroupEquiv := MulEquiv.refl _
    deg_eq _ := rfl
    isEmbedding_ker := isEmbedding_ker_weilGroupDeg p s G
    isFrobeniusElement_frobenius := isFrobeniusElement_frobeniusElement s G }

omit [ConnectedSpace C] [IsFundamentalGroup (fiber s) G] in
/-- A geometrically connected curve over a finite field has a Weil group. -/
theorem nonempty (p : C ⟶ Spec (.of K)) [IsCurve p] [GeometricallyConnected p] :
    Nonempty (WeilGroup p) := by
  have : ConnectedSpace C := GeometricallyConnected.connectedSpace_of_subsingleton p
  obtain ⟨s⟩ := p.nonempty_algebraicClosure_point
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup s
  exact ⟨ofFundamentalGroup p s G⟩


section Restriction

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  [GeometricallyConnected p] [ConnectedSpace C] {pU : U ⟶ Spec (.of K)} [IsCurve pU]
  [GeometricallyConnected pU] [ConnectedSpace U] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]
  (hj : j ≫ p = pU) {sU : Spec (.of (AlgebraicClosure K)) ⟶ U}
  {sC : Spec (.of (AlgebraicClosure K)) ⟶ C} (τ : fiber (sU ≫ j) ≅ fiber sC)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]
  (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC] [CompactSpace GC]
  [∀ P, MulAction GC ((fiber sC).obj P)] [IsFundamentalGroup (fiber sC) GC]

/-- The map `π₁(U₀, s_U) → π₁(C₀, s_C)` induced by `j` and the path `τ`. -/
noncomputable abbrev restrictionMap : GU →* GC :=
  fundamentalGroupMap (pullbackFiberIso j sU ≪≫ τ) GU GC

include hj in
/-- The restriction `W(U₀) → W(C₀)` of Weil groups. -/
noncomputable def restrictionHom : weilGroup pU sU GU →* weilGroup p sC GC :=
  ((((restrictionMap j τ GU GC).prodMap (MonoidHom.id _)).comp
    (weilGroup pU sU GU).subtype).codRestrict _ fun w ↦
      (mem_weilGroup_fundamentalGroupMap_iff j hj sU τ GU GC _ _).1 w.2)

omit [IsCurve p] [IsCurve pU] [IsOpenImmersion j] [Nonempty U] in
lemma restrictionHom_apply (w : weilGroup pU sU GU) :
    (restrictionHom j hj τ GU GC w : GC × Multiplicative ℤ) =
      (restrictionMap j τ GU GC (w : GU × Multiplicative ℤ).1, (w : GU × Multiplicative ℤ).2) :=
  rfl

omit [Finite K] [GeometricallyConnected p] [Nonempty U] in
/-- On a smooth curve, base change to a nonempty open preserves connectedness of finite étale
covers: a connected finite étale cover is smooth over `K`, hence regular, hence irreducible, and
a nonempty open subscheme of an irreducible scheme is connected (Stacks `0BQM`). -/
lemma isConnected_pullback_of_smooth [Smooth p] (P : C.FiniteEtale) (hP : IsConnected P) :
    IsConnected ((Scheme.FiniteEtale.pullback j).obj P) := by
  have := connectedSpace_of_isConnected P
  have : Etale P.obj.hom := P.obj.prop
  let q : P.obj.left ⟶ Spec (.of K) := P.obj.hom ≫ p
  have : Smooth q := inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian q
  have := IsRegular.of_smooth q
  have := IsRegular.irreducibleSpace P.obj.left
  exact isConnected_pullback_of_irreducibleSpace j P

omit [Finite K] [GeometricallyConnected p] [Nonempty U] in
/-- **The fundamental group of a dense open of a smooth curve surjects** onto that of the curve
(Stacks `0BQM`, blueprint `theorem-purity-real-sheaves-curves`). -/
lemma restrictionMap_surjective [Smooth p] : Function.Surjective (restrictionMap j τ GU GC) :=
  fundamentalGroupMap_surjective _ GC GU fun P hP ↦ isConnected_pullback_of_smooth (p := p) j P hP

omit [IsCurve pU] [Nonempty U] in
include hj in
lemma restrictionHom_surjective [Smooth p] :
    Function.Surjective (restrictionHom j hj τ GU GC) := by
  rintro ⟨⟨h, n⟩, hw⟩
  obtain ⟨γ, hγ⟩ := exists_mem_weilGroup_snd_eq_one pU sU GU
  let g₀ : weilGroup pU sU GU := ⟨(γ, Multiplicative.ofAdd 1), hγ⟩ ^ n.toAdd
  have hg₀ : (g₀ : GU × Multiplicative ℤ).2 = n := by
    change (Multiplicative.ofAdd 1) ^ n.toAdd = n
    rw [← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
  have hρg₀ := (restrictionHom j hj τ GU GC g₀).2
  rw [restrictionHom_apply, hg₀] at hρg₀
  have h' : (((restrictionMap j τ GU GC g₀.1.1)⁻¹ * h, 1) : GC × Multiplicative ℤ) ∈
      weilGroup p sC GC := by
    convert (weilGroup p sC GC).mul_mem ((weilGroup p sC GC).inv_mem hρg₀) hw using 1
    simp
  obtain ⟨g₁, hg₁⟩ := restrictionMap_surjective (p := p) j τ GU GC
    ((restrictionMap j τ GU GC g₀.1.1)⁻¹ * h)
  have hg₁W : (g₁, (1 : Multiplicative ℤ)) ∈ weilGroup pU sU GU :=
    (mem_weilGroup_fundamentalGroupMap_iff j hj sU τ GU GC _ _).2 (hg₁ ▸ h')
  refine ⟨g₀ * ⟨_, hg₁W⟩, Subtype.ext ?_⟩
  rw [restrictionHom_apply]
  simp only [Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul, map_mul, hg₁, hg₀, mul_one,
    mul_inv_cancel_left]

omit [ConnectedSpace U] [IsCurve pU] [GeometricallyConnected pU] [Nonempty U] [IsCurve p]
  [GeometricallyConnected p] [ConnectedSpace C] in
lemma degreeOver_eq (x : U) (hx : x ∈ U.finitePoints) :
    p.degreeOver (j x) = pU.degreeOver x := by
  have : Finite (U.residueField x) := hx
  have hx' : j x ∈ C.finitePoints :=
    Finite.of_equiv _ (residueFieldEquiv j x).symm.toEquiv
  have h1 := p.pointNorm_eq_pow_degreeOver hx'
  have h2 := pU.pointNorm_eq_pow_degreeOver hx
  rw [Scheme.pointNorm, natCard_residueField_eq] at h1
  rw [Scheme.pointNorm] at h2
  have hq : 1 < Nat.card K := Finite.one_lt_card
  exact Nat.pow_right_injective hq (h1.symm.trans h2)

include hj in
/-- **The restriction of Weil groups along an open immersion** of curves `j : U₀ ⟶ C₀`, for a
smooth curve `C₀`, the Weil groups being those of `AlgebraicGeometry.WeilGroup.ofFundamentalGroup`
and the path `τ` from `s_U ≫ j` to `s_C` arbitrary. (blueprint `lemma-boundary-stalk--2`,
`theorem-purity-real-sheaves-curves`) -/
noncomputable def restrictionOfPath [Smooth p] :
    Restriction j (ofFundamentalGroup pU sU GU) (ofFundamentalGroup p sC GC) where
  comp_eq := hj
  restrict := restrictionHom j hj τ GU GC
  fiberIso := pullbackFiberIso j sU ≪≫ τ
  restrict_smul g P y := fundamentalGroupMap_smul (pullbackFiberIso j sU ≪≫ τ) GU GC g.1.1 P y
  continuous_restrict := by
    have := fun P ↦ IsFundamentalGroup.continuous_smul (F := fiber sU) (G := GU) P
    refine Continuous.subtype_mk (((continuous_fundamentalGroupMap _ GU GC).comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
        (continuous_snd.comp continuous_subtype_val)) _
  deg_restrict := rfl
  surjective_restrict := restrictionHom_surjective j hj τ GU GC
  restrict_frobenius x y hxy := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain rfl : j x = y := hxy
    have : Finite (U.residueField x) := hx
    have : Finite (C.residueField (j x)) := hy
    have h₁ := isFrobeniusElement_frobeniusElement sC GC ⟨j x, hy⟩
    have h₂ := IsFrobeniusElement.fundamentalGroupMap j x (pullbackFiberIso j sU ≪≫ τ) GU GC
      (isFrobeniusElement_frobeniusElement sU GU ⟨x, hx⟩)
    obtain ⟨c, n, hcW, hc⟩ := h₁.exists_mem_weilGroup_conj p sC GC h₂
    refine isConj_iff.2 ⟨⟨(c, n), hcW⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · exact hc
    · change n * Multiplicative.ofAdd (p.degreeOver (j x) : ℤ) * n⁻¹ =
        Multiplicative.ofAdd (pU.degreeOver x : ℤ)
      rw [mul_comm n, mul_assoc, mul_inv_cancel, mul_one, degreeOver_eq j x hx]

include hj in
/-- A nonempty open `j : U₀ ⟶ C₀` of a smooth geometrically connected curve over a finite field,
itself geometrically connected, has a restriction of Weil groups. -/
theorem Restriction.nonempty [Smooth p] :
    ∃ (WU : WeilGroup pU) (WC : WeilGroup p), Nonempty (Restriction j WU WC) := by
  obtain ⟨sU⟩ := pU.nonempty_algebraicClosure_point
  obtain ⟨sC⟩ := p.nonempty_algebraicClosure_point
  obtain ⟨GU, _, _⟩ := exists_isFundamentalGroup sU
  obtain ⟨GC, _, _⟩ := exists_isFundamentalGroup sC
  obtain ⟨τ⟩ := nonempty_iso_of_fiberFunctor (fiber (sU ≫ j)) (fiber sC)
  exact ⟨_, _, ⟨restrictionOfPath j hj τ GU GC⟩⟩

end Restriction

section RestrictionRegular

/-! ### Restriction of Weil groups along a dense open, in general

The restriction `W(U₀) → W(C₀)` of `AlgebraicGeometry.WeilGroup.restrictionHom` is defined for
any open immersion `j : U₀ ⟶ C₀` of connected, geometrically connected schemes over a finite
field, not only for curves. It preserves the degrees, it is the map of fundamental groups
`AlgebraicGeometry.WeilGroup.restrictionMap` on the underlying elements, hence on the geometric
subgroups `ker deg`, and it is surjective as soon as that map is, e.g. for `C₀` regular or normal
(blueprint `theorem-purity-real-sheaves-curves`, part (2)).

The blueprint states part (2) for `V₀` separated of finite type over `k₀` with `V = V₀ ⊗ k`
connected and normal. Here normality is asked of `V₀` (its local rings are integrally closed
domains); it follows from normality of `V` by faithfully flat descent, and is equivalent to it
over the perfect field `k₀`. The surjectivity of `π₁(V'₀) → π₁(V₀)` is then
`AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap_surjective_of_isIntegrallyClosed_stalk`,
giving `AlgebraicGeometry.WeilGroup.restrictionHom_surjective_of_isIntegrallyClosed_stalk`; the
regular case is `AlgebraicGeometry.WeilGroup.restrictionHom_surjective_of_isRegular`. The Weil
groups are those of `AlgebraicGeometry.Scheme.FiniteEtale.weilGroup`, built from the arithmetic
fundamental groups `π₁(V₀, s)`; the structure `AlgebraicGeometry.WeilGroup` itself is only set
up for curves. -/

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)}
  [GeometricallyConnected p] [ConnectedSpace C] {pU : U ⟶ Spec (.of K)}
  [GeometricallyConnected pU] [ConnectedSpace U] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]
  (hj : j ≫ p = pU) {sU : Spec (.of (AlgebraicClosure K)) ⟶ U}
  {sC : Spec (.of (AlgebraicClosure K)) ⟶ C} (τ : fiber (sU ≫ j) ≅ fiber sC)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]
  (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC] [CompactSpace GC]
  [∀ P, MulAction GC ((fiber sC).obj P)] [IsFundamentalGroup (fiber sC) GC]

omit [IsOpenImmersion j] [Nonempty U] in
/-- The restriction of Weil groups commutes with the degree maps (blueprint
`theorem-purity-real-sheaves-curves`, part (2)). -/
lemma weilGroupDeg_restrictionHom (w : weilGroup pU sU GU) :
    weilGroupDeg p sC GC (restrictionHom j hj τ GU GC w) = weilGroupDeg pU sU GU w :=
  rfl

omit [IsOpenImmersion j] [Nonempty U] in
/-- The restriction of Weil groups maps the geometric subgroup `ker deg` of `W(U₀)` onto that of
`W(C₀)` if it is surjective (e.g. for `C₀` regular or normal,
`AlgebraicGeometry.WeilGroup.restrictionHom_surjective_of_isRegular`,
`AlgebraicGeometry.WeilGroup.restrictionHom_surjective_of_isIntegrallyClosed_stalk`), since it
preserves degrees. On the underlying elements of `π₁(U₀)` it is the map of fundamental groups
`AlgebraicGeometry.WeilGroup.restrictionMap` (`AlgebraicGeometry.WeilGroup.restrictionHom_apply`),
so on the geometric subgroups it is the surjection of part (1) of
`theorem-purity-real-sheaves-curves`. -/
lemma map_ker_weilGroupDeg_restrictionHom
    (hsurj : Function.Surjective (restrictionHom j hj τ GU GC)) :
    (weilGroupDeg pU sU GU).ker.map (restrictionHom j hj τ GU GC) =
      (weilGroupDeg p sC GC).ker := by
  have h : weilGroupDeg pU sU GU = (weilGroupDeg p sC GC).comp (restrictionHom j hj τ GU GC) :=
    rfl
  rw [h, ← MonoidHom.comap_ker, Subgroup.map_comap_eq_self_of_surjective hsurj]

omit [IsOpenImmersion j] [Nonempty U] in
/-- **The restriction of Weil groups is surjective** if the map of fundamental groups is: an
element of degree `n` of `W(C₀)` differs from the image of an element of degree `n` of `W(U₀)`
by an element of the geometric subgroup, which lifts (blueprint
`theorem-purity-real-sheaves-curves`, part (2)). -/
lemma restrictionHom_surjective_of_surjective
    (hsurj : Function.Surjective (restrictionMap j τ GU GC)) :
    Function.Surjective (restrictionHom j hj τ GU GC) := by
  rintro ⟨⟨h, n⟩, hw⟩
  obtain ⟨γ, hγ⟩ := exists_mem_weilGroup_snd_eq_one pU sU GU
  let g₀ : weilGroup pU sU GU := ⟨(γ, Multiplicative.ofAdd 1), hγ⟩ ^ n.toAdd
  have hg₀ : (g₀ : GU × Multiplicative ℤ).2 = n := by
    rw [Subgroup.coe_zpow, Prod.pow_snd, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
  have hρg₀ := (restrictionHom j hj τ GU GC g₀).2
  rw [restrictionHom_apply, hg₀] at hρg₀
  have h' : (((restrictionMap j τ GU GC g₀.1.1)⁻¹ * h, 1) : GC × Multiplicative ℤ) ∈
      weilGroup p sC GC := by
    convert (weilGroup p sC GC).mul_mem ((weilGroup p sC GC).inv_mem hρg₀) hw using 1
    simp
  obtain ⟨g₁, hg₁⟩ := hsurj ((restrictionMap j τ GU GC g₀.1.1)⁻¹ * h)
  have hg₁W : (g₁, (1 : Multiplicative ℤ)) ∈ weilGroup pU sU GU :=
    (mem_weilGroup_fundamentalGroupMap_iff j hj sU τ GU GC _ _).2 (hg₁ ▸ h')
  refine ⟨g₀ * ⟨_, hg₁W⟩, Subtype.ext ?_⟩
  rw [restrictionHom_apply]
  simp only [Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul, map_mul, hg₁, hg₀, mul_one,
    mul_inv_cancel_left]

/-- **The restriction of Weil groups along a dense open of a regular scheme is surjective**
(blueprint `theorem-purity-real-sheaves-curves`, part (2), for `C₀` regular, e.g. smooth over
`K`): the map of fundamental groups is surjective
(`AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap_surjective_of_isRegular`). -/
lemma restrictionHom_surjective_of_isRegular [IsRegular C] [IsLocallyNoetherian C] :
    Function.Surjective (restrictionHom j hj τ GU GC) :=
  restrictionHom_surjective_of_surjective j hj τ GU GC
    (fundamentalGroupMap_surjective_of_isRegular j _ GU GC)

/-- **The restriction of Weil groups along a dense open of a normal scheme is surjective**
(blueprint `theorem-purity-real-sheaves-curves`, part (2)): if the local rings of the locally
noetherian scheme `C₀` are integrally closed domains, the map of fundamental groups is surjective
(`AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap_surjective_of_isIntegrallyClosed_stalk`).
-/
lemma restrictionHom_surjective_of_isIntegrallyClosed_stalk [IsLocallyNoetherian C]
    (hC : ∀ x : C, IsDomain (C.presheaf.stalk x) ∧ IsIntegrallyClosed (C.presheaf.stalk x)) :
    Function.Surjective (restrictionHom j hj τ GU GC) :=
  restrictionHom_surjective_of_surjective j hj τ GU GC
    (fundamentalGroupMap_surjective_of_isIntegrallyClosed_stalk j _ GU GC hC)

end RestrictionRegular

section Standard

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  [GeometricallyConnected p] (W : WeilGroup p)

/-- The Weil group `AlgebraicGeometry.WeilGroup.ofFundamentalGroup` built from the base point and
the fundamental group of a Weil group `W`. -/
noncomputable abbrev standard : WeilGroup p :=
  have := W.connectedSpace
  ofFundamentalGroup p W.basePoint W.fundamentalGroup

/-- **A Weil group is isomorphic, as a topological group, to the standard one** built from its
base point and fundamental group: the isomorphism is `weilGroupEquiv`, which is a homeomorphism
because both topologies make the geometric part open, with the topology induced from
`π₁(C₀, s)`. -/
noncomputable def toStandard : W.carrier ≃ₜ* W.standard.carrier where
  toMulEquiv := W.weilGroupEquiv
  continuous_toFun := by
    refine continuous_of_continuousAt_one W.weilGroupEquiv.toMonoidHom ?_
    refine ContinuousOn.continuousAt ?_ (W.isOpen_ker.mem_nhds W.geometric.one_mem)
    rw [continuousOn_iff_continuous_domRestrict]
    let ψ : W.geometric → W.standard.geometric := fun g ↦
      ⟨W.weilGroupEquiv g, (W.deg_eq g).symm.trans (MonoidHom.mem_ker.1 g.2)⟩
    have hψ : Continuous ψ :=
      W.standard.isEmbedding_ker.isInducing.continuous_iff.2 W.isEmbedding_ker.continuous
    exact continuous_subtype_val.comp hψ
  continuous_invFun := by
    refine continuous_of_continuousAt_one W.weilGroupEquiv.symm.toMonoidHom ?_
    refine ContinuousOn.continuousAt ?_
      (W.standard.isOpen_ker.mem_nhds W.standard.geometric.one_mem)
    rw [continuousOn_iff_continuous_domRestrict]
    let ψ : W.standard.geometric → W.geometric := fun g ↦
      ⟨W.weilGroupEquiv.symm g.1, by
        rw [MonoidHom.mem_ker, W.deg_eq, MulEquiv.apply_symm_apply]
        exact MonoidHom.mem_ker.1 g.2⟩
    have hψ : Continuous ψ := by
      refine W.isEmbedding_ker.isInducing.continuous_iff.2 ?_
      refine W.standard.isEmbedding_ker.continuous.congr fun g ↦ ?_
      simp only [Function.comp_apply, ψ, MulEquiv.apply_symm_apply]
      rfl
    exact continuous_subtype_val.comp hψ

lemma toStandard_apply (g : W.carrier) : (W.toStandard g : W.standard.carrier) =
    W.weilGroupEquiv g :=
  rfl

/-- The isomorphism with the standard Weil group carries each local Frobenius element to a
conjugate of the local Frobenius element of the standard Weil group. -/
lemma isConj_toStandard_frobenius (x : C.finitePoints) :
    IsConj (W.toStandard (W.frobenius x)) (W.standard.frobenius x) := by
  have := W.connectedSpace
  have : Finite (C.residueField x.1) := x.2
  obtain ⟨c, n, hcW, hc⟩ := (W.isFrobeniusElement_frobenius x).exists_mem_weilGroup_conj p
    W.basePoint W.fundamentalGroup (isFrobeniusElement_frobeniusElement W.basePoint
      W.fundamentalGroup x)
  refine isConj_iff.2 ⟨⟨(c, n), hcW⟩, Subtype.ext (Prod.ext hc ?_)⟩
  change n * (W.weilGroupEquiv (W.frobenius x)).1.2 * n⁻¹ =
    Multiplicative.ofAdd (p.degreeOver x.1 : ℤ)
  rw [mul_comm n, mul_assoc, mul_inv_cancel, mul_one]
  exact (W.deg_eq _).symm.trans (W.deg_frobenius x)

/-- Blueprint `definition-weil-representation--1`: Weil sheaves and their representations.

The local Frobenius `F_x` at a closed point `x` is well defined up to conjugacy in `W(C₀)`: every
Frobenius element `f` at `x` of `π₁(C₀, s)`, whatever path from a geometric point over `x` to the
base point it is transported along, is the image of an element of `W(C₀)` of degree `e_x`, and
that element is conjugate to `F_x` in `W(C₀)` (and not merely in `π₁(C₀, s)`). -/
theorem isConj_frobenius_of_isFrobeniusElement (x : C.finitePoints) {f : W.fundamentalGroup}
    (hf : haveI : Finite (C.residueField x.1) := x.2
      Scheme.FiniteEtale.IsFrobeniusElement W.basePoint W.fundamentalGroup x.1 f) :
    IsConj (W.frobenius x) (W.weilGroupEquiv.symm
      ⟨(f, Multiplicative.ofAdd (p.degreeOver x.1 : ℤ)),
        haveI : Finite (C.residueField x.1) := x.2
        hf.mem_weilGroup p⟩) := by
  have := W.connectedSpace
  have : Finite (C.residueField x.1) := x.2
  obtain ⟨c, n, hcW, hc⟩ := (W.isFrobeniusElement_frobenius x).exists_mem_weilGroup_conj p
    W.basePoint W.fundamentalGroup hf
  refine isConj_iff.2 ⟨W.weilGroupEquiv.symm ⟨(c, n), hcW⟩,
    W.weilGroupEquiv.injective (Subtype.ext (Prod.ext ?_ ?_))⟩
  · simpa using hc
  · simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
      Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv]
    rw [mul_comm n, mul_assoc, mul_inv_cancel, mul_one]
    exact (W.deg_eq _).symm.trans (W.deg_frobenius x)

end Standard

section OpenSubcurve

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j]

omit [Finite K] in
/-- An affine open of a curve is a curve. -/
lemma isCurve_comp_of_isAffine [IsAffine U] : IsCurve (j ≫ p) where
  krullDim_le_one :=
    j.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans (IsCurve.krullDim_le_one (f := p))

omit [Finite K] [IsCurve p] in
/-- A nonempty open of a smooth geometrically connected scheme over a field is geometrically
connected: it is geometrically irreducible. -/
lemma geometricallyConnected_comp [Nonempty U] [Smooth p] [GeometricallyConnected p] :
    GeometricallyConnected (j ≫ p) := by
  have : GeometricallyIrreducible p := .of_smooth_of_geometricallyConnected p
  have : Surjective (j ≫ p) := ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  infer_instance

end OpenSubcurve

end WeilGroup

end AlgebraicGeometry
