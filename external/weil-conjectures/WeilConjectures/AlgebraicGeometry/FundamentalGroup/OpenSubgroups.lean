/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems

/-!
# Galois covers and open subgroups of the fundamental group

Let `Y` be a connected scheme with a geometric point `s : Spec Ω ⟶ Y` and let `G` be a
fundamental group of the fibre functor `F_s` on finite étale `Y`-schemes (the étale fundamental
group `π₁(Y, s)`).

- `AlgebraicGeometry.Scheme.FiniteEtale.IsGaloisCover` (blueprint `def-galois-object`): a finite
  étale `P ⟶ Y` is a Galois cover if `P` is connected and `Aut_Y(P)` acts simply transitively on
  the geometric fibre `P_s`. These are the Galois objects of the Galois category `FÉt(Y)`
  (`AlgebraicGeometry.Scheme.FiniteEtale.isGaloisCover_iff_isGalois`).
- `AlgebraicGeometry.Scheme.FiniteEtale.galois_openSubgroups` (blueprint
  `lemma-cohomology-near-two-transverse-divisors--1`): the stabilizers of the points of the
  geometric fibres of connected finite étale covers are exactly the open subgroups of `G`; two
  connected covers are isomorphic if and only if their stabilizers are conjugate (and pointed covers
  are isomorphic if and only if the stabilizers of the points agree); the degree of a connected
  cover is the index of the stabilizer.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- Blueprint `def-galois-object`: Galois covers.

A finite étale `Y`-scheme `P` is a *Galois cover* (relative to the geometric point `s` of `Y`)
if `P` is connected and the group `Aut_Y(P)` of `Y`-automorphisms of `P` acts simply
transitively on the geometric fibre `P_s`: for every `x ∈ P_s` the evaluation `σ ↦ σ(x)` is a
bijection `Aut_Y(P) → P_s`. -/
def IsGaloisCover (P : Y.FiniteEtale) : Prop :=
  ConnectedSpace P.obj.left ∧
    ∀ x : (fiber s).obj P, Function.Bijective fun σ : Aut P ↦ (fiber s).map σ.asIso.hom x

/-- Over a connected base the Galois covers are the Galois objects of the Galois category of
finite étale `Y`-schemes. -/
theorem isGaloisCover_iff_isGalois [ConnectedSpace Y] (P : Y.FiniteEtale) :
    IsGaloisCover s P ↔ IsGalois P := by
  rw [isGalois_iff s P]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨isConnected_of_connectedSpace P, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  exact ⟨connectedSpace_of_isConnected P, h₂⟩

section OpenSubgroups

variable [ConnectedSpace Y] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

open scoped FintypeCatDiscrete

/-- The stabilizer of a point of a geometric fibre is an open subgroup of the fundamental
group, the action on the finite discrete fibre being continuous. -/
lemma isOpen_stabilizer (P : Y.FiniteEtale) (x : (fiber s).obj P) :
    IsOpen (MulAction.stabilizer G x : Set G) :=
  stabilizer_isOpen G x

/-- The stabilizer of a point of a geometric fibre, as an open subgroup. -/
def stabilizerOpenSubgroup (P : Y.FiniteEtale) (x : (fiber s).obj P) : OpenSubgroup G :=
  ⟨MulAction.stabilizer G x, isOpen_stabilizer s G P x⟩

/-- The degree of a connected finite étale cover is the index of the stabilizer of a point of
its geometric fibre. -/
lemma natCard_fiber_eq_index (P : Y.FiniteEtale) [IsConnected P] (x : (fiber s).obj P) :
    Nat.card ((fiber s).obj P) = (MulAction.stabilizer G x).index :=
  (MulAction.index_stabilizer_of_transitive G x).symm

/-- A finite étale `Y`-scheme with nonempty geometric fibre on which `G` acts transitively is
connected: a proper nonempty subobject would give a proper nonempty `G`-stable subset of the
fibre. -/
lemma isConnected_of_isPretransitive (P : Y.FiniteEtale) [Nonempty ((fiber s).obj P)]
    [MulAction.IsPretransitive G ((fiber s).obj P)] : IsConnected P := by
  by_contra hc
  have hni : IsInitial P → False := (not_initial_iff_fiber_nonempty (fiber s) P).2 inferInstance
  obtain ⟨Z, i, hZ, hm, hiso⟩ :=
    has_non_trivial_subobject_of_not_isConnected_of_not_initial P hc hni
  obtain ⟨z⟩ := (not_initial_iff_fiber_nonempty (fiber s) Z).1 hZ
  apply hiso
  have hinj : Function.Injective ((fiber s).map i) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback ((fiber s).map i)).1 inferInstance
  have : IsIso ((fiber s).map i) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, fun y ↦ ?_⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G ((fiber s).map i z) y
    exact ⟨g • z, by rw [IsNaturalSMul.naturality, hg]⟩
  exact isIso_of_reflects_iso i (fiber s)

/-- Every finite `G`-set with open stabilizers is, equivariantly, the geometric fibre of a finite
étale cover (`AlgebraicGeometry.Scheme.FiniteEtale.equivalenceContAction`). -/
lemma exists_fiber_equiv {X : Type u} [Finite X] [MulAction G X]
    (hX : ∀ x : X, IsOpen {g : G | g • x = x}) :
    ∃ (P : Y.FiniteEtale) (e : (fiber s).obj P ≃ X), ∀ (g : G) x, e (g • x) = g • e x := by
  classical
  have : Fintype X := Fintype.ofFinite X
  let XA : Action FintypeCat.{u} G := Action.FintypeCat.ofMulAction G (FintypeCat.of X)
  have hcont : XA.IsContinuous := by
    let : DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj XA) := ⟨rfl⟩
    exact AlgebraicGeometry.continuousSMul_of_isOpen_stabilizer G hX
  let XC : ContAction FintypeCat.{u} G := ⟨XA, hcont⟩
  let A := equivalenceContAction s G
  let iP : A.functor.obj (A.inverse.obj XC) ≅ XC := A.counitIso.app XC
  exact ⟨A.inverse.obj XC,
    FintypeCat.equivEquivIso.symm ((ObjectProperty.ι _ ⋙ Action.forget _ _).mapIso iP),
    fun g x ↦ ConcreteCategory.congr_hom (iP.hom.hom.comm g) x⟩

/-- Every open subgroup `H` of the fundamental group is the stabilizer of a point of the
geometric fibre of a connected finite étale cover, namely of the cover with fibre `G ⧸ H`. -/
theorem exists_isConnected_stabilizer_eq (H : OpenSubgroup G) :
    ∃ (P : Y.FiniteEtale) (x : (fiber s).obj P),
      IsConnected P ∧ MulAction.stabilizer G x = H := by
  have : Finite (G ⧸ H.toSubgroup) := H.toSubgroup.quotient_finite_of_isOpen H.isOpen'
  obtain ⟨P, e, he⟩ := exists_fiber_equiv s G (X := G ⧸ H.toSubgroup) fun q ↦ by
    induction q using QuotientGroup.induction_on with | H a
    have : {g : G | g • (a : G ⧸ H.toSubgroup) = a} = (fun g ↦ a⁻¹ * g * a) ⁻¹' H := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe]
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq, ← Subgroup.inv_mem_iff]
      group
      rfl
    rw [this]
    exact H.isOpen.preimage ((continuous_const_mul _).mul continuous_const)
  let x : (fiber s).obj P := e.symm (QuotientGroup.mk (1 : G))
  have : Nonempty ((fiber s).obj P) := ⟨x⟩
  have : MulAction.IsPretransitive G ((fiber s).obj P) := ⟨fun y z ↦ by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (e y) (e z)
    exact ⟨g, e.injective (by rw [he, hg])⟩⟩
  refine ⟨P, x, isConnected_of_isPretransitive s G P, ?_⟩
  ext g
  rw [MulAction.mem_stabilizer_iff, ← e.injective.eq_iff, he, Equiv.apply_symm_apply,
    ← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G] in
/-- Two transitive `G`-sets with points of equal stabilizers are equivariantly isomorphic, by an
isomorphism matching the points. -/
lemma exists_equiv_of_stabilizer_eq {X Z : Type*} [MulAction G X] [MulAction G Z]
    [MulAction.IsPretransitive G X] [MulAction.IsPretransitive G Z] (x : X) (z : Z)
    (h : MulAction.stabilizer G x = MulAction.stabilizer G z) :
    ∃ e : X ≃ Z, e x = z ∧ ∀ (g : G) (x' : X), e (g • x') = g • e x' := by
  let oX : X ≃ MulAction.orbit G x :=
    (Equiv.Set.univ X).symm.trans (Set.equivOfEq (MulAction.orbit_eq_univ G x).symm)
  let oZ : Z ≃ MulAction.orbit G z :=
    (Equiv.Set.univ Z).symm.trans (Set.equivOfEq (MulAction.orbit_eq_univ G z).symm)
  let e : X ≃ Z := oX.trans ((MulAction.orbitEquivQuotientStabilizer G x).trans
    ((Subgroup.quotientEquivOfEq h).trans
      ((MulAction.orbitEquivQuotientStabilizer G z).symm.trans oZ.symm)))
  have key (g : G) : e (g • x) = g • z := by
    have h1 : MulAction.orbitEquivQuotientStabilizer G x (oX (g • x)) = (g : G ⧸ _) := by
      rw [← Equiv.eq_symm_apply]
      ext
      simp [oX, MulAction.orbitEquivQuotientStabilizer_symm_apply]
    simp only [e, Equiv.trans_apply, h1, Subgroup.quotientEquivOfEq_mk]
    simp [oZ, MulAction.orbitEquivQuotientStabilizer_symm_apply]
  refine ⟨e, by simpa using key 1, fun g x' ↦ ?_⟩
  obtain ⟨g', rfl⟩ := MulAction.exists_smul_eq G x x'
  rw [smul_smul, key, key, mul_smul]

/-- **Pointed connected covers are classified by stabilizers.** Two connected finite étale
covers with points `x ∈ P_s`, `y ∈ Q_s` are isomorphic by an isomorphism sending `x` to `y` if
and only if `x` and `y` have the same stabilizer in the fundamental group. -/
theorem exists_iso_fiber_map_eq_iff (P Q : Y.FiniteEtale) [IsConnected P] [IsConnected Q]
    (x : (fiber s).obj P) (y : (fiber s).obj Q) :
    (∃ f : P ≅ Q, (fiber s).map f.hom x = y) ↔
      MulAction.stabilizer G x = MulAction.stabilizer G y := by
  constructor
  · rintro ⟨f, rfl⟩
    ext g
    simp only [MulAction.mem_stabilizer_iff]
    rw [← IsNaturalSMul.naturality]
    exact ((ConcreteCategory.bijective_of_isIso ((fiber s).map f.hom)).1.eq_iff).symm
  · intro h
    obtain ⟨e, hex, he⟩ := exists_equiv_of_stabilizer_eq G x y h
    let A := equivalenceContAction s G
    let i : (A.functor.obj P).obj ≅ (A.functor.obj Q).obj :=
      Action.mkIso (FintypeCat.equivEquivIso e) fun g ↦ by
        ext x'
        change e (((A.functor.obj P).obj.ρ g).asHom.hom x') =
          ((A.functor.obj Q).obj.ρ g).asHom.hom (e x')
        rw [equivalenceContAction_functor_obj_obj_ρ_apply,
          equivalenceContAction_functor_obj_obj_ρ_apply]
        exact he g x'
    let f : P ≅ Q := A.fullyFaithfulFunctor.preimageIso
      ((ObjectProperty.fullyFaithfulι _).preimageIso i)
    refine ⟨f, ?_⟩
    have hf : (A.functor.map f.hom).hom.hom = (fiber s).map f.hom :=
      equivalenceContAction_functor_map_hom_hom s G f.hom
    rw [← hf]
    simp only [f, Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
    exact hex

/-- **Connected covers up to isomorphism are classified by conjugacy classes of stabilizers.**
Two connected finite étale covers `P`, `Q` with points `x ∈ P_s`, `y ∈ Q_s` are isomorphic if and
only if the stabilizer of `x` is conjugate to that of `y`, i.e. equal to the stabilizer of some
`g • y`. -/
theorem nonempty_iso_iff (P Q : Y.FiniteEtale) [IsConnected P] [IsConnected Q]
    (x : (fiber s).obj P) (y : (fiber s).obj Q) :
    Nonempty (P ≅ Q) ↔
      ∃ g : G, MulAction.stabilizer G x = MulAction.stabilizer G (g • y) := by
  constructor
  · rintro ⟨f⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G y ((fiber s).map f.hom x)
    exact ⟨g, hg ▸ (exists_iso_fiber_map_eq_iff s G P Q x _).1 ⟨f, rfl⟩⟩
  · rintro ⟨g, hg⟩
    exact ⟨((exists_iso_fiber_map_eq_iff s G P Q x (g • y)).2 hg).choose⟩

/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1`: Open subgroups and finite etale
covers.

Let `Y` be connected with geometric point `s`, and `G` the fundamental group `π₁(Y, s)` (any
fundamental group of the fibre functor `F_s`). Assigning to a connected finite étale cover `P`
the stabilizer in `G` of a point of `P_s` is a bijection between isomorphism classes of connected
finite étale covers and open subgroups of `G` up to conjugacy, and the degree `#P_s` of `P` is
the index of the subgroup:

1. every stabilizer is open, and every open subgroup is a stabilizer;
2. two connected covers are isomorphic if and only if the stabilizers of points of their fibres
   are conjugate (for pointed covers: if and only if the stabilizers agree,
   `AlgebraicGeometry.Scheme.FiniteEtale.exists_iso_fiber_map_eq_iff`);
3. the degree is the index of the stabilizer.

The blueprint states the bijection with open subgroups; the stabilizer of a point is only
well-defined up to conjugacy (changing the point conjugates it), which is the form stated in (2).
-/
theorem galois_openSubgroups :
    (∀ (P : Y.FiniteEtale) (x : (fiber s).obj P), IsOpen (MulAction.stabilizer G x : Set G)) ∧
    (∀ H : OpenSubgroup G, ∃ (P : Y.FiniteEtale) (x : (fiber s).obj P),
      IsConnected P ∧ MulAction.stabilizer G x = H) ∧
    (∀ (P Q : Y.FiniteEtale) [IsConnected P] [IsConnected Q] (x : (fiber s).obj P)
      (y : (fiber s).obj Q), Nonempty (P ≅ Q) ↔
        ∃ g : G, MulAction.stabilizer G x = MulAction.stabilizer G (g • y)) ∧
    ∀ (P : Y.FiniteEtale) [IsConnected P] (x : (fiber s).obj P),
      Nat.card ((fiber s).obj P) = (MulAction.stabilizer G x).index :=
  ⟨isOpen_stabilizer s G, exists_isConnected_stabilizer_eq s G,
    fun P Q _ _ x y ↦ nonempty_iso_iff s G P Q x y, fun P _ x ↦ natCard_fiber_eq_index s G P x⟩

end OpenSubgroups

end AlgebraicGeometry.Scheme.FiniteEtale
