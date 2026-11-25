/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.BoundaryNeighbourhood
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ExtendOverInertia
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusDecomposition
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroupDense
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryConstruction
public import WeilConjectures.Mathlib.RingTheory.Ideal.Pointwise

/-!
# Decomposition and inertia groups at the boundary points of an open subcurve

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over a finite
field, `U₀` geometrically connected, and `z` a boundary point. Fix a separable closure `Ω` of
the function field `k(C)`, so that `Spec Ω ⟶ U₀` is a geometric generic point, and a path from it
to the base point of `π₁(U₀)`; this gives `ρ : Gal(Ω / k(C)) → π₁(U₀)`.

An affine chart `W ∋ z` of `U₀ ∪ {z}` on which `z` is cut out by one section
(`AlgebraicGeometry.WeilGroup.BoundaryChart`) and a maximal ideal `Q` over `z` of the integral
closure `B` of `Γ(C, W)` in `Ω` are a compatible system of points over `z` on the normalizations
of `C₀` in the covers of `U₀`. The decomposition group `D_z` is the stabiliser of `Q`, the inertia
group `I_z` the subgroup acting trivially on `B ⧸ Q`, and `D_z / I_z` is the automorphism group of
`(B ⧸ Q) / κ(z)` (`Ideal.Quotient.stabilizerQuotientInertiaEquivIntegralClosure`), `B ⧸ Q` being an
algebraic closure of `κ(z)`.

The image of `I_z` in `π₁(U₀)` (`AlgebraicGeometry.WeilGroup.inertiaGroup`) is the inertia group at
`z`:

- it acts trivially on the covers extending over `z`
  (`AlgebraicGeometry.WeilGroup.inertiaGroup_le_localKernel`);
- conversely the kernel of `π₁(U₀) → π₁(U₀ ∪ {z})` is the closed normal subgroup it generates
  (`AlgebraicGeometry.WeilGroup.localKernel_le_topologicalClosure_normalClosure`), since a cover on
  which `I_z` acts trivially extends over `z`.

A lift in `D_z` of the inverse arithmetic Frobenius of `κ(z)` restricts to a Frobenius element at
`z` in `π₁(C₀)`
(`BoundaryChart.exists_mem_stabilizer_isFrobeniusElement_restrictionMap`).
Together with the density of the Weil group in `π₁(U₀)`, this builds the boundary datum of
`lemma-boundary-stalk--1` (`AlgebraicGeometry.WeilGroup.boundaryDatum`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory
open scoped Pointwise

namespace AlgebraicGeometry.WeilGroup

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  [GeometricallyConnected p] [ConnectedSpace C] [Smooth p] {pU : U ⟶ Spec (.of K)} [IsCurve pU]
  [GeometricallyConnected pU] [ConnectedSpace U] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]

section Chart

open scoped Classical in
/-- The open `U₀ ∪ {z}` of `C₀`, for a boundary point `z`. -/
noncomputable abbrev boundaryOpen (z : C) : C.Opens :=
  complOpens (boundaryFinset (p := p) j) (isClosed_of_mem_boundaryFinset j) {z}

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma mem_boundaryOpen_iff {z x : C} :
    x ∈ boundaryOpen (p := p) j z ↔ x ∈ Set.range j.base ∨ x = z := by
  classical
  rw [mem_complOpens, ← Finset.mem_coe, coe_boundaryFinset, Finset.mem_singleton,
    Set.mem_compl_iff, not_not]

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma opensRange_le_boundaryOpen (z : C) : j.opensRange ≤ boundaryOpen (p := p) j z :=
  fun _ hx ↦ (mem_boundaryOpen_iff j).2 (Or.inl hx)

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma connectedSpace_boundaryOpen (z : C) : ConnectedSpace (boundaryOpen (p := p) j z) := by
  have := irreducibleSpace_of_smooth (p := p)
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  have hne : ((boundaryOpen (p := p) j z : C.Opens) : Set C).Nonempty :=
    ⟨j u, opensRange_le_boundaryOpen j z ⟨u, rfl⟩⟩
  have hirr : IsIrreducible ((boundaryOpen (p := p) j z : C.Opens) : Set C) :=
    ⟨hne, (IrreducibleSpace.isIrreducible_univ C).isPreirreducible.open_subset
      (boundaryOpen (p := p) j z).isOpen (Set.subset_univ _)⟩
  exact isConnected_iff_connectedSpace.1 hirr.isConnected

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma toBoundaryOpen_eq (z : C) :
    toBoundaryOpen (p := p) j z = toOpen j (boundaryOpen (p := p) j z)
      (opensRange_le_boundaryOpen j z) :=
  rfl

variable (p) in
/-- An affine chart at a boundary point `z`: an affine open `W ∋ z` of `U₀ ∪ {z}` on which `z` is
the zero locus of a single section `ϖ`, i.e. `W ∖ {z} = D(ϖ)`. -/
structure BoundaryChart (z : C) where
  /-- The affine open. -/
  W : C.Opens
  isAffineOpen : IsAffineOpen W
  mem : z ∈ W
  le : W ≤ boundaryOpen (p := p) j z
  /-- The section cutting out `z`. -/
  ϖ : Γ(C, W)
  mem_basicOpen_iff : ∀ x ∈ W, x ∈ C.basicOpen ϖ ↔ x ≠ z

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma nonempty_boundaryChart [SmoothOfRelativeDimension 1 p] [IsIntegral C] {z : C}
    (hz : z ∈ (Set.range j.base)ᶜ) : Nonempty (BoundaryChart p j z) := by
  have hzS : z ∈ boundaryFinset (p := p) j := by
    rw [← Finset.mem_coe, coe_boundaryFinset]
    exact hz
  obtain ⟨W, hW, hzW, ϖ, hle, h⟩ := exists_isAffineOpen_basicOpen_eq p
    (isClosed_of_mem_boundaryFinset j z hzS) (boundaryOpen (p := p) j z)
    ((mem_boundaryOpen_iff j).2 (Or.inr rfl))
  exact ⟨⟨W, hW, hzW, hle, ϖ, h⟩⟩

namespace BoundaryChart

variable {j} {z : C} (c : BoundaryChart p j z)

instance : Nonempty c.W := ⟨⟨z, c.mem⟩⟩

/-- The prime ideal of `Γ(C, W)` at `z`. -/
noncomputable abbrev ideal : Ideal Γ(C, c.W) := (c.isAffineOpen.primeIdealOf ⟨z, c.mem⟩).asIdeal

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma ϖ_mem : c.ϖ ∈ c.ideal := by
  by_contra h
  exact ((c.mem_basicOpen_iff z c.mem).1
    ((IsAffineOpen.mem_basicOpen_iff c.isAffineOpen ⟨z, c.mem⟩ c.ϖ).2 h)) rfl

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
/-- `z` is the only zero of `ϖ` on `W`. -/
lemma eq_ideal (P : Ideal Γ(C, c.W)) (hP : P.IsPrime) (hϖ : c.ϖ ∈ P) : P = c.ideal := by
  have hU := c.isAffineOpen
  let q : Spec Γ(C, c.W) := ⟨P, hP⟩
  have hqW : hU.fromSpec q ∈ c.W := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨q, rfl⟩
  let x : c.W := ⟨_, hqW⟩
  have hx : hU.primeIdealOf x = q :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf x)
  have hxz : x = ⟨z, c.mem⟩ := by
    refine Subtype.ext (not_not.1 fun hne ↦ ?_)
    have := (c.mem_basicOpen_iff x x.2).2 hne
    rw [IsAffineOpen.mem_basicOpen_iff hU x, hx] at this
    exact this hϖ
  calc P = (hU.primeIdealOf x).asIdeal := by rw [hx]
    _ = c.ideal := by rw [hxz]

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma isMaximal_ideal : c.ideal.IsMaximal := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal c.ideal Ideal.IsPrime.ne_top'
  rwa [c.eq_ideal M hM.isPrime (hle c.ϖ_mem)] at hM

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma finite_quotient [Finite (C.residueField z)] : Finite (Γ(C, c.W) ⧸ c.ideal) := by
  have := c.isMaximal_ideal
  let z' : c.W := ⟨z, c.mem⟩
  let _ : Algebra Γ(C, c.W) (C.presheaf.stalk z') := TopCat.Presheaf.algebra_section_stalk _ z'
  have := c.isAffineOpen.isLocalization_stalk z'
  let e : Γ(C, c.W) ⧸ c.ideal ≃+* C.residueField z :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal c.ideal (C.presheaf.stalk z')).toRingEquiv
  exact Finite.of_equiv _ e.symm.toEquiv

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma opensRange_inf (hz : z ∉ Set.range j.base) : j.opensRange ⊓ c.W = C.basicOpen c.ϖ := by
  apply le_antisymm
  · rintro x ⟨hxj, hxW⟩
    exact (c.mem_basicOpen_iff x hxW).2 (by rintro rfl; exact hz hxj)
  · intro x hx
    have hxW : x ∈ c.W := C.basicOpen_le c.ϖ hx
    refine ⟨?_, hxW⟩
    rcases (mem_boundaryOpen_iff j).1 (c.le hxW) with h | h
    · exact h
    · exact absurd h ((c.mem_basicOpen_iff x hxW).1 hx)

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma boundaryOpen_le : boundaryOpen (p := p) j z ≤ j.opensRange ⊔ c.W := by
  intro x hx
  rcases (mem_boundaryOpen_iff j).1 hx with h | rfl
  · exact Or.inl h
  · exact Or.inr c.mem

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma ϖ_ne_zero (hz : z ∉ Set.range j.base) : c.ϖ ≠ 0 := by
  have := irreducibleSpace_of_smooth (p := p)
  intro h0
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  obtain ⟨x, hxj, hxW⟩ := nonempty_preirreducible_inter j.opensRange.isOpen c.W.isOpen
    ⟨j u, u, rfl⟩ ⟨z, c.mem⟩
  have : x ∈ C.basicOpen c.ϖ := by
    rw [← c.opensRange_inf hz]
    exact ⟨hxj, hxW⟩
  rw [h0, Scheme.basicOpen_zero] at this
  exact this

end BoundaryChart

end Chart

variable [IsIntegral C]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

namespace BoundaryChart

variable {j} {z : C} (c : BoundaryChart p j z)

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] [IsCurve pU]
  [GeometricallyConnected pU] in
lemma exists_isMaximal_liesOver :
    ∃ Q : Ideal (integralClosure Γ(C, c.W) Ω), Q.IsMaximal ∧ Q.LiesOver c.ideal := by
  have := c.isMaximal_ideal
  have : IsFractionRing Γ(C, c.W) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C c.W c.isAffineOpen
  have : FaithfulSMul Γ(C, c.W) (integralClosure Γ(C, c.W) Ω) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h ↦ ?_
    have h' : algebraMap Γ(C, c.W) Ω a = algebraMap Γ(C, c.W) Ω b := congrArg Subtype.val h
    rw [IsScalarTower.algebraMap_apply Γ(C, c.W) C.functionField Ω,
      IsScalarTower.algebraMap_apply Γ(C, c.W) C.functionField Ω b] at h'
    exact IsFractionRing.injective Γ(C, c.W) C.functionField ((algebraMap _ Ω).injective h')
  have : Algebra.IsIntegral Γ(C, c.W) (integralClosure Γ(C, c.W) Ω) :=
    integralClosure.AlgebraIsIntegral
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := integralClosure Γ(C, c.W) Ω)
    c.ideal

/-- A maximal ideal over `z` of the integral closure of `Γ(C, W)` in the separable closure of the
function field: a geometric point over the local field at `z`. -/
noncomputable def point : Ideal (integralClosure Γ(C, c.W) Ω) :=
  c.exists_isMaximal_liesOver.choose

instance : c.point.IsMaximal := c.exists_isMaximal_liesOver.choose_spec.1

instance : c.point.LiesOver c.ideal := c.exists_isMaximal_liesOver.choose_spec.2

end BoundaryChart

variable (sU : Spec (.of (AlgebraicClosure K)) ⟶ U)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]

/-- A path from the generic geometric point `Spec Ω ⟶ U₀` to the base point `s_U`. -/
noncomputable def genericPath : fiber (pointOfAlgebra Ω (genericPointLift j)) ≅ fiber sU :=
  (nonempty_iso_of_fiberFunctor _ _).some

/-- The map `Gal(Ω / k(C)) → π₁(U₀, s_U)` of the generic point. -/
noncomputable def genericGaloisMap : Gal(Ω/C.functionField) →* GU :=
  galoisToFundamentalGroup (genericPointLift j) (genericPath j sU) GU

section Groups

variable {j} {z : C} (c : BoundaryChart p j z)

-- instance search through `SeparableClosure` and its integral closures is slow
/-- The decomposition group in `π₁(U₀)` of a point `Q` over the boundary point `z`: the image of
the stabiliser of `Q`. -/
noncomputable def decompositionGroup (Q : Ideal (integralClosure Γ(C, c.W) Ω)) : Subgroup GU :=
  (MulAction.stabilizer Gal(Ω/C.functionField) Q).map (genericGaloisMap j sU GU)

/-- The inertia group in `π₁(U₀)` of a point `Q` over the boundary point `z`: the image of the
subgroup of `Gal(Ω / k(C))` acting trivially on the residue field of `Q`. -/
noncomputable def inertiaGroup (Q : Ideal (integralClosure Γ(C, c.W) Ω)) : Subgroup GU :=
  (Q.inertia Gal(Ω/C.functionField)).map (genericGaloisMap j sU GU)

omit [Finite K] [GeometricallyConnected p] [IsCurve pU] [GeometricallyConnected pU] in
lemma inertiaGroup_le_decompositionGroup (Q : Ideal (integralClosure Γ(C, c.W) Ω)) :
    inertiaGroup sU GU c Q ≤ decompositionGroup sU GU c Q :=
  Subgroup.map_mono (Ideal.inertia_le_stabilizer Q)

omit [Finite K] [GeometricallyConnected p] [IsCurve pU] [GeometricallyConnected pU] in
/-- **Inertia acts trivially on the covers extending over `z`**: the inertia group lies in the
kernel of `π₁(U₀) → π₁(U₀ ∪ {z})`. -/
theorem inertiaGroup_le_localKernel (Q : Ideal (integralClosure Γ(C, c.W) Ω)) [Q.IsMaximal] :
    inertiaGroup sU GU c Q ≤ localKernel (p := p) j sU GU z := by
  have := connectedSpace_boundaryOpen (p := p) j z
  rintro _ ⟨σ, hσ, rfl⟩ P x
  obtain ⟨t, rfl⟩ : ∃ t, (genericPath j sU).hom.app _ t = x :=
    ⟨(genericPath j sU).inv.app _ x,
      ConcreteCategory.congr_hom ((genericPath j sU).inv_hom_id_app _) x⟩
  rw [genericGaloisMap, galoisToFundamentalGroup_smul]
  congr 1
  exact galoisToAut_hom_app_pullback_eq_of_mem_inertia j c.isAffineOpen Q
    (boundaryOpen (p := p) j z) (opensRange_le_boundaryOpen j z) c.le hσ P t

omit [Finite K] [GeometricallyConnected p] [IsCurve pU] [GeometricallyConnected pU] in
/-- **Covers on which inertia acts trivially extend over `z`**: the kernel of
`π₁(U₀) → π₁(U₀ ∪ {z})` is the closed normal subgroup generated by the inertia group. -/
theorem localKernel_le_topologicalClosure_normalClosure (hz : z ∉ Set.range j.base)
    [Finite (C.residueField z)] (Q : Ideal (integralClosure Γ(C, c.W) Ω)) [Q.IsMaximal]
    [Q.LiesOver c.ideal] :
    localKernel (p := p) j sU GU z ≤
      (Subgroup.normalClosure (inertiaGroup sU GU c Q : Set GU)).topologicalClosure := by
  have := c.isMaximal_ideal
  have := c.finite_quotient
  have := isDedekindDomain_of_isAffineOpen p c.isAffineOpen
  have := connectedSpace_boundaryOpen (p := p) j z
  intro g hg
  set N := (Subgroup.normalClosure (inertiaGroup sU GU c Q : Set GU)).topologicalClosure
  have hNc : IsClosed (N : Set GU) := Subgroup.isClosed_topologicalClosure _
  have hNn : N.Normal := Subgroup.is_normal_topologicalClosure _
  refine mem_of_forall_smul_eq_self sU GU N hNc g fun Y u hu ↦ ?_
  obtain ⟨Z, i, y, rfl, hZ, hi⟩ := fiber_in_connected_component (fiber sU) Y u
  -- `N` acts trivially on the fibre of the connected cover `Z`
  have hinj : Function.Injective ((fiber sU).map i) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback ((fiber sU).map i)
  have hNy (k : GU) (hk : k ∈ N) : k • y = y :=
    hinj (by rw [IsNaturalSMul.naturality, hu k hk])
  have hNZ (k : GU) (hk : k ∈ N) (x : (fiber sU).obj Z) : k • x = x := by
    obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq GU y x
    have : h⁻¹ * k * h ∈ N := by simpa using hNn.conj_mem k hk h⁻¹
    rw [← mul_smul, show k * h = h * (h⁻¹ * k * h) by group, mul_smul, hNy _ this]
  -- so inertia acts trivially on the generic fibre of `Z`
  have hIZ : ∀ σ ∈ Q.inertia Gal(Ω/C.functionField),
      ∀ t : (fiber (pointOfAlgebra Ω (genericPointLift j))).obj Z,
        (galoisToAut (genericPointLift j) σ).asIso.hom.app Z t = t := by
    intro σ hσ t
    apply ((ConcreteCategory.isIso_iff_bijective ((genericPath j sU).hom.app Z)).1
      inferInstance).1
    rw [← galoisToFundamentalGroup_smul (genericPointLift j) (genericPath j sU) GU σ Z t]
    exact hNZ _ (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨σ, hσ, rfl⟩)) _
  -- `Z` is integral, being connected and smooth over `K`
  have : ConnectedSpace Z.obj.left := connectedSpace_of_isConnected Z
  have : Etale Z.obj.hom := Z.obj.prop
  let q : Z.obj.left ⟶ Spec (.of K) := Z.obj.hom ≫ j ≫ p
  have : Smooth q := inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian q
  have := IsRegular.of_smooth q
  have : IsIntegral Z.obj.left := IsRegular.isIntegral _
  have := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨Z', ⟨e⟩⟩ := exists_pullback_toOpen_iso_of_forall_inertia j c.isAffineOpen c.ϖ
    (c.ϖ_ne_zero hz) (c.opensRange_inf hz) c.ideal c.eq_ideal Q (boundaryOpen (p := p) j z)
    (opensRange_le_boundaryOpen j z) c.le Z c.boundaryOpen_le hIZ
  -- `g` acts trivially on the fibre of `Z`, which extends over `z`
  rw [← IsNaturalSMul.naturality, smul_eq_self_of_iso sU GU e (hg Z')]

variable {sC : Spec (.of (AlgebraicClosure K)) ⟶ C} (τ : fiber (sU ≫ j) ≅ fiber sC)
  (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC] [CompactSpace GC]
  [∀ P, MulAction GC ((fiber sC).obj P)] [IsFundamentalGroup (fiber sC) GC]

omit [Finite K] [GeometricallyConnected p] [ConnectedSpace U] in
lemma BoundaryChart.pointOfAlgebra_genericPointLift_comp :
    pointOfAlgebra Ω (genericPointLift j) ≫ j = pointOfAlgebra Ω (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(C, c.W) C.functionField)) ≫ c.isAffineOpen.fromSpec) := by
  rw [Category.assoc, genericPointLift_comp, c.isAffineOpen.fromSpecFunctionField_eq]
  rfl

/-- The generic geometric point of `U₀`, mapped to `C₀`, is the generic geometric point through
the chart `W`. -/
noncomputable def BoundaryChart.genericFiberIso :
    fiber (pointOfAlgebra Ω (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(C, c.W) C.functionField)) ≫ c.isAffineOpen.fromSpec)) ≅
      fiber (pointOfAlgebra Ω (genericPointLift j) ≫ j) :=
  fiberIsoOfIso (Iso.refl _) (by rw [Iso.refl_hom, Category.id_comp,
    c.pointOfAlgebra_genericPointLift_comp])

/-- The path from the generic geometric point, seen through the chart `W`, to `s_C`: the image
under `j` of the generic path of `U₀`. -/
noncomputable def BoundaryChart.path : fiber (pointOfAlgebra Ω (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(C, c.W) C.functionField)) ≫ c.isAffineOpen.fromSpec)) ≅ fiber sC :=
  c.genericFiberIso ≪≫ (pullbackFiberIso j (pointOfAlgebra Ω (genericPointLift j))).symm ≪≫
    Functor.isoWhiskerLeft (Scheme.FiniteEtale.pullback j) (genericPath j sU) ≪≫
    (pullbackFiberIso j sU ≪≫ τ)

omit [Finite K] [GeometricallyConnected p] in
/-- The map `Gal(Ω / k(C)) → π₁(U₀) → π₁(C₀)` is the map of the generic point of `C₀`. -/
lemma BoundaryChart.restrictionMap_genericGaloisMap (σ : Gal(Ω/C.functionField)) :
    restrictionMap j τ GU GC (genericGaloisMap j sU GU σ) =
      galoisToFundamentalGroup _ (c.path sU τ) GC σ := by
  have h1 (P : C.FiniteEtale) (t) : (c.path sU τ).hom.app P t =
      (pullbackFiberIso j sU ≪≫ τ).hom.app P ((genericPath j sU).hom.app _
        ((pullbackFiberIso j (pointOfAlgebra Ω (genericPointLift j))).inv.app P
          (c.genericFiberIso.hom.app P t))) := rfl
  have key (P : C.FiniteEtale) (y : (fiber sC).obj P) :
      restrictionMap j τ GU GC (genericGaloisMap j sU GU σ) • y =
        galoisToFundamentalGroup _ (c.path sU τ) GC σ • y := by
    obtain ⟨t, rfl⟩ : ∃ t, (c.path sU τ).hom.app P t = y :=
      ⟨(c.path sU τ).inv.app P y, ConcreteCategory.congr_hom ((c.path sU τ).inv_hom_id_app P) y⟩
    rw [galoisToFundamentalGroup_smul, h1, h1, restrictionMap, fundamentalGroupMap_smul,
      genericGaloisMap, galoisToFundamentalGroup_smul]
    congr 2
    apply ((ConcreteCategory.isIso_iff_bijective
      ((pullbackFiberIso j (pointOfAlgebra Ω (genericPointLift j))).hom.app P)).1 inferInstance).1
    rw [← ConcreteCategory.comp_apply ((pullbackFiberIso j _).inv.app P)
      ((pullbackFiberIso j _).hom.app P), Iso.inv_hom_id_app]
    have h2 : ((pullbackFiberIso j (pointOfAlgebra Ω (genericPointLift j))).inv.app P
        (c.genericFiberIso.hom.app P t)).left ≫ Limits.pullback.fst P.obj.hom j =
          (c.genericFiberIso.hom.app P t).left :=
      congrArg Over.Hom.left (ConcreteCategory.congr_hom
        ((pullbackFiberIso j (pointOfAlgebra Ω (genericPointLift j))).inv_hom_id_app P)
        (c.genericFiberIso.hom.app P t))
    apply fiber_ext
    change (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
      ((pullbackFiberIso j (pointOfAlgebra Ω (genericPointLift j))).inv.app P
        (c.genericFiberIso.hom.app P t)).left) ≫ Limits.pullback.fst P.obj.hom j =
          (Iso.refl _).hom ≫ Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ t.left
    refine (Category.assoc _ _ _).trans
      ((congrArg (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ ·) h2).trans ?_)
    simp only [BoundaryChart.genericFiberIso, fiberIsoOfIso_hom_app_left, Iso.refl_hom,
      Category.id_comp]
  rw [← mul_inv_eq_one]
  refine IsFundamentalGroup.non_trivial (F := fiber sC) _ fun P y ↦ ?_
  rw [mul_smul, key, smul_inv_smul]

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through `SeparableClosure` and its integral closures is slow
omit [Finite K] [GeometricallyConnected p] [IsCurve pU] [GeometricallyConnected pU] in
/-- **Frobenius lifts in the decomposition group.** Some element of the decomposition group of `Q`
restricts to a Frobenius element at `z` in `π₁(C₀)`: one inducing the inverse of the arithmetic
Frobenius on the residue field of `Q`, an algebraic closure of `κ(z)`. -/
theorem BoundaryChart.exists_mem_stabilizer_isFrobeniusElement_restrictionMap
    [Finite (C.residueField z)] (Q : Ideal (integralClosure Γ(C, c.W) Ω)) [Q.IsMaximal]
    [Q.LiesOver c.ideal] :
    ∃ σ ∈ MulAction.stabilizer Gal(Ω/C.functionField) Q,
      IsFrobeniusElement sC GC z (restrictionMap j τ GU GC (genericGaloisMap j sU GU σ)) := by
  have := c.isMaximal_ideal
  have := isDedekindDomain_of_isAffineOpen p c.isAffineOpen
  obtain ⟨σ, hσ, hF⟩ := exists_mem_stabilizer_isFrobeniusElement c.isAffineOpen z c.mem Q GC
    (c.path sU τ)
  exact ⟨σ, hσ, by
    rw [c.restrictionMap_genericGaloisMap (sU := sU) (GU := GU) (τ := τ) (GC := GC)]; exact hF⟩

end Groups

section Datum

variable [SmoothOfRelativeDimension 1 p] (hj : j ≫ p = pU)
  {sC : Spec (.of (AlgebraicClosure K)) ⟶ C} (τ : fiber (sU ≫ j) ≅ fiber sC)
  (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC] [CompactSpace GC]
  [∀ P, MulAction GC ((fiber sC).obj P)] [IsFundamentalGroup (fiber sC) GC]

/-- The chosen affine chart at a boundary point. -/
noncomputable def boundaryChart (z : ↥((Set.range j.base)ᶜ)) : BoundaryChart p j z.1 :=
  (nonempty_boundaryChart (p := p) j z.2).some

/-- The inertia group at a boundary point `z`, as a subgroup of the geometric part of `W(U₀)`:
the elements whose image in `π₁(U₀)` lies in the inertia group of the chosen point over `z`. -/
noncomputable def boundaryInertia (z : ↥((Set.range j.base)ᶜ)) :
    Subgroup (weilGroup pU sU GU) :=
  (inertiaGroup sU GU (boundaryChart (p := p) j z) (boundaryChart (p := p) j z).point).comap
    ((MonoidHom.fst _ _).comp (weilGroup pU sU GU).subtype) ⊓ (weilGroupDeg pU sU GU).ker

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through `SeparableClosure` and its integral closures is slow
omit [GeometricallyConnected p] in
lemma exists_boundaryFrobeniusLift (z : ↥((Set.range j.base)ᶜ)) :
    have : Finite (C.residueField z.1) := boundary_subset_finitePoints (p := p) j z.2
    ∃ σ ∈ MulAction.stabilizer Gal(Ω/C.functionField) (boundaryChart (p := p) j z).point,
      IsFrobeniusElement sC GC z.1 (restrictionMap j τ GU GC (genericGaloisMap j sU GU σ)) :=
  have : Finite (C.residueField z.1) := boundary_subset_finitePoints (p := p) j z.2
  (boundaryChart (p := p) j z).exists_mem_stabilizer_isFrobeniusElement_restrictionMap sU GU τ GC _

/-- The residue Frobenius lift at a boundary point `z`, in `Gal(Ω / k(C))`: an element of the
decomposition group of the chosen point over `z` inducing the inverse arithmetic Frobenius on
its residue field. -/
noncomputable def boundaryFrobeniusLift (z : ↥((Set.range j.base)ᶜ)) : Gal(Ω/C.functionField) :=
  (exists_boundaryFrobeniusLift (p := p) j sU GU τ GC z).choose

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through `SeparableClosure` and its integral closures is slow
omit [GeometricallyConnected p] in
lemma boundaryFrobeniusLift_mem_stabilizer (z : ↥((Set.range j.base)ᶜ)) :
    boundaryFrobeniusLift (p := p) j sU GU τ GC z ∈
      MulAction.stabilizer Gal(Ω/C.functionField) (boundaryChart (p := p) j z).point :=
  (exists_boundaryFrobeniusLift (p := p) j sU GU τ GC z).choose_spec.1

omit [GeometricallyConnected p] in
lemma isFrobeniusElement_boundaryFrobeniusLift (z : ↥((Set.range j.base)ᶜ)) :
    have : Finite (C.residueField z.1) := boundary_subset_finitePoints (p := p) j z.2
    IsFrobeniusElement sC GC z.1
      (restrictionMap j τ GU GC
        (genericGaloisMap j sU GU (boundaryFrobeniusLift (p := p) j sU GU τ GC z))) :=
  (exists_boundaryFrobeniusLift (p := p) j sU GU τ GC z).choose_spec.2

include hj in
omit [IsCurve pU] in
lemma mem_weilGroup_boundaryFrobeniusLift (z : ↥((Set.range j.base)ᶜ)) :
    (genericGaloisMap j sU GU (boundaryFrobeniusLift (p := p) j sU GU τ GC z),
      Multiplicative.ofAdd (p.degreeOver z.1 : ℤ)) ∈ weilGroup pU sU GU := by
  have : Finite (C.residueField z.1) := boundary_subset_finitePoints (p := p) j z.2
  rw [mem_weilGroup_fundamentalGroupMap_iff j hj sU τ GU GC]
  exact (isFrobeniusElement_boundaryFrobeniusLift (p := p) j sU GU τ GC z).mem_weilGroup p

/-- The residue Frobenius lift at a boundary point `z`, in `W(U₀)`, of degree `e_z`. -/
noncomputable def boundaryResidueFrobenius (z : ↥((Set.range j.base)ᶜ)) :
    weilGroup pU sU GU :=
  ⟨_, mem_weilGroup_boundaryFrobeniusLift j sU GU hj τ GC z⟩

omit [IsCurve pU] in
lemma isConj_restrictionHom_boundaryResidueFrobenius (z : ↥((Set.range j.base)ᶜ)) :
    IsConj (weilFrobenius p sC GC ⟨z.1, boundary_subset_finitePoints (p := p) j z.2⟩)
      (restrictionHom j hj τ GU GC (boundaryResidueFrobenius j sU GU hj τ GC z)) := by
  have : Finite (C.residueField z.1) := boundary_subset_finitePoints (p := p) j z.2
  have h₁ := isFrobeniusElement_frobeniusElement sC GC
    ⟨z.1, boundary_subset_finitePoints (p := p) j z.2⟩
  obtain ⟨c, n, hcW, hc⟩ := h₁.exists_mem_weilGroup_conj p sC GC
    (isFrobeniusElement_boundaryFrobeniusLift (p := p) j sU GU τ GC z)
  refine isConj_iff.2 ⟨⟨(c, n), hcW⟩, Subtype.ext (Prod.ext hc ?_)⟩
  change n * Multiplicative.ofAdd (p.degreeOver z.1 : ℤ) * n⁻¹ =
    Multiplicative.ofAdd (p.degreeOver z.1 : ℤ)
  rw [mul_comm n, mul_assoc, mul_inv_cancel, mul_one]

set_option synthInstance.maxHeartbeats 200000 in
-- instance search through `SeparableClosure` and its integral closures is slow
omit [GeometricallyConnected p] [IsCurve pU] in
/-- An element of `W(U₀)` mapping into the decomposition group conjugates the inertia group at `z`
into itself. -/
lemma conj_mem_boundaryInertia (z : ↥((Set.range j.base)ᶜ)) (r : weilGroup pU sU GU)
    {σ : Gal(Ω/C.functionField)}
    (hσ : σ ∈ MulAction.stabilizer Gal(Ω/C.functionField) (boundaryChart (p := p) j z).point)
    (hr : (r : GU × Multiplicative ℤ).1 = genericGaloisMap j sU GU σ) {x : weilGroup pU sU GU}
    (hx : x ∈ boundaryInertia (p := p) (pU := pU) j sU GU z) :
    r * x * r⁻¹ ∈ boundaryInertia (p := p) (pU := pU) j sU GU z := by
  obtain ⟨⟨ι, hι, hιx⟩, hx2⟩ := hx
  refine ⟨⟨σ * ι * σ⁻¹, Ideal.conj_mem_inertia hσ hι, ?_⟩,
    Subgroup.Normal.conj_mem inferInstance x hx2 r⟩
  change _ = (r : GU × Multiplicative ℤ).1 * (x : GU × Multiplicative ℤ).1 *
    (r : GU × Multiplicative ℤ).1⁻¹
  rw [map_mul, map_mul, map_inv, hr]
  exact congrArg (fun k ↦ genericGaloisMap j sU GU σ * k * (genericGaloisMap j sU GU σ)⁻¹) hιx

omit [IsCurve pU] in
/-- The residue Frobenius lift normalises the inertia group. -/
lemma map_conj_boundaryInertia (z : ↥((Set.range j.base)ᶜ)) :
    (boundaryInertia (p := p) (pU := pU) j sU GU z).map
      (MulAut.conj (boundaryResidueFrobenius j sU GU hj τ GC z)).toMonoidHom =
      boundaryInertia (p := p) (pU := pU) j sU GU z := by
  set r := boundaryResidueFrobenius j sU GU hj τ GC z
  have hσ := boundaryFrobeniusLift_mem_stabilizer (p := p) j sU GU τ GC z
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_boundaryInertia (p := p) (pU := pU) j sU GU z r hσ rfl hx
  · intro x hx
    refine ⟨r⁻¹ * x * r, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    simpa using conj_mem_boundaryInertia (p := p) (pU := pU) j sU GU z r⁻¹ (inv_mem hσ)
      (by rw [map_inv]; rfl) hx

include hj in
/-- **The inertia groups generate the kernel of the restriction** `W(U₀) → W(C₀)` as a closed
normal subgroup. -/
theorem ker_restrictionHom_eq_boundaryInertia :
    (restrictionHom j hj τ GU GC).ker = (Subgroup.normalClosure (⋃ z : ↥((Set.range j.base)ᶜ),
      SetLike.coe (boundaryInertia (p := p) (pU := pU) j sU GU z))).topologicalClosure := by
  have hcU : ∀ P, ContinuousSMul GU ((fiber sU).obj P) := fun P ↦
    IsFundamentalGroup.continuous_smul P
  have : T2Space GU := (toAutHomeo (fiber sU) GU).isEmbedding.t2Space
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace pU
  have : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated pU
  let φ : weilGroup pU sU GU →* GU := (MonoidHom.fst _ _).comp (weilGroup pU sU GU).subtype
  have hI (z : ↥((Set.range j.base)ᶜ)) :
      boundaryInertia (p := p) (pU := pU) j sU GU z ≤
        weilLocalKernel (p := p) (pU := pU) j sU GU z.1 := fun w hw ↦
    ⟨inertiaGroup_le_localKernel (p := p) sU GU _ _ hw.1, hw.2⟩
  set M := (Subgroup.normalClosure (⋃ z : ↥((Set.range j.base)ᶜ),
      SetLike.coe (boundaryInertia (p := p) (pU := pU) j sU GU z))).topologicalClosure
  have hMn : M.Normal := Subgroup.is_normal_topologicalClosure _
  refine le_antisymm ?_ (Subgroup.topologicalClosure_minimal _
    (Subgroup.normalClosure_le_normal (Set.iUnion_subset fun z ↦ (hI z).trans ?_))
    (isClosed_ker_restrictionHom j hj τ GU GC))
  swap
  · rw [ker_restrictionHom_eq j hj τ GU GC]
    exact fun w hw ↦ Subgroup.le_topologicalClosure _
      (Subgroup.subset_normalClosure (Set.mem_iUnion.2 ⟨z, hw⟩))
  rw [ker_restrictionHom_eq j hj τ GU GC]
  refine Subgroup.topologicalClosure_minimal _
    (Subgroup.normalClosure_le_normal (Set.iUnion_subset fun z ↦ ?_))
    (Subgroup.isClosed_topologicalClosure _)
  -- the image in `π₁(U₀)` of the geometric part of `M`, a closed subgroup
  let H : Subgroup GU := (M ⊓ (weilGroupDeg pU sU GU).ker).map φ
  have hHc : IsClosed (H : Set GU) := by
    rw [Subgroup.coe_map, Subgroup.coe_inf]
    exact (((isCompact_ker_weilGroupDeg pU sU GU).inter_left
      (Subgroup.isClosed_topologicalClosure _)).image
        (continuous_fst.comp continuous_subtype_val)).isClosed
  -- it is normal, being normalised by the dense Weil group
  have hHn : H.Normal := by
    let S : Subgroup GU :=
      { carrier := {g | ∀ h ∈ H, g * h * g⁻¹ ∈ H ∧ g⁻¹ * h * g ∈ H}
        mul_mem' := fun {a b} ha hb h hh ↦
          ⟨by simpa [mul_assoc] using (ha _ (hb h hh).1).1,
            by simpa [mul_assoc] using (hb _ (ha h hh).2).2⟩
        one_mem' := fun h hh ↦ by simpa using hh
        inv_mem' := fun {a} ha h hh ↦ by simpa using (ha h hh).symm }
    have hSc : IsClosed (S : Set GU) := by
      have : (S : Set GU) =
          ⋂ h ∈ (H : Set GU), ({g | g * h * g⁻¹ ∈ H} ∩ {g | g⁻¹ * h * g ∈ H}) := by
        ext g
        simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact Iff.rfl
      rw [this]
      exact isClosed_biInter fun h _ ↦
        (hHc.preimage (by fun_prop)).inter (hHc.preimage (by fun_prop))
    have hN : (M ⊓ (weilGroupDeg pU sU GU).ker).Normal := inferInstance
    have hSW : ∀ w ∈ weilGroup pU sU GU, w.1 ∈ S := by
      intro w hw h hh
      obtain ⟨v, hv, rfl⟩ := hh
      exact ⟨⟨_, hN.conj_mem v hv ⟨w, hw⟩, rfl⟩, ⟨_, hN.conj_mem v hv ⟨w, hw⟩⁻¹, by simp [φ]⟩⟩
    have hS := eq_top_of_forall_mem_weilGroup pU GU S hSc hSW
    exact ⟨fun h hh g ↦ ((hS ▸ Subgroup.mem_top g : g ∈ S) h hh).1⟩
  -- the local kernel at `z` lies in `H`
  have : Finite (C.residueField z.1) := boundary_subset_finitePoints (p := p) j z.2
  have hIH : (inertiaGroup sU GU (boundaryChart (p := p) j z)
      (boundaryChart (p := p) j z).point : Set GU) ⊆ H := by
    intro k hk
    have hkL := inertiaGroup_le_localKernel (p := p) sU GU _ _ hk
    have hkW : (k, (1 : Multiplicative ℤ)) ∈ weilGroup pU sU GU := by
      rw [mem_weilGroup_fundamentalGroupMap_iff j hj sU τ GU GC,
        MonoidHom.mem_ker.1 (localKernel_le_ker_restrictionMap j τ GU GC z.1 hkL)]
      exact (weilGroup p sC GC).one_mem
    exact ⟨⟨_, hkW⟩, ⟨Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
      (Set.mem_iUnion.2 ⟨z, hk, rfl⟩)), rfl⟩, rfl⟩
  have hle : localKernel (p := p) j sU GU z.1 ≤ H :=
    (localKernel_le_topologicalClosure_normalClosure (p := p) sU GU
      (boundaryChart (p := p) j z) z.2 _).trans
      (Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hIH) hHc)
  rintro w ⟨hg, hdeg⟩
  obtain ⟨w', ⟨hw'M, hw'deg⟩, hw'⟩ := hle hg
  obtain rfl : w' = w := Subtype.ext (Prod.ext hw' (hw'deg.trans hdeg.symm))
  exact hw'M

/-- Blueprint `lemma-boundary-stalk--1`: Boundary extension and inertia.

**The boundary datum of an open subcurve**: the restriction of Weil groups
`AlgebraicGeometry.WeilGroup.restrictionOfPath`, with the inertia group at a boundary point `z`
the image of the inertia group of a point over `z` of the integral closure of an affine chart at
`z` in the separable closure of the function field, and the residue Frobenius lift at `z` the
image of an element of its decomposition group inducing the inverse arithmetic Frobenius on the
residue field. -/
noncomputable def boundaryDatum :
    BoundaryDatum j (ofFundamentalGroup pU sU GU) (ofFundamentalGroup p sC GC) where
  toRestriction := restrictionOfPath j hj τ GU GC
  finite_boundary := finite_boundary (p := p) j
  boundary_subset_finitePoints := boundary_subset_finitePoints (p := p) j
  inertia z := boundaryInertia (p := p) (pU := pU) j sU GU z
  inertia_le _ := inf_le_right
  ker_restrict_eq := ker_restrictionHom_eq_boundaryInertia j sU GU hj τ GC
  residueFrobenius z := boundaryResidueFrobenius j sU GU hj τ GC z
  deg_residueFrobenius _ := rfl
  restrict_residueFrobenius z := isConj_restrictionHom_boundaryResidueFrobenius j sU GU hj τ GC z
  normalizes_inertia z := map_conj_boundaryInertia j sU GU hj τ GC z

end Datum

omit [Smooth p] [IsIntegral C] in
/-- A nonempty open `j : U₀ ⟶ C₀` of a smooth geometrically connected curve over a finite field,
itself geometrically connected, has a boundary datum
(`AlgebraicGeometry.WeilGroup.boundaryDatum`). -/
theorem BoundaryDatum.nonempty [SmoothOfRelativeDimension 1 p] (hj : j ≫ p = pU) :
    ∃ (WU : WeilGroup pU) (WC : WeilGroup p), Nonempty (BoundaryDatum j WU WC) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := IsRegular.of_smooth p
  have : IsIntegral C := IsRegular.isIntegral C
  obtain ⟨sU⟩ := pU.nonempty_algebraicClosure_point
  obtain ⟨sC⟩ := p.nonempty_algebraicClosure_point
  obtain ⟨GU, _, _⟩ := exists_isFundamentalGroup sU
  obtain ⟨GC, _, _⟩ := exists_isFundamentalGroup sC
  obtain ⟨τ⟩ := nonempty_iso_of_fiberFunctor (fiber (sU ≫ j)) (fiber sC)
  exact ⟨_, _, ⟨boundaryDatum j sU GU hj τ GC⟩⟩

end AlgebraicGeometry.WeilGroup
