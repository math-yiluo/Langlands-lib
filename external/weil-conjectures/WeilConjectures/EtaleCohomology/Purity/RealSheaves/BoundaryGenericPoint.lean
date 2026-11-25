/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia

/-!
# The geometric generic point of the geometric curve

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over a finite field
`k₀`, `Ω` the separable closure of the function field `k(C)` and `η₀ : Spec Ω ⟶ U₀` the generic
geometric point. Choosing an embedding `ι : k̄ ⟶ Ω` over `k₀`
(`AlgebraicGeometry.WeilGroup.genericEmb`), `η₀` lifts to a geometric point
`η : Spec Ω ⟶ Ū = U₀ ×_{k₀} k̄` (`AlgebraicGeometry.WeilGroup.genericGeomPoint`).

The action of the Galois group `Gal(Ω / k(C))` on `k̄ ⊆ Ω` is read off from the Weil group: if the
image `(ρ(σ), n)` of `σ` lies in the Weil group `W(U₀)`, then `σ` acts on `ι(k̄)` as the `n`-th
power of the geometric Frobenius (`AlgebraicGeometry.WeilGroup.genericEmb_galois`), since the
Weil group is defined by the action on the fibres of the constant covers `U₀ ×_{k₀} Spec A`, which
at `η₀` are the `k₀`-embeddings `A ⟶ Ω`. Hence `Spec σ ≫ η = η ≫ Frⁿ`
(`AlgebraicGeometry.WeilGroup.specMap_comp_genericGeomPoint`): inertia elements (`n = 0`) act on
`Spec Ω` over `Ū`, and residue Frobenius lifts (`n = deg z`) act over the geometric Frobenius.
This is used to compare the boundary stalks of direct images with the inertia invariants of the
Weil fundamental representation (blueprint `lemma-boundary-stalk--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {pU : U ⟶ Spec (.of K)}
  (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U] [IsIntegral C]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

/-- The generic geometric point `η₀ : Spec Ω ⟶ U₀`. -/
noncomputable abbrev genericBasePoint : Spec (.of Ω) ⟶ U :=
  pointOfAlgebra Ω (genericPointLift j)

variable (pU) in
/-- The structure map `k₀ ⟶ Ω` of the generic geometric point. -/
noncomputable def genericStructHom : K →+* Ω :=
  (Spec.preimage (genericBasePoint j ≫ pU)).hom

omit [Finite K] in
variable (pU) in
lemma spec_genericStructHom :
    Spec.map (CommRingCat.ofHom (genericStructHom pU j)) = genericBasePoint j ≫ pU := by
  rw [genericStructHom, CommRingCat.ofHom_hom, Spec.map_preimage]

variable (pU) in
/-- An embedding `ι : k̄ ⟶ Ω` over `k₀`. -/
noncomputable def genericEmb : AlgebraicClosure K →+* Ω :=
  letI := (genericStructHom pU j).toAlgebra
  (IsSepClosed.lift : AlgebraicClosure K →ₐ[K] Ω).toRingHom

lemma genericEmb_algebraMap (x : K) :
    genericEmb pU j (algebraMap K (AlgebraicClosure K) x) = genericStructHom pU j x := by
  let _ := (genericStructHom pU j).toAlgebra
  exact (IsSepClosed.lift : AlgebraicClosure K →ₐ[K] Ω).commutes x

lemma genericEmb_comp_algebraMap :
    (genericEmb pU j).comp (algebraMap K (AlgebraicClosure K)) = genericStructHom pU j :=
  RingHom.ext (genericEmb_algebraMap j)

variable (pU) in
lemma genericBasePoint_comp :
    genericBasePoint j ≫ pU = Spec.map (CommRingCat.ofHom (genericEmb pU j)) ≫
      (Scheme.specAlgebraicClosure K).hom := by
  rw [← spec_genericStructHom, ← genericEmb_comp_algebraMap]
  change _ = _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

variable (pU) in
/-- The geometric generic point `η : Spec Ω ⟶ Ū`, lifting `η₀` through `ι`. -/
noncomputable def genericGeomPoint : Spec (.of Ω) ⟶ pU.geometricFiber :=
  pullback.lift (genericBasePoint j) (Spec.map (CommRingCat.ofHom (genericEmb pU j)))
    (genericBasePoint_comp pU j)

@[reassoc (attr := simp)]
lemma genericGeomPoint_geometricFiberProj :
    genericGeomPoint pU j ≫ pU.geometricFiberProj = genericBasePoint j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma genericGeomPoint_geometricFiberToAlgebraicClosure :
    genericGeomPoint pU j ≫ pU.geometricFiberToAlgebraicClosure =
      Spec.map (CommRingCat.ofHom (genericEmb pU j)) :=
  pullback.lift_snd _ _ _

omit [Finite K] in
/-- Galois automorphisms of `Ω` over `k(C)` fix the structure map `k₀ ⟶ Ω`. -/
lemma galois_comp_genericStructHom (σ : Gal(Ω/C.functionField)) :
    (σ : Ω →+* Ω).comp (genericStructHom pU j) = genericStructHom pU j := by
  have h : Spec.map (CommRingCat.ofHom (genericStructHom pU j) ≫
      CommRingCat.ofHom (σ : Ω →+* Ω)) = Spec.map (CommRingCat.ofHom (genericStructHom pU j)) := by
    rw [Spec.map_comp, spec_genericStructHom, ← Category.assoc]
    congr 1
    exact specMapIso_hom_comp_pointOfAlgebra (genericPointLift j) σ
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

section Constant

/-- The point of the fibre at `η₀` of the constant cover `U₀ ×_{k₀} Spec A` given by an embedding
`ψ : A ⟶ Ω` over `k₀`. -/
noncomputable def constantCoverPoint (A : FiniteEtaleAlgebra K) (ψ : A.1 →+* Ω)
    (hψ : ψ.comp (algebraMap K A.1) = genericStructHom pU j) :
    (fiber (genericBasePoint j)).obj (constantCover pU A) :=
  fiberMk _ _ (pullback.lift (genericBasePoint j) (Spec.map (CommRingCat.ofHom ψ)) (by
    rw [← spec_genericStructHom, ← hψ]
    change _ = _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl)) (pullback.lift_fst _ _ _)

omit [Finite K] in
lemma constantCoverPoint_left (A : FiniteEtaleAlgebra K) (ψ : A.1 →+* Ω)
    (hψ : ψ.comp (algebraMap K A.1) = genericStructHom pU j) :
    (constantCoverPoint j A ψ hψ).left =
      pullback.lift (genericBasePoint j) (Spec.map (CommRingCat.ofHom ψ)) (by
        rw [← spec_genericStructHom, ← hψ]
        change _ = _ ≫ Spec.map _
        rw [← Spec.map_comp]
        rfl) :=
  rfl

omit [Finite K] in
lemma constantCoverPoint_injective (A : FiniteEtaleAlgebra K) {ψ ψ' : A.1 →+* Ω}
    (hψ : ψ.comp (algebraMap K A.1) = genericStructHom pU j)
    (hψ' : ψ'.comp (algebraMap K A.1) = genericStructHom pU j)
    (h : constantCoverPoint j A ψ hψ = constantCoverPoint j A ψ' hψ') : ψ = ψ' := by
  have h' := congrArg (fun x ↦ x.left ≫ pullback.snd pU A.specHom) h
  simp only [constantCoverPoint_left, pullback.lift_snd] at h'
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h')

omit [Finite K] in
lemma galoisToAut_constantCoverPoint (σ : Gal(Ω/C.functionField)) (A : FiniteEtaleAlgebra K)
    (ψ : A.1 →+* Ω) (hψ : ψ.comp (algebraMap K A.1) = genericStructHom pU j) :
    (galoisToAut (genericPointLift j) σ).asIso.hom.app _ (constantCoverPoint j A ψ hψ) =
      constantCoverPoint j A ((σ : Ω →+* Ω).comp ψ)
        (by rw [RingHom.comp_assoc, hψ, galois_comp_genericStructHom]) := by
  apply fiber_ext
  rw [galoisToAut_hom_app_left, constantCoverPoint_left, constantCoverPoint_left]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    exact specMapIso_hom_comp_pointOfAlgebra (genericPointLift j) σ
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Spec.map_comp]
    rfl

lemma fiber_map_arithmeticFrobenius_constantCoverPoint (A : FiniteEtaleAlgebra K)
    (ψ : A.1 →+* Ω) (hψ : ψ.comp (algebraMap K A.1) = genericStructHom pU j) :
    (fiber (genericBasePoint j)).map (arithmeticFrobenius pU A).hom
        (constantCoverPoint j A ψ hψ) =
      constantCoverPoint j A (ψ.comp (A.frobenius : A.1 →+* A.1)) (by
        rw [RingHom.comp_assoc]
        convert hψ using 2
        ext c
        exact A.frobenius.commutes c) := by
  apply fiber_ext
  rw [fiber_map_left, constantCoverPoint_left, constantCoverPoint_left,
    show (arithmeticFrobenius pU A).hom = constantCoverMap pU A A.frobenius.toAlgHom from rfl,
    constantCoverMap_hom_left]
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, ← Spec.map_comp]
    rfl

lemma geometricFrobenius_pow_constantCoverPoint (A : FiniteEtaleAlgebra K) (n : ℕ)
    (ψ : A.1 →+* Ω) (hψ : ψ.comp (algebraMap K A.1) = genericStructHom pU j) :
    (geometricFrobenius pU (genericBasePoint j) A ^ n) (constantCoverPoint j A ψ hψ) =
      constantCoverPoint j A (ψ.comp ((A.frobenius.symm ^ n : A.1 ≃ₐ[K] A.1) : A.1 →+* A.1))
        (by
          rw [RingHom.comp_assoc]
          convert hψ using 2
          ext c
          exact (A.frobenius.symm ^ n).commutes c) := by
  induction n with
  | zero =>
    congr
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    rw [geometricFrobenius, Equiv.Perm.inv_def, Equiv.symm_apply_eq]
    change _ = (fiber (genericBasePoint j)).map (arithmeticFrobenius pU A).hom _
    rw [fiber_map_arithmeticFrobenius_constantCoverPoint]
    congr 1
    rw [RingHom.comp_assoc]
    congr 1
    ext y
    simp [pow_succ]

end Constant

section Degree

variable [GeometricallyConnected pU] [ConnectedSpace U]
  (sU : Spec (.of (AlgebraicClosure K)) ⟶ U)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]

omit [IsOpenImmersion j] [Nonempty U] [IsIntegral C] [GeometricallyConnected pU]
  [ConnectedSpace U] in
/-- Paths commute with the geometric Frobenius of the constant covers. -/
lemma geometricFrobenius_pow_path {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsSepClosed Ω₁] [Field Ω₂]
    [IsSepClosed Ω₂] {s : Spec (.of Ω₁) ⟶ U} {s' : Spec (.of Ω₂) ⟶ U}
    (τ : fiber s ≅ fiber s') (A : FiniteEtaleAlgebra K) (n : ℕ)
    (x : (fiber s).obj (constantCover pU A)) :
    (geometricFrobenius pU s' A ^ n) (τ.hom.app _ x) =
      τ.hom.app _ ((geometricFrobenius pU s A ^ n) x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    set y := (geometricFrobenius pU s A ^ n) x
    rw [geometricFrobenius, Equiv.Perm.inv_def, Equiv.symm_apply_eq]
    change _ = (fiber s').map (arithmeticFrobenius pU A).hom _
    rw [← ConcreteCategory.comp_apply, ← τ.hom.naturality, ConcreteCategory.comp_apply]
    congr 1
    exact (fiber_map_arithmeticFrobenius_geometricFrobenius pU s A y).symm

/-- The powers of the inverse Frobenius of an intermediate field of `k̄` are the restrictions of
the powers of the geometric Frobenius. -/
lemma coe_frobenius_symm_pow (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] (hA : Module.Finite K L ∧ Algebra.Etale K L) (n : ℕ) (y : L) :
    letI := Fintype.ofFinite K
    (((FiniteEtaleAlgebra.frobenius ⟨CommAlgCat.of K L, hA⟩).symm ^ n) y : AlgebraicClosure K) =
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ n) y := by
  let _ := Fintype.ofFinite K
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, pow_succ', AlgEquiv.mul_apply, ← ih]
    set z := ((FiniteEtaleAlgebra.frobenius ⟨CommAlgCat.of K L, hA⟩).symm ^ n) y
    rw [FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, AlgEquiv.aut_inv,
      eq_comm, AlgEquiv.symm_apply_eq, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    have h := (FiniteEtaleAlgebra.frobenius_apply ⟨CommAlgCat.of K L, hA⟩
      ((FiniteEtaleAlgebra.frobenius ⟨CommAlgCat.of K L, hA⟩).symm z))
    rw [AlgEquiv.apply_symm_apply] at h
    have h' := congrArg (fun w : L ↦ (w : AlgebraicClosure K)) h
    simp only at h'
    rw [h', Nat.card_eq_fintype_card]
    rfl

/-- **Galois automorphisms act on `k̄ ⊆ Ω` through their degree.** If the image `(ρ(σ), n)` of
`σ ∈ Gal(Ω / k(C))` lies in the Weil group, then `σ ∘ ι = ι ∘ Φⁿ` on `k̄`, `Φ` the geometric
Frobenius. -/
theorem genericEmb_galois (σ : Gal(Ω/C.functionField)) (n : ℕ)
    (h : (genericGaloisMap j sU GU σ, Multiplicative.ofAdd (n : ℤ)) ∈ weilGroup pU sU GU)
    (x : AlgebraicClosure K) :
    letI := Fintype.ofFinite K
    σ (genericEmb pU j x) = genericEmb pU j
      ((FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ n) x) := by
  let _ := Fintype.ofFinite K
  let L : IntermediateField K (AlgebraicClosure K) := IntermediateField.adjoin K {x}
  have : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have : Algebra.IsSeparable K L := Algebra.IsSeparable.of_algHom K (AlgebraicClosure K) L.val
  have : Algebra.FormallyEtale K L := .of_isSeparable K L
  have hA : Module.Finite K L ∧ Algebra.Etale K L :=
    ⟨inferInstance, ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩⟩
  let A : FiniteEtaleAlgebra K := ⟨CommAlgCat.of K L, hA⟩
  let ψ : A.1 →+* Ω := (genericEmb pU j).comp (L.val : L →+* AlgebraicClosure K)
  have hψ : ψ.comp (algebraMap K A.1) = genericStructHom pU j :=
    RingHom.ext fun c ↦ genericEmb_algebraMap (pU := pU) j c
  have hw := (mem_weilGroup_iff pU sU GU).1 h A
    ((genericPath j sU).hom.app _ (constantCoverPoint j A ψ hψ))
  rw [genericGaloisMap, galoisToFundamentalGroup_smul, galoisToAut_constantCoverPoint] at hw
  simp only [toAdd_ofAdd, zpow_natCast] at hw
  rw [geometricFrobenius_pow_path, geometricFrobenius_pow_constantCoverPoint] at hw
  have hinj := (ConcreteCategory.bijective_of_isIso ((genericPath j sU).hom.app
    (constantCover pU A))).1
  have e := constantCoverPoint_injective j A _ _ (hinj hw)
  have hx := RingHom.congr_fun e ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  simp only [RingHom.comp_apply, ψ] at hx
  refine hx.trans (congrArg (genericEmb pU j) ?_)
  exact coe_frobenius_symm_pow L hA n _

/-- **The action of Galois automorphisms on the geometric generic point.** If `(ρ(σ), n)` lies in
the Weil group, then `Spec σ ≫ η = η ≫ Frⁿ`. -/
theorem specMap_comp_genericGeomPoint (σ : Gal(Ω/C.functionField)) (n : ℕ)
    (h : (genericGaloisMap j sU GU σ, Multiplicative.ofAdd (n : ℤ)) ∈ weilGroup pU sU GU) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ genericGeomPoint pU j =
      genericGeomPoint pU j ≫ (pU.geometricGaloisFrobenius ^ n).asIso.hom := by
  let _ := Fintype.ofFinite K
  apply pullback.hom_ext
  · change _ ≫ genericGeomPoint pU j ≫ pU.geometricFiberProj =
      _ ≫ (pU.geometricGaloisFrobenius ^ n).asIso.hom ≫ pU.geometricFiberProj
    rw [genericGeomPoint_geometricFiberProj,
      Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj,
      genericGeomPoint_geometricFiberProj]
    exact specMapIso_hom_comp_pointOfAlgebra (genericPointLift j) σ
  · change _ ≫ genericGeomPoint pU j ≫ pU.geometricFiberToAlgebraicClosure =
      _ ≫ (pU.geometricGaloisFrobenius ^ n).asIso.hom ≫ pU.geometricFiberToAlgebraicClosure
    rw [genericGeomPoint_geometricFiberToAlgebraicClosure,
      Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure,
      genericGeomPoint_geometricFiberToAlgebraicClosure_assoc, specGeometricFrobenius_pow_hom,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun x ↦ genericEmb_galois j sU GU σ n h x)

end Degree

end AlgebraicGeometry.WeilGroup
