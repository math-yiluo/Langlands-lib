/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
public import WeilConjectures.AlgebraicGeometry.Curve.Kummer
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The cohomology of `μ_m` on a smooth proper curve

Let `X` be a smooth proper connected curve over an algebraically closed field `k` and `m` an
integer prime to the characteristic. The Kummer sequence identifies `H¹(X, μ_m)` with the
`m`-torsion `Pic(X)[m]` and `H²(X, μ_m)` with `Pic(X)/m`. The degree modulo `m` defines a trace
`H²(X, μ_m) ⟶ ℤ/m`, which is bijective since `Pic⁰(X)` is the group of points of the Jacobian, a
divisible group. In particular `H²(X, μ_m)` has exactly `m` elements.

## Main definitions

- `AlgebraicGeometry.Scheme.kummerTorsionEquiv`: the Kummer identification
  `H¹(X, μ_m) ≅ Pic(X)[m]`.
- `AlgebraicGeometry.Scheme.picToSheafHTwo`: the Kummer map `Pic(X) ⟶ H²(X, μ_m)`.
- `AlgebraicGeometry.Scheme.sheafHTwoTrace`: the trace `H²(X, μ_m) ⟶ ℤ/m`.

## Main statements

- `AlgebraicGeometry.Scheme.surjective_pow_picardZero`: `Pic⁰(X)` is divisible.
- `AlgebraicGeometry.Scheme.bijective_sheafHTwoTrace`: the trace is bijective.
- `AlgebraicGeometry.Scheme.card_sheafH_two_rootsOfUnitySheaf`: `#H²(X, μ_m) = m`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- `Pic⁰` of a smooth proper connected curve over an algebraically closed field is divisible: it
is the group of points of the Jacobian, an abelian variety. -/
lemma surjective_pow_picardZero [GeometricallyIntegral (X ↘ Spec (.of k))] (n : ℕ)
    (hn : 0 < n) : Function.Surjective fun L : picardZero k X ↦ L ^ n := by
  obtain ⟨J, _, -, hP, hS, hG, -, ⟨φ⟩⟩ := exists_jacobian (k := k) (X := X)
  have : Smooth J.hom := SmoothOfRelativeDimension.smooth (arithmeticGenus k X) _
  have : IrreducibleSpace J.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := J.hom)
  have : IsAbelianVariety J := ⟨⟩
  obtain ⟨-, -, hdiv, -, -⟩ := abelianVariety_estimate_of_isAlgClosed (ringChar k) J
  intro L
  obtain ⟨a, ha⟩ := hdiv n hn (φ L)
  exact ⟨φ.symm a, by simp only [← map_pow, ha, MulEquiv.symm_apply_apply]⟩

/-- The degree modulo `m` of the class of an invertible module. -/
noncomputable def picDegreeMod (m : ℕ) : Additive X.Pic →+ ZMod m where
  toFun L := ((picDegreeHom k X L.toMul).toAdd : ZMod m)
  map_zero' := by simp
  map_add' L L' := by simp

lemma ker_picDegreeMod [GeometricallyIntegral (X ↘ Spec (.of k))] [Nonempty X] (m : ℕ)
    (hm : 0 < m) :
    (picDegreeMod (k := k) (X := X) m).ker =
      (zsmulAddGroupHom (α := Additive X.Pic) (m : ℤ)).range := by
  ext L
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  constructor
  · intro hL
    change (((picDegreeHom k X L.toMul).toAdd : ℤ) : ZMod m) = 0 at hL
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hL
    obtain ⟨d, hd⟩ := hL
    obtain ⟨L₁, hL₁⟩ := surjective_picDegreeHom (k := k) (C := X) (.ofAdd d)
    have h₀ : L.toMul * (L₁ ^ m)⁻¹ ∈ picardZero k X := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hL₁, ← ofAdd_toAdd (picDegreeHom k X _),
        hd, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add, ofAdd_eq_one, nsmul_eq_mul]
      ring
    obtain ⟨L₂, hL₂⟩ := surjective_pow_picardZero (k := k) (X := X) m hm ⟨_, h₀⟩
    refine ⟨Additive.ofMul (L₁ * L₂.1), ?_⟩
    apply Additive.toMul.injective
    rw [zsmulAddGroupHom_apply, natCast_zsmul, toMul_nsmul, toMul_ofMul, mul_pow]
    have := congrArg Subtype.val hL₂
    simp only [SubgroupClass.coe_pow] at this
    rw [this, mul_comm, inv_mul_cancel_right]
  · rintro ⟨L', rfl⟩
    change (((picDegreeHom k X (((m : ℤ) • L').toMul)).toAdd : ℤ) : ZMod m) = 0
    rw [toMul_zsmul, map_zpow, toAdd_zpow, smul_eq_mul, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul]

/-! ### The Kummer identifications in degrees one and two -/

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [IsAlgClosed k] in
/-- An integer which is nonzero in `k` is a unit on every `k`-scheme. -/
lemma isUnit_natCast_appTop (m : ℕ) (hm : (m : k) ≠ 0) : IsUnit (m : Γ(X, ⊤)) := by
  simpa using hm.isUnit.map ((ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] in
/-- On a proper scheme over an algebraically closed field, the map `H¹(X, μ_m) ⟶ H¹(X, 𝔾ₘ)`
induced by the inclusion `μ_m ⊆ 𝔾ₘ` is injective: global units are `m`-th powers. -/
lemma injective_sheafHMap_kernelι_one (m : ℕ) (hm : (m : k) ≠ 0) :
    Function.Injective (Sheaf.H.map (kernel.ι (m • 𝟙 X.gmSheaf)) 1) := by
  obtain ⟨hα, hαβ, -⟩ := X.exact_sheafH_rootsOfUnitySheaf_one m (isUnit_natCast_appTop m hm)
  let := (globalSectionsRingHom k (X := X)).toAlgebra
  have : Module.Finite k Γ(X, ⊤) := finite_globalSectionsRingHom_of_isProper
  have hdiv := IsAlgClosed.exists_pow_eq_of_finite (A := Γ(X, ⊤)) hm
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨u, rfl⟩ := (hαβ x).1 hx
  obtain ⟨v, hv⟩ := hdiv (Additive.toMul u)
  have hu : u ∈ (X.kummerδ₀ m (isUnit_natCast_appTop m hm)).ker := by
    rw [hα]
    exact ⟨Additive.ofMul v, by simp [← ofMul_pow, hv]⟩
  exact hu

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [IsAlgClosed k] in
/-- The image of `H¹(X, μ_m) ⟶ H¹(X, 𝔾ₘ) ≅ Pic(X)` is the `m`-torsion. -/
lemma mem_torsionBy_iff_exists_sheafHMap_kernelι_one (m : ℕ) (hm : (m : k) ≠ 0)
    (L : Additive X.Pic) :
    L ∈ AddSubgroup.torsionBy (Additive X.Pic) (m : ℤ) ↔
      ∃ x, (Pic.toCohomologicalPicardGroupAddEquiv X).symm
        (Sheaf.H.map (kernel.ι (m • 𝟙 X.gmSheaf)) 1 x) = L := by
  obtain ⟨-, -, hβ⟩ := X.exact_sheafH_rootsOfUnitySheaf_one m (isUnit_natCast_appTop m hm)
  have h := congrArg (fun H : AddSubgroup X.CohomologicalPicardGroup ↦
    Pic.toCohomologicalPicardGroupAddEquiv X L ∈ H) hβ
  simp only [AddMonoidHom.mem_range, eq_iff_iff] at h
  rw [AddSubgroup.torsionBy.nsmul_iff]
  simp only [AddEquiv.symm_apply_eq]
  rw [h, AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul, AddEquivClass.map_eq_zero_iff]

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] in
/-- Blueprint `proposition-h-1-curve-tate-module--1` (first step): the Kummer
identification `H¹(X, μ_m) ≅ Pic(X)[m]` of a proper scheme `X` over an algebraically closed
field, for `m` prime to the characteristic: the map induced by `μ_m ⊆ 𝔾ₘ`, followed by the
canonical identification `H¹(X, 𝔾ₘ) ≅ Pic(X)`
(`AlgebraicGeometry.Scheme.Pic.toCohomologicalPicardGroupAddEquiv`). -/
noncomputable def kummerTorsionEquiv (m : ℕ) (hm : (m : k) ≠ 0) :
    Sheaf.H (X.rootsOfUnitySheaf m) 1 ≃+ AddSubgroup.torsionBy (Additive X.Pic) (m : ℤ) :=
  (AddMonoidHom.ofInjective
    (f := ((Pic.toCohomologicalPicardGroupAddEquiv X).symm.toAddMonoidHom.comp
      (Sheaf.H.map (kernel.ι (m • 𝟙 X.gmSheaf)) 1)))
    ((Pic.toCohomologicalPicardGroupAddEquiv X).symm.injective.comp
      (injective_sheafHMap_kernelι_one m hm))).trans
    (AddEquiv.addSubgroupCongr (by
      ext L
      rw [mem_torsionBy_iff_exists_sheafHMap_kernelι_one m hm]
      rfl))

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] in
/-- The Kummer identification sends a class to its image in `Pic(X)`. -/
lemma coe_kummerTorsionEquiv_apply (m : ℕ) (hm : (m : k) ≠ 0)
    (x : Sheaf.H (X.rootsOfUnitySheaf m) 1) :
    (kummerTorsionEquiv m hm x : Additive X.Pic) = (Pic.toCohomologicalPicardGroupAddEquiv X).symm
      (Sheaf.H.map (kernel.ι (m • 𝟙 X.gmSheaf)) 1 x) :=
  rfl

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] in
/-- The Kummer map `Pic(X) ≅ H¹(X, 𝔾ₘ) ⟶ H²(X, μ_m)`, the connecting map of the Kummer
sequence. -/
noncomputable def picToSheafHTwo (m : ℕ) (hm : (m : k) ≠ 0) :
    Additive X.Pic →+ Sheaf.H (X.rootsOfUnitySheaf m) 2 :=
  (X.kummerδ₁ m (isUnit_natCast_appTop m hm)).comp
    (Pic.toCohomologicalPicardGroupAddEquiv X).toAddMonoidHom

/-- On a smooth curve over an algebraically closed field the Kummer map to `H²(X, μ_m)` is
surjective, since the Brauer group vanishes. -/
lemma surjective_picToSheafHTwo (m : ℕ) (hm : (m : k) ≠ 0) :
    Function.Surjective (picToSheafHTwo (X := X) m hm) := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsCurve (X ↘ Spec (.of k)) :=
    { krullDim_le_one := topologicalKrullDim_le_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) 1 }
  have := IsCurve.subsingleton_cohomologicalBrauerGroup_of_smooth (X ↘ Spec (.of k))
  obtain ⟨-, hαβ, -⟩ := X.exact_sheafH_rootsOfUnitySheaf_two m (isUnit_natCast_appTop m hm)
  intro y
  obtain ⟨z, hz⟩ := (hαβ y).1 (Subsingleton.elim _ _)
  exact ⟨(Pic.toCohomologicalPicardGroupAddEquiv X).symm z, by simp [picToSheafHTwo, hz]⟩

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [IsAlgClosed k] in
/-- The kernel of the Kummer map to `H²(X, μ_m)` consists of the `m`-th multiples. -/
lemma picToSheafHTwo_eq_zero_iff (m : ℕ) (hm : (m : k) ≠ 0) (L : Additive X.Pic) :
    picToSheafHTwo m hm L = 0 ↔ ∃ L', (m : ℤ) • L' = L := by
  obtain ⟨hα, -, -⟩ := X.exact_sheafH_rootsOfUnitySheaf_two m (isUnit_natCast_appTop m hm)
  have h := congrArg (fun H : AddSubgroup X.CohomologicalPicardGroup ↦
    Pic.toCohomologicalPicardGroupAddEquiv X L ∈ H) hα
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range, zsmulAddGroupHom_apply,
    eq_iff_iff] at h
  rw [picToSheafHTwo, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨(Pic.toCohomologicalPicardGroupAddEquiv X).symm z, by
      rw [← map_zsmul, hz, AddEquiv.symm_apply_apply]⟩
  · rintro ⟨L', rfl⟩
    exact ⟨Pic.toCohomologicalPicardGroupAddEquiv X L', by rw [map_zsmul]⟩

omit [IsAlgClosed k] in
/-- The kernel of the Kummer map to `H²(X, μ_m)` has degree divisible by `m`. -/
lemma ker_picToSheafHTwo_le (m : ℕ) (hm : (m : k) ≠ 0) :
    (picToSheafHTwo (X := X) m hm).ker ≤ (picDegreeMod (k := k) (X := X) m).ker := by
  intro L hL
  obtain ⟨L', rfl⟩ := (picToSheafHTwo_eq_zero_iff m hm L).1 hL
  rw [AddMonoidHom.mem_ker, map_zsmul, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul]

/-- The trace `H²(X, μ_m) ⟶ ℤ/m` of a smooth proper curve over an algebraically closed field:
the degree modulo `m` of a line bundle whose Kummer class is the given class. -/
noncomputable def sheafHTwoTrace (m : ℕ) (hm : (m : k) ≠ 0) :
    Sheaf.H (X.rootsOfUnitySheaf m) 2 →+ ZMod m :=
  (QuotientAddGroup.lift _ (picDegreeMod (k := k) m) (ker_picToSheafHTwo_le m hm)).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (surjective_picToSheafHTwo (X := X) m hm)).symm.toAddMonoidHom

/-- The trace of the Kummer class of a line bundle is its degree modulo `m`. -/
@[simp]
lemma sheafHTwoTrace_picToSheafHTwo (m : ℕ) (hm : (m : k) ≠ 0) (L : Additive X.Pic) :
    sheafHTwoTrace m hm (picToSheafHTwo m hm L) = picDegreeMod (k := k) m L := by
  have e : (QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_picToSheafHTwo (X := X) m
      hm)).symm (picToSheafHTwo m hm L) = (L : Additive X.Pic ⧸ (picToSheafHTwo m hm).ker) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  rw [sheafHTwoTrace, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, e]
  rfl

/-- The trace `H²(X, μ_m) ⟶ ℤ/m` of a smooth proper connected curve over an algebraically
closed field is bijective: by the Kummer sequence `H²(X, μ_m)` is `Pic(X)/m`, which the degree
identifies with `ℤ/m` since `Pic⁰(X)` is divisible. -/
theorem bijective_sheafHTwoTrace [GeometricallyIntegral (X ↘ Spec (.of k))] [Nonempty X]
    (m : ℕ) [NeZero m] (hm : (m : k) ≠ 0) :
    Function.Bijective (sheafHTwoTrace (X := X) m hm) := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  refine ⟨?_, fun a ↦ ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨L, rfl⟩ := surjective_picToSheafHTwo m hm z
    rw [sheafHTwoTrace_picToSheafHTwo, ← AddMonoidHom.mem_ker, ker_picDegreeMod m hm0] at hz
    obtain ⟨L', rfl⟩ := hz
    exact (picToSheafHTwo_eq_zero_iff m hm _).2 ⟨L', rfl⟩
  · obtain ⟨L, hL⟩ := surjective_picDegreeHom (k := k) (C := X) (.ofAdd (a.val : ℤ))
    refine ⟨picToSheafHTwo m hm (Additive.ofMul L), ?_⟩
    rw [sheafHTwoTrace_picToSheafHTwo]
    change (((picDegreeHom k X L).toAdd : ℤ) : ZMod m) = a
    rw [hL, toAdd_ofAdd, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- `H²(X, μ_m)` has exactly `m` elements for a smooth proper connected curve `X` over an
algebraically closed field and `m` prime to the characteristic: by the Kummer sequence it is
`Pic(X)/m`, which the degree identifies with `ℤ/m` since `Pic⁰(X)` is divisible. -/
theorem card_sheafH_two_rootsOfUnitySheaf [GeometricallyIntegral (X ↘ Spec (.of k))]
    [Nonempty X] (m : ℕ) [NeZero m] (hm : (m : k) ≠ 0) :
    Nonempty (Sheaf.H (X.rootsOfUnitySheaf m) 2 ≃+ ZMod m) :=
  ⟨AddEquiv.ofBijective _ (bijective_sheafHTwoTrace m hm)⟩

end AlgebraicGeometry.Scheme
