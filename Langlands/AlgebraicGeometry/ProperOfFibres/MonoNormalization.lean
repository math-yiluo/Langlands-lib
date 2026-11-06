import Mathlib
import Langlands.AlgebraicGeometry.NoetherianApproximation.IntegerFiniteTypeNormalizationProof

/-! # Finite normalization of a monomorphism of finite type out of an integral scheme -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ProperOfFibres

/-- **Algebraic finiteness.** Let `A` be a finitely generated `ℤ`-algebra and `C` a domain which is
an `A`-algebra such that every element of `C` is a fraction of images of elements of `A`. Then the
integral closure of `A` in `C` is a finite `A`-module. -/
theorem finite_integralClosure_of_forall_exists_mul_eq {A C : Type u} [CommRing A] [CommRing C]
    [IsDomain C] [Algebra A C] [Algebra.FiniteType ℤ A]
    (h : ∀ c : C, ∃ a b : A, algebraMap A C b ≠ 0 ∧ c * algebraMap A C b = algebraMap A C a) :
    Module.Finite A (integralClosure A C) := by
  classical
  let S : Subalgebra A C := (Algebra.ofId A C).range
  let L := FractionRing C
  have hS : ∀ s : S, ∃ a : A, algebraMap A C a = s := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  have hsurj : Function.Surjective (algebraMap A S) := by
    intro s
    obtain ⟨a, ha⟩ := hS s
    exact ⟨a, Subtype.ext ha⟩
  have : Algebra.FiniteType ℤ S :=
    Algebra.FiniteType.of_surjective ((Algebra.ofId A S).restrictScalars ℤ) hsurj
  have hinjCL : Function.Injective (algebraMap C L) := IsFractionRing.injective C L
  have hinjSL : Function.Injective (algebraMap S L) := by
    rw [Subalgebra.algebraMap_eq]
    exact hinjCL.comp Subtype.val_injective
  have : FaithfulSMul S L := (faithfulSMul_iff_algebraMap_injective S L).mpr hinjSL
  have hASL : IsScalarTower A S L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A C L, Subalgebra.algebraMap_def]
    rfl
  -- `L` is a fraction field of `S`
  have hfrac : ∀ c : C, ∃ x y : S, algebraMap S L y ≠ 0 ∧
      algebraMap C L c = algebraMap S L x / algebraMap S L y := by
    intro c
    obtain ⟨a, b, hb, hab⟩ := h c
    refine ⟨algebraMap A S a, algebraMap A S b, ?_, ?_⟩
    · rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A C L]
      exact (map_ne_zero_iff _ hinjCL).mpr hb
    · rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply A C L, IsScalarTower.algebraMap_apply A C L, ← hab,
        map_mul]
      have : algebraMap C L (algebraMap A C b) ≠ 0 := (map_ne_zero_iff _ hinjCL).mpr hb
      rw [mul_div_cancel_right₀ _ this]
  have : IsFractionRing S L := by
    refine IsFractionRing.of_field S L fun z ↦ ?_
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := C) z
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨x₁, x₂, hx₂, hx⟩ := hfrac x
    obtain ⟨y₁, y₂, hy₂, hy'⟩ := hfrac y
    have hy₁ : algebraMap S L y₁ ≠ 0 := by
      intro h0
      apply (map_ne_zero_iff _ hinjCL).mpr hy0
      rw [hy', h0, zero_div]
    refine ⟨x₁ * y₂, x₂ * y₁, ?_⟩
    rw [hx, hy', map_mul, map_mul]
    exact div_div_div_eq _ _ _ _
  -- finiteness of the normalization of `S` inside `L`
  have hfinS : Module.Finite S (integralClosure S (FractionRing S)) :=
    Langlands.AlgebraicGeometry.NoetherianApproximation.integerFiniteTypeNormalization S
  let e : FractionRing S ≃ₐ[S] L := IsLocalization.algEquiv (nonZeroDivisors S) (FractionRing S) L
  have hfinL : Module.Finite S (integralClosure S L) := by
    rw [← integralClosure_map_algEquiv e]
    exact Module.Finite.equiv (Subalgebra.equivMapOfInjective (integralClosure S (FractionRing S))
      (e : FractionRing S →ₐ[S] L) e.injective).toLinearEquiv
  have : Module.Finite A S := Module.Finite.of_surjective (Algebra.linearMap A S) hsurj
  have hfinAL : Module.Finite A (integralClosure S L) := Module.Finite.trans S _
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  -- embed the integral closure of `A` in `C` into that of `S` in `L`
  let ψ : integralClosure A C →ₗ[A] integralClosure S L :=
    { toFun := fun x ↦ ⟨algebraMap C L (x : C), IsIntegral.tower_top
        (x.2.map (IsScalarTower.toAlgHom A C L))⟩
      map_add' := fun x y ↦ Subtype.ext (map_add (algebraMap C L) (x : C) y)
      map_smul' := fun a x ↦ Subtype.ext (map_smul (IsScalarTower.toAlgHom A C L) a (x : C)) }
  have hψ : Function.Injective ψ := fun x y hxy ↦
    Subtype.ext (hinjCL (congrArg Subtype.val hxy))
  exact Module.Finite.of_injective ψ hψ

variable {X Y : Scheme.{u}} (j : X ⟶ Y)

/-- A monomorphism locally of finite type induces surjections (hence isomorphisms) on residue
fields: the residue field extensions are separable (`j` is formally unramified, its diagonal being
an isomorphism) and purely inseparable (`j` is universally injective). -/
theorem surjective_residueFieldMap [Mono j] [LocallyOfFiniteType j] (x : X) :
    Function.Surjective (j.residueFieldMap x) := by
  let _ : Algebra (Y.residueField (j x)) (X.residueField x) := (j.residueFieldMap x).hom.toAlgebra
  have : Algebra.IsSeparable (Y.residueField (j x)) (X.residueField x) := inferInstance
  have hj : UniversallyInjective j := inferInstance
  have h := ((tfae_universallyInjective j).out 1 3).mp hj
  have : IsPurelyInseparable (Y.residueField (j x)) (X.residueField x) := h.2 x
  exact IsPurelyInseparable.surjective_algebraMap_of_isSeparable _ _

/-- For a monomorphism locally of finite type out of an integral scheme, the stalk map at the
generic point is surjective: the stalk there is a field, equal to its residue field. -/
theorem surjective_stalkMap_genericPoint [Mono j] [LocallyOfFiniteType j] [IsIntegral X] :
    Function.Surjective (j.stalkMap (genericPoint X)) := by
  intro z
  obtain ⟨w, hw⟩ := surjective_residueFieldMap j (genericPoint X) (X.residue _ z)
  obtain ⟨s, rfl⟩ := Y.residue_surjective _ w
  refine ⟨s, (X.residue (genericPoint X)).hom.injective ?_⟩
  rw [← hw, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]

/-- For a monomorphism locally of finite type out of an integral scheme and an affine open `U` of
the target meeting the image, every section of `X` over `j⁻¹ U` is a fraction of pulled back
sections of `Y` over `U`. -/
theorem exists_mul_eq_app [Mono j] [LocallyOfFiniteType j] [IsIntegral X] {U : Y.Opens}
    (hU : IsAffineOpen U) (hη : genericPoint X ∈ j ⁻¹ᵁ U) (c : Γ(X, j ⁻¹ᵁ U)) :
    ∃ a b : Γ(Y, U), j.app U b ≠ 0 ∧ c * j.app U b = j.app U a := by
  let x : U := ⟨j (genericPoint X), hη⟩
  let _ := Y.presheaf.algebra_section_stalk x
  have hloc := hU.isLocalization_stalk x
  obtain ⟨s, hs⟩ := surjective_stalkMap_genericPoint j (X.presheaf.germ _ _ hη c)
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf x).asIdeal.primeCompl s
  have hspec := IsLocalization.mk'_spec (Y.presheaf.stalk x) a b
  have hb : IsUnit (algebraMap Γ(Y, U) (Y.presheaf.stalk x) b) := IsLocalization.map_units _ b
  have hgerm : ∀ t : Γ(Y, U), j.stalkMap (genericPoint X) (algebraMap Γ(Y, U) _ t) =
      X.presheaf.germ _ _ hη (j.app U t) := fun t ↦ Scheme.Hom.germ_stalkMap_apply j U _ hη t
  refine ⟨a, b, ?_, ?_⟩
  · intro h0
    have hu := (hb.map (j.stalkMap (genericPoint X)).hom)
    change IsUnit (j.stalkMap _ (algebraMap _ _ (b : Γ(Y, U)))) at hu
    rw [hgerm, h0, map_zero] at hu
    exact not_isUnit_zero hu
  · apply germ_injective_of_isIntegral X (genericPoint X) hη
    rw [map_mul, ← hgerm, ← hgerm, ← hs, ← map_mul, hspec]

/-- **Finiteness of the normalization.** Let `j : X ⟶ Y` be a quasi-compact monomorphism locally of
finite type out of an integral scheme, such that the ring of sections of `Y` over every affine open is
a finitely generated `ℤ`-algebra. Then the relative normalization of `Y` in `X` is finite over `Y`. -/
theorem isFinite_fromNormalization [Mono j] [LocallyOfFiniteType j] [QuasiCompact j] [IsIntegral X]
    (hY : ∀ U : Y.Opens, IsAffineOpen U → Algebra.FiniteType ℤ Γ(Y, U)) :
    IsFinite j.fromNormalization := by
  refine { toIsAffineHom := inferInstance, finite_app := fun U hU ↦ ?_ }
  let _ := (j.app U).hom.toAlgebra
  rw [j.fromNormalization_app hU, CommRingCat.hom_comp]
  refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (j.normalizationObjIso hU).inv).2) ?_
  rw [CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
  have := hY U hU
  by_cases hη : genericPoint X ∈ j ⁻¹ᵁ U
  · have : Nonempty (j ⁻¹ᵁ U) := ⟨⟨_, hη⟩⟩
    exact finite_integralClosure_of_forall_exists_mul_eq (exists_mul_eq_app j hU hη)
  · have h : j ⁻¹ᵁ U = ⊥ := by
      by_contra h
      refine hη (((genericPoint_spec X).mem_open_set_iff (j ⁻¹ᵁ U).isOpen).mpr ?_)
      rw [Set.univ_inter]
      exact Set.nonempty_iff_ne_empty.mpr fun h' ↦
        h (TopologicalSpace.Opens.ext (h'.trans TopologicalSpace.Opens.coe_bot.symm))
    have : Subsingleton Γ(X, j ⁻¹ᵁ U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty h)
    infer_instance

end Langlands.AlgebraicGeometry.ProperOfFibres
