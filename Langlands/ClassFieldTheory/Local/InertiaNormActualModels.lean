import Langlands.ClassFieldTheory.Local.InertiaNormFieldModels

/-! Totally ramified local models of an arbitrary finite tower above inertia. -/
noncomputable section
namespace Langlands.ClassFieldTheory.Local.InertiaNormActualModels

open Langlands Langlands.LocalClassField IntermediateField
open Langlands.ClassFieldTheory.Local.InertiaNormDescent Langlands.ClassFieldTheory.Local.InertiaNormFieldModels
universe u

/-- Realize a finite lower model in the original closure, then use a compatible
closure map to identify the image of its compositum with the inertia field. -/
theorem lower_model
    (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (U p F) E] [Algebra E L] [Algebra (U p F) L]
    [IsScalarTower (U p F) E L]
    [Algebra F.Carrier E] [Algebra F.Carrier L]
    [IsScalarTower F.Carrier (U p F) E]
    [IsScalarTower F.Carrier (U p F) L]
    [IsScalarTower F.Carrier E L]
    (B : IntermediateField F.Carrier E) [FiniteDimensional F.Carrier B]
    (j₀ : L →ₐ[U p F] AlgebraicClosure F.Carrier)
    (hgen : IntermediateField.adjoin (U p F) (B : Set E) = ⊤) :
    ∃ (D : FiniteIntermediateExtension F.Carrier) (eB : B ≃ₐ[F.Carrier] D.field),
      letI : Algebra D.field E := (B.val.toRingHom.comp eB.symm.toRingEquiv.toRingHom).toAlgebra
      letI : Algebra D.field L := ((algebraMap E L).comp
        (algebraMap D.field E)).toAlgebra
      letI : IsScalarTower D.field E L := IsScalarTower.of_algebraMap_eq' rfl
      ∃ j : L →ₐ[D.field] AlgebraicClosure D.field,
        (j.comp (IsScalarTower.toAlgHom D.field E L)).fieldRange =
          U p (D.asPadicField (p := p)) := by
  let jB : B →ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
    ((j₀.restrictScalars F.Carrier).comp (IsScalarTower.toAlgHom F.Carrier E L)).comp B.val
  let D : FiniteIntermediateExtension F.Carrier :=
    ⟨jB.fieldRange, Module.Finite.equiv jB.equivFieldRange.toLinearEquiv⟩
  let eB : B ≃ₐ[F.Carrier] D.field := jB.equivFieldRange
  refine ⟨D, eB, ?_⟩
  let : Algebra D.field E := (B.val.toRingHom.comp eB.symm.toRingEquiv.toRingHom).toAlgebra
  let : Algebra D.field L := ((algebraMap E L).comp (algebraMap D.field E)).toAlgebra
  let : IsScalarTower D.field E L := IsScalarTower.of_algebraMap_eq' rfl
  have hB (b : B) : algebraMap D.field E (eB b) = (b : E) := by
    change ((eB.symm (eB b) : B) : E) = _
    rw [eB.symm_apply_apply]
  let j₁ : L →ₐ[D.field] AlgebraicClosure F.Carrier :=
    { j₀.toRingHom with
      commutes' := by
        intro d
        obtain ⟨b, rfl⟩ := eB.surjective d
        change j₀ (algebraMap E L (algebraMap D.field E (eB b))) = _
        rw [hB]
        rfl }
  let : Algebra F.Carrier (AlgebraicClosure D.field) :=
    ((algebraMap D.field (AlgebraicClosure D.field)).comp
      (algebraMap F.Carrier D.field)).toAlgebra
  let : SMul F.Carrier (AlgebraicClosure D.field) :=
    (inferInstance : Algebra F.Carrier (AlgebraicClosure D.field)).toSMul
  let : SMul D.field (AlgebraicClosure D.field) :=
    (inferInstance : Algebra D.field (AlgebraicClosure D.field)).toSMul
  let : IsScalarTower F.Carrier D.field (AlgebraicClosure D.field) :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨jF, hjF⟩ := exists_compatible_closure_map F.Carrier D
  let j₂ : AlgebraicClosure F.Carrier →ₐ[D.field] AlgebraicClosure D.field :=
    { jF.toRingHom with commutes' := hjF }
  let j := j₂.comp j₁
  refine ⟨j, fieldRange_eq_inertia p F D E jF hjF
    (j.comp (IsScalarTower.toAlgHom D.field E L)) ?_ ?_⟩
  · intro x
    change jF (j₀ (algebraMap E L (algebraMap (U p F) E x))) = jF x
    rw [← IsScalarTower.algebraMap_apply (U p F) E L, j₀.commutes]
    rfl
  · have hrange : Set.range (algebraMap D.field E) = (B : Set E) := by
      ext x
      constructor
      · rintro ⟨d, rfl⟩
        exact (eB.symm d).2
      · intro hx
        exact ⟨eB ⟨x, hx⟩, hB ⟨x, hx⟩⟩
    rw [hrange]
    exact hgen

/-- The upper image is the compositum of the lower image with the finite model. -/
theorem upper_range
    (K E L Ω : Type u) [Field K] [Field E] [Field L] [Field Ω]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [Algebra K Ω] (C : IntermediateField K L) (j : L →ₐ[K] Ω)
    (hgen : IntermediateField.adjoin E (C : Set L) = ⊤) :
    j.fieldRange = (j.comp (IsScalarTower.toAlgHom K E L)).fieldRange ⊔ C.map j := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ IntermediateField.adjoin E (C : Set L) := by
      rw [hgen]; trivial
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      exact (show C.map j ≤
        (j.comp (IsScalarTower.toAlgHom K E L)).fieldRange ⊔ C.map j from le_sup_right)
        ⟨x, hx, rfl⟩
    | algebraMap x =>
      exact (show (j.comp (IsScalarTower.toAlgHom K E L)).fieldRange ≤
        (j.comp (IsScalarTower.toAlgHom K E L)).fieldRange ⊔ C.map j from le_sup_left)
        ⟨x, rfl⟩
    | add x y _ _ hx hy => simpa only [map_add] using
        IntermediateField.add_mem _ hx hy
    | mul x y _ _ hx hy => simpa only [map_mul] using
        IntermediateField.mul_mem _ hx hy
    | inv x _ hx => simpa only [map_inv₀] using IntermediateField.inv_mem _ hx
  · apply sup_le
    · rintro _ ⟨x, rfl⟩
      exact ⟨algebraMap E L x, rfl⟩
    · rintro _ ⟨x, _, rfl⟩
      exact ⟨x, rfl⟩

/-- A finite disjoint Galois model above the inertia image gives the exact
commuting presentation of the original extension as an inertia compositum. -/
theorem upper_model
    (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E L : Type u) [Field E] [Field L]
    [Algebra F.Carrier E] [Algebra F.Carrier L] [Algebra E L]
    [IsScalarTower F.Carrier E L]
    (C : IntermediateField F.Carrier L) [FiniteDimensional F.Carrier C]
    [IsGalois F.Carrier C]
    (j : L →ₐ[F.Carrier] AlgebraicClosure F.Carrier)
    (hj : (j.comp (IsScalarTower.toAlgHom F.Carrier E L)).fieldRange = U p F)
    (hdisj : C.LinearDisjoint E)
    (hgen : IntermediateField.adjoin E (C : Set L) = ⊤) :
    ∃ D : FiniteIntermediateExtension F.Carrier,
      IsGalois F.Carrier D.field ∧
      D.field.LinearDisjoint (U p F) ∧
      (D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
        Module.finrank F.Carrier D.field * F.canonicalTopologicalData.ramificationIndex ∧
      ∃ (eE : E ≃+* U p F) (eL : L ≃+* (U p F ⊔ D.field :
          IntermediateField F.Carrier (AlgebraicClosure F.Carrier))),
        letI : Algebra (U p F) (U p F ⊔ D.field :
            IntermediateField F.Carrier (AlgebraicClosure F.Carrier)) :=
          (IntermediateField.inclusion le_sup_left).toAlgebra
        (algebraMap (U p F) (U p F ⊔ D.field :
          IntermediateField F.Carrier (AlgebraicClosure F.Carrier))).comp eE.toRingHom =
          eL.toRingHom.comp (algebraMap E L) := by
  let D : FiniteIntermediateExtension F.Carrier :=
    ⟨C.map j, Module.Finite.equiv (IntermediateField.equivMap C j).toLinearEquiv⟩
  have hGal : IsGalois F.Carrier D.field :=
    IsGalois.of_algEquiv (IntermediateField.equivMap C j)
  have hram := total_ramification_of_image_inertia p F E L C j hj hdisj
  have hdeg := (IntermediateField.equivMap C j).toLinearEquiv.finrank_eq
  have htop : j.fieldRange = U p F ⊔ D.field := by
    rw [upper_range F.Carrier E L (AlgebraicClosure F.Carrier) C j hgen, hj]
  let jE := j.comp (IsScalarTower.toAlgHom F.Carrier E L)
  let eE : E ≃+* U p F :=
    (jE.equivFieldRange.trans (IntermediateField.equivOfEq hj)).toRingEquiv
  let eL : L ≃+* (U p F ⊔ D.field :
      IntermediateField F.Carrier (AlgebraicClosure F.Carrier)) :=
    (j.equivFieldRange.trans (IntermediateField.equivOfEq htop)).toRingEquiv
  have hdisjD : D.field.LinearDisjoint (U p F) := by
    rw [← hj]
    exact map_disjoint_fieldRange F.Carrier E L (AlgebraicClosure F.Carrier) C j hdisj
  refine ⟨D, hGal, hdisjD, ?_, eE, eL, ?_⟩
  · simpa only [hdeg] using hram
  · ext x
    rfl

set_option maxHeartbeats 800000 in
/-- The original abstract tower has a compatible totally ramified local model. -/
theorem actual_models
    (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (U p F) E] [FiniteDimensional (U p F) E]
    [Algebra E L] [FiniteDimensional E L] [IsGalois E L] :
    ∃ (F' : PadicField.{u} p) (D : FiniteIntermediateExtension F'.Carrier),
      IsGalois F'.Carrier D.field ∧
      D.field.LinearDisjoint (U p F') ∧
      (D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
        Module.finrank F'.Carrier D.field * F'.canonicalTopologicalData.ramificationIndex ∧
      ∃ (eE : E ≃+* U p F') (eL : L ≃+* (U p F' ⊔ D.field :
          IntermediateField F'.Carrier (AlgebraicClosure F'.Carrier))),
        letI : Algebra (U p F') (U p F' ⊔ D.field :
            IntermediateField F'.Carrier (AlgebraicClosure F'.Carrier)) :=
          (IntermediateField.inclusion le_sup_left).toAlgebra
        (algebraMap (U p F') (U p F' ⊔ D.field :
          IntermediateField F'.Carrier (AlgebraicClosure F'.Carrier))).comp eE.toRingHom =
          eL.toRingHom.comp (algebraMap E L) := by
  let : Algebra (U p F) L := ((algebraMap E L).comp (algebraMap (U p F) E)).toAlgebra
  let : IsScalarTower (U p F) E L := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (U p F) L := Module.Finite.trans E L
  let : Algebra F.Carrier E :=
    ((algebraMap (U p F) E).comp (algebraMap F.Carrier (U p F))).toAlgebra
  let : Algebra F.Carrier L :=
    ((algebraMap E L).comp (algebraMap F.Carrier E)).toAlgebra
  let : IsScalarTower F.Carrier (U p F) E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F.Carrier (U p F) L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F.Carrier E L := IsScalarTower.of_algebraMap_eq' rfl
  let j₀ : L →ₐ[U p F] AlgebraicClosure F.Carrier := IsAlgClosed.lift
  obtain ⟨i, _, hmodels⟩ := finite_models p F E L (Classical.choice inferInstance) ∅ ∅
  let A := stageField p F i
  let : Algebra F.Carrier A := stageAlgebra p F i
  let : FiniteDimensional F.Carrier A := stage_finite p F i
  let : Algebra A (U p F) := Algebra.ofSubsemiring A
  let : Algebra A E := Algebra.ofSubsemiring A
  let : Algebra A L := Algebra.ofSubsemiring A
  let : IsScalarTower A (U p F) E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A (U p F) L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A E L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F.Carrier A E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨B, hmodels⟩ := hmodels
  let : Algebra A B := B.toSubalgebra.algebra
  let : Algebra B L := Algebra.ofSubsemiring B
  let : IsScalarTower B E L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨C, hmodels⟩ := hmodels
  let : Algebra B C := C.toSubalgebra.algebra
  let : Algebra A C := IntermediateField.algebra' C
  let : IsScalarTower A C L := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨hAB, _, _, hBC, hGal, _, _, _, _, hBgen, _, _, hdisj, hCgen, _⟩ := hmodels
  let : FiniteDimensional A B := hAB
  let : FiniteDimensional B C := hBC
  let : IsGalois B C := hGal
  let B₀ := B.restrictScalars F.Carrier
  let : Algebra F.Carrier B := B₀.toSubalgebra.algebra
  let : IsScalarTower F.Carrier A B := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional F.Carrier B₀ := Module.Finite.trans A B
  obtain ⟨D₀, eB, j, hj⟩ := lower_model p F E L B₀ j₀ hBgen
  let : Algebra D₀.field E := (B₀.val.toRingHom.comp eB.symm.toRingEquiv.toRingHom).toAlgebra
  let : Algebra D₀.field L := ((algebraMap E L).comp (algebraMap D₀.field E)).toAlgebra
  let : IsScalarTower D₀.field E L := IsScalarTower.of_algebraMap_eq' rfl
  let e : B ≃+* D₀.field := eB.toRingEquiv
  have he (b : B) : algebraMap D₀.field L (e b) = algebraMap B L b := by
    exact congrArg (fun x : B₀ => algebraMap E L x.1)
      (eB.symm_apply_apply (show B₀ from b))
  let C₀ := rebaseField e he C
  let : FiniteDimensional D₀.field C₀ := rebaseField_finite e he C
  let : IsGalois D₀.field C₀ := rebaseField_galois e he C
  have hdisj₀ : C₀.LinearDisjoint E := rebaseField_disjoint e he C hdisj
  exact ⟨D₀.asPadicField (p := p), upper_model p (D₀.asPadicField (p := p))
    E L C₀ j hj hdisj₀ hCgen⟩

end Langlands.ClassFieldTheory.Local.InertiaNormActualModels
