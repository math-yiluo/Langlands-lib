import Langlands.ClassFieldTheory.Local.InertiaNormDescent
import Langlands.Galois.Local.InertiaFixedFieldBaseChangeProof
import Langlands.Galois.Local.InertiaDisjointRamificationProof

/-! Compatible closure, base-change and disjointness adapters for finite local models. -/
noncomputable section

namespace Langlands.ClassFieldTheory.Local.InertiaNormFieldModels

universe u v w z

open IntermediateField Module

/-- The same compositum may be viewed over either of its two fields. -/
theorem fieldRange_eq_adjoin
    (B : Type u) (U : Type v) (E : Type w) (Ω : Type z)
    [Field B] [Field U] [Field E] [Field Ω]
    [Algebra B E] [Algebra U E] [Algebra B Ω]
    (j : E →ₐ[B] Ω)
    (h : IntermediateField.adjoin U (Set.range (algebraMap B E)) = ⊤) :
    j.fieldRange = IntermediateField.adjoin B
      (Set.range fun x : U => j (algebraMap U E x)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ IntermediateField.adjoin U (Set.range (algebraMap B E)) := by
      rw [h]; trivial
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact (j.commutes b).symm ▸ (IntermediateField.adjoin B _).algebraMap_mem b
    | algebraMap x => exact subset_adjoin B _ ⟨x, rfl⟩
    | add x y _ _ hx hy => simpa only [map_add] using
        (IntermediateField.adjoin B _).add_mem hx hy
    | mul x y _ _ hx hy => simpa only [map_mul] using
        (IntermediateField.adjoin B _).mul_mem hx hy
    | inv x _ hx => simpa only [map_inv₀] using
        (IntermediateField.adjoin B _).inv_mem hx
  · apply adjoin_le_iff.mpr
    rintro _ ⟨x, rfl⟩
    exact ⟨algebraMap U E x, rfl⟩

open Langlands Langlands.LocalClassField

/-- A closure embedding over an actual finite intermediate field restricts to
the required commuting embedding over the original base. -/
theorem exists_compatible_closure_map
    (K : Type u) [Field K] (D : FiniteIntermediateExtension K) :
    letI : Algebra K (AlgebraicClosure D.field) :=
      ((algebraMap D.field (AlgebraicClosure D.field)).comp
        (algebraMap K D.field)).toAlgebra
    letI : SMul K (AlgebraicClosure D.field) :=
      (inferInstance : Algebra K (AlgebraicClosure D.field)).toSMul
    letI : SMul D.field (AlgebraicClosure D.field) :=
      (inferInstance : Algebra D.field (AlgebraicClosure D.field)).toSMul
    letI : IsScalarTower K D.field (AlgebraicClosure D.field) :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∃ j : AlgebraicClosure K →ₐ[K] AlgebraicClosure D.field,
      ∀ a : D.field, j a = algebraMap D.field (AlgebraicClosure D.field) a := by
  let : Algebra K (AlgebraicClosure D.field) :=
    ((algebraMap D.field (AlgebraicClosure D.field)).comp
      (algebraMap K D.field)).toAlgebra
  let : SMul K (AlgebraicClosure D.field) :=
    (inferInstance : Algebra K (AlgebraicClosure D.field)).toSMul
  let : SMul D.field (AlgebraicClosure D.field) :=
    (inferInstance : Algebra D.field (AlgebraicClosure D.field)).toSMul
  let : IsScalarTower K D.field (AlgebraicClosure D.field) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic D.field (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) D.field
  let j : AlgebraicClosure K →ₐ[D.field] AlgebraicClosure D.field := IsAlgClosed.lift
  exact ⟨j.restrictScalars K, fun a => j.commutes a⟩

/-- The full base-change theorem identifies the image of a descended compositum
with the actual inertia fixed field, once the two embeddings commute. -/
theorem fieldRange_eq_inertia
    (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (D : FiniteIntermediateExtension F.Carrier)
    (E : Type u) [Field E]
    [Algebra (Langlands.ClassFieldTheory.Local.InertiaNormDescent.U p F) E] [Algebra D.field E] :
    letI : Algebra F.Carrier (AlgebraicClosure D.field) :=
      ((algebraMap D.field (AlgebraicClosure D.field)).comp
        (algebraMap F.Carrier D.field)).toAlgebra
    letI : SMul F.Carrier (AlgebraicClosure D.field) :=
      (inferInstance : Algebra F.Carrier (AlgebraicClosure D.field)).toSMul
    letI : SMul D.field (AlgebraicClosure D.field) :=
      (inferInstance : Algebra D.field (AlgebraicClosure D.field)).toSMul
    letI : IsScalarTower F.Carrier D.field (AlgebraicClosure D.field) :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ (jF : AlgebraicClosure F.Carrier →ₐ[F.Carrier] AlgebraicClosure D.field),
      (∀ a : D.field, jF a = algebraMap D.field (AlgebraicClosure D.field) a) →
      ∀ (j : E →ₐ[D.field] AlgebraicClosure D.field),
        (∀ x : Langlands.ClassFieldTheory.Local.InertiaNormDescent.U p F,
          j (algebraMap (Langlands.ClassFieldTheory.Local.InertiaNormDescent.U p F) E x) = jF x) →
        IntermediateField.adjoin (Langlands.ClassFieldTheory.Local.InertiaNormDescent.U p F)
          (Set.range (algebraMap D.field E)) = ⊤ →
        j.fieldRange = Langlands.ClassFieldTheory.Local.InertiaNormDescent.U p (D.asPadicField (p := p)) := by
  let : Algebra F.Carrier (AlgebraicClosure D.field) :=
    ((algebraMap D.field (AlgebraicClosure D.field)).comp
      (algebraMap F.Carrier D.field)).toAlgebra
  let : SMul F.Carrier (AlgebraicClosure D.field) :=
    (inferInstance : Algebra F.Carrier (AlgebraicClosure D.field)).toSMul
  let : SMul D.field (AlgebraicClosure D.field) :=
    (inferInstance : Algebra D.field (AlgebraicClosure D.field)).toSMul
  let : IsScalarTower F.Carrier D.field (AlgebraicClosure D.field) :=
    IsScalarTower.of_algebraMap_eq' rfl
  intro jF hjF j hj hgen
  have hrange :
      (Set.range fun x : Langlands.ClassFieldTheory.Local.InertiaNormDescent.U p F =>
        j (algebraMap (Langlands.ClassFieldTheory.Local.InertiaNormDescent.U p F) E x)) =
      jF '' (Langlands.ClassFieldTheory.Local.InertiaNormDescent.U p F : Set (AlgebraicClosure F.Carrier)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, (hj x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hj ⟨x, hx⟩⟩
  rw [fieldRange_eq_adjoin D.field (Langlands.ClassFieldTheory.Local.InertiaNormDescent.U p F) E
    (AlgebraicClosure D.field) j hgen, hrange]
  exact (PadicField.inertiaFixedFieldBaseChange p F D jF hjF).symm

/-- Transport both sides of the descended disjointness through one embedding. -/
theorem map_disjoint_fieldRange
    (K : Type u) (E : Type v) (L : Type w) (Ω : Type z)
    [Field K] [Field E] [Field L] [Field Ω]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [Algebra K Ω] (C : IntermediateField K L) (j : L →ₐ[K] Ω)
    (h : C.LinearDisjoint E) :
    (C.map j).LinearDisjoint
      (j.comp (IsScalarTower.toAlgHom K E L)).fieldRange := by
  apply IntermediateField.linearDisjoint_iff'.mpr
  rw [IntermediateField.toSubalgebra_map, AlgHom.fieldRange_toSubalgebra,
    AlgHom.range_comp]
  exact Subalgebra.LinearDisjoint.map h j j.injective

/-- Change the base presentation while retaining the identical subset of the
ambient field and its field operations. -/
def rebaseField
    {B B' L : Type*} [Field B] [Field B'] [Field L]
    [Algebra B L] [Algebra B' L] (e : B ≃+* B')
    (he : ∀ b, algebraMap B' L (e b) = algebraMap B L b)
    (C : IntermediateField B L) : IntermediateField B' L where
  __ := C.toSubfield
  algebraMap_mem' b := by
    rw [← e.apply_symm_apply b, he]
    exact C.algebraMap_mem (e.symm b)

theorem rebaseField_finite
    {B B' L : Type*} [Field B] [Field B'] [Field L]
    [Algebra B L] [Algebra B' L] (e : B ≃+* B')
    (he : ∀ b, algebraMap B' L (e b) = algebraMap B L b)
    (C : IntermediateField B L) [FiniteDimensional B C] :
    FiniteDimensional B' (rebaseField e he C) := by
  let : Algebra B' C := (rebaseField e he C).toSubalgebra.algebra
  have hc : (algebraMap B' (rebaseField e he C)).comp e.toRingHom =
      (RingEquiv.refl C).toRingHom.comp (algebraMap B C) := by
    ext b
    exact he b
  exact Module.Finite.of_equiv_equiv e (RingEquiv.refl C) hc

theorem rebaseField_galois
    {B B' L : Type*} [Field B] [Field B'] [Field L]
    [Algebra B L] [Algebra B' L] (e : B ≃+* B')
    (he : ∀ b, algebraMap B' L (e b) = algebraMap B L b)
    (C : IntermediateField B L) [IsGalois B C] :
    IsGalois B' (rebaseField e he C) := by
  let : Algebra B' C := (rebaseField e he C).toSubalgebra.algebra
  apply IsGalois.of_equiv_equiv (F := B) (E := C)
    (f := e) (g := RingEquiv.refl C)
  ext b
  exact he b

theorem rebaseField_disjoint
    {B B' E L : Type*} [Field B] [Field B'] [Field E] [Field L]
    [Algebra B E] [Algebra B L] [Algebra B' E] [Algebra B' L] [Algebra E L]
    [IsScalarTower B E L] [IsScalarTower B' E L]
    (e : B ≃+* B') (he : ∀ b, algebraMap B' L (e b) = algebraMap B L b)
    (C : IntermediateField B L) (h : C.LinearDisjoint E) :
    (rebaseField e he C).LinearDisjoint E := by
  let b := Basis.ofVectorSpace B C
  let : Algebra B' C := (rebaseField e he C).toSubalgebra.algebra
  have hsmul (c : B) (x : C) : e c • x = c • x := by
    simp only [Algebra.smul_def]
    apply Subtype.ext
    change algebraMap B' L (e c) * (x : L) = algebraMap B L c * (x : L)
    rw [he]
  let b' : Basis (Basis.ofVectorSpaceIndex B C) B' (rebaseField e he C) :=
    b.mapCoeffs e hsmul
  apply IntermediateField.LinearDisjoint.of_basis_left b'
  have hi := h.linearIndependent_left b.linearIndependent
  have hfun : (rebaseField e he C).val ∘ b' = C.val ∘ b := by
    funext i
    exact congrArg (fun x : C => (x : L)) (b.mapCoeffs_apply e hsmul i)
  rw [hfun]
  exact hi

/-- Once the lower image is the actual inertia field, the upper descended model
is totally ramified by the published disjointness theorem. -/
theorem total_ramification_of_image_inertia
    (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E L : Type u) [Field E] [Field L]
    [Algebra F.Carrier E] [Algebra F.Carrier L] [Algebra E L]
    [IsScalarTower F.Carrier E L]
    (C : IntermediateField F.Carrier L) [FiniteDimensional F.Carrier C]
    (j : L →ₐ[F.Carrier] AlgebraicClosure F.Carrier)
    (hj : (j.comp (IsScalarTower.toAlgHom F.Carrier E L)).fieldRange =
      Langlands.ClassFieldTheory.Local.InertiaNormDescent.U p F)
    (h : C.LinearDisjoint E) :
    let D : FiniteIntermediateExtension F.Carrier :=
      ⟨C.map j, Module.Finite.equiv (IntermediateField.equivMap C j).toLinearEquiv⟩
    (D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier C * F.canonicalTopologicalData.ramificationIndex := by
  let D : FiniteIntermediateExtension F.Carrier :=
    ⟨C.map j, Module.Finite.equiv (IntermediateField.equivMap C j).toLinearEquiv⟩
  have hdisj : D.field.LinearDisjoint (Langlands.ClassFieldTheory.Local.InertiaNormDescent.U p F) := by
    rw [← hj]
    exact map_disjoint_fieldRange F.Carrier E L (AlgebraicClosure F.Carrier) C j h
  have hram := PadicField.inertiaDisjointTotallyRamified p F D hdisj
  have hdeg : Module.finrank F.Carrier C = Module.finrank F.Carrier D.field :=
    (IntermediateField.equivMap C j).toLinearEquiv.finrank_eq
  simpa only [← hdeg] using hram

end Langlands.ClassFieldTheory.Local.InertiaNormFieldModels
