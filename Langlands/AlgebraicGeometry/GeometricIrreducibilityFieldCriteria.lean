import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! # Field criteria for geometric irreducibility -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Geometric irreducibility descends through a surjective change of base. -/
theorem geometricallyIrreducible_of_surjective_baseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [Surjective g] [h : GeometricallyIrreducible (pullback.snd f g)] :
    GeometricallyIrreducible f := by
  refine ⟨fun K _ k Z a b hZ ↦ ?_⟩
  obtain ⟨z, -⟩ := (pullback.fst k g).surjective default
  let j := (pullback k g).fromSpecResidueField z
  let p := j ≫ pullback.fst k g
  let q := j ≫ pullback.snd k g
  have hpq : p ≫ k = q ≫ g := by
    simp only [p, q, Category.assoc, pullback.condition]
  have : Surjective p := ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have hs : IsPullback (pullback.fst b p ≫ a) (pullback.snd b p) f (q ≫ g) := by
    rw [← hpq]
    exact (IsPullback.of_hasPullback b p).paste_horiz hZ
  let m : pullback b p ⟶ pullback f g :=
    pullback.lift (pullback.fst b p ≫ a) (pullback.snd b p ≫ q)
      (by simpa only [Category.assoc] using hs.w)
  have hm₁ : m ≫ pullback.fst f g = pullback.fst b p ≫ a :=
    pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd f g = pullback.snd b p ≫ q :=
    pullback.lift_snd _ _ _
  have hs' : IsPullback (m ≫ pullback.fst f g) (pullback.snd b p) f (q ≫ g) := by
    rw [hm₁]
    exact hs
  have hc : IsPullback m (pullback.snd b p) (pullback.snd f g) q :=
    IsPullback.of_right hs' hm₂ (IsPullback.of_hasPullback f g)
  have : IrreducibleSpace ↥(pullback b p) :=
    h.geometrically_irreducibleSpace q m (pullback.snd b p) hc
  exact (pullback.fst b p).surjective.irreducibleSpace (pullback.fst b p).continuous

/-- A purely inseparable field extension induces a universally injective spectrum map. -/
theorem universallyInjective_specMap_of_isPurelyInseparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsPurelyInseparable K L] :
    UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  apply ((tfae_universallyInjective _).out 2 1).mp
  intro M _ a b hab
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply IsPurelyInseparable.injective_comp_algebraMap K L M
  have hab' : CommRingCat.ofHom (algebraMap K L) ≫ a =
      CommRingCat.ofHom (algebraMap K L) ≫ b :=
    Spec.map_injective (by simpa only [Spec.map_comp] using hab)
  exact congrArg CommRingCat.Hom.hom hab'

/-- The scalar extension by a purely inseparable field extension has the same topology. -/
def purelyInseparableBaseChangeHomeomorph
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsPurelyInseparable K L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) :
    ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≃ₜ X := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have : UniversallyInjective g :=
    universallyInjective_specMap_of_isPurelyInseparable K L
  have : IsIntegralHom g :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  have : Surjective g := ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have hi : Function.Injective (pullback.fst f g) :=
    UniversallyInjective.universally_injective _ _ _
      (IsPullback.of_hasPullback f g)
  have hs := (pullback.fst f g).surjective
  exact
    (Equiv.ofBijective _ ⟨hi, hs⟩).toHomeomorphOfContinuousClosed
      (pullback.fst f g).continuous (pullback.fst f g).isClosedMap

/-- Purely inseparable scalar extension preserves irreducibility. -/
theorem irreducibleSpace_pullback_of_isPurelyInseparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsPurelyInseparable K L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IrreducibleSpace X] :
    IrreducibleSpace
      ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :=
  (purelyInseparableBaseChangeHomeomorph K L f).irreducibleSpace_iff.mpr inferInstance

/-- Over a separably closed field, ordinary irreducibility implies geometric irreducibility. -/
theorem geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed
    {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IrreducibleSpace X] :
    GeometricallyIrreducible f := by
  let L := AlgebraicClosure K
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have : Surjective g := ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : IrreducibleSpace ↥(pullback f g) :=
    irreducibleSpace_pullback_of_isPurelyInseparable K L f
  have : GeometricallyIrreducible (pullback.snd f g) :=
    GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed _
  exact geometricallyIrreducible_of_surjective_baseChange f g

end Langlands.AlgebraicGeometry
