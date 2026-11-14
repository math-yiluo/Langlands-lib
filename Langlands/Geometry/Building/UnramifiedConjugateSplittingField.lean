import Mathlib.FieldTheory.Galois.Basic

/-! # Conjugating embedded splitting fields -/

noncomputable section

universe u

namespace Langlands.Geometry.Building

namespace FieldIsoSquare

variable {k K A B : Type u} [Field k] [Field K] [Field A] [Field B]
  [Algebra k A] [Algebra K B]

variable (e : k ≃+* K) (f : A ≃+* B)
  (hcomm : (algebraMap K B).comp e.toRingHom =
    f.toRingHom.comp (algebraMap k A))
  (L : IntermediateField k A)

/-- The image of an intermediate field under a compatible field isomorphism. -/
def conjugateIntermediateField : IntermediateField K B :=
  (L.toSubfield.map f.toRingHom).toIntermediateField fun x => by
    apply Subfield.mem_map.mpr
    refine ⟨algebraMap k A (e.symm x), L.algebraMap_mem _, ?_⟩
    have h := congrArg (fun g : k →+* B => g (e.symm x)) hcomm
    change f (algebraMap k A (e.symm x)) = algebraMap K B x
    change algebraMap K B (e (e.symm x)) = f (algebraMap k A (e.symm x)) at h
    simpa only [RingEquiv.apply_symm_apply] using h.symm

/-- Restriction of the ambient field isomorphism to the image field. -/
def conjugateIntermediateFieldEquiv :
    L ≃+* conjugateIntermediateField e f hcomm L := by
  let g : L →+* conjugateIntermediateField e f hcomm L := {
    toFun := fun x => ⟨f (x : A), Subfield.mem_map.mpr ⟨x, x.property, rfl⟩⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' := fun x y => Subtype.ext (map_mul f (x : A) (y : A))
    map_zero' := Subtype.ext (map_zero f)
    map_add' := fun x y => Subtype.ext (map_add f (x : A) (y : A)) }
  apply RingEquiv.ofBijective g
  constructor
  · intro x y h
    exact Subtype.ext (f.injective (congrArg Subtype.val h))
  · intro y
    obtain ⟨x, hx, hxy⟩ := Subfield.mem_map.mp y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[simp]
theorem conjugateIntermediateFieldEquiv_coe (x : L) :
    (conjugateIntermediateFieldEquiv e f hcomm L x : B) = f (x : A) := rfl

/-- The restricted isomorphism is semilinear over the prescribed base map. -/
theorem conjugateIntermediateFieldEquiv_commutes :
    (algebraMap K (conjugateIntermediateField e f hcomm L)).comp e.toRingHom =
      (conjugateIntermediateFieldEquiv e f hcomm L).toRingHom.comp
        (algebraMap k L) := by
  ext x
  exact congrArg (fun g : k →+* B => g x) hcomm

instance conjugateIntermediateField_finiteDimensional [FiniteDimensional k L] :
    FiniteDimensional K (conjugateIntermediateField e f hcomm L) :=
  Module.Finite.of_equiv_equiv e (conjugateIntermediateFieldEquiv e f hcomm L)
    (conjugateIntermediateFieldEquiv_commutes e f hcomm L)

instance conjugateIntermediateField_isGalois [IsGalois k L] :
    IsGalois K (conjugateIntermediateField e f hcomm L) :=
  IsGalois.of_equiv_equiv (F := k) (E := L) (f := e)
    (g := conjugateIntermediateFieldEquiv e f hcomm L)
    (conjugateIntermediateFieldEquiv_commutes e f hcomm L)

end FieldIsoSquare

end Langlands.Geometry.Building
