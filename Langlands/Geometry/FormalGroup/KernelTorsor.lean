import Langlands.Geometry.FormalGroup.KernelQuotient
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.RingTheory.RingHom.Flat

/-! # Translation of a represented kernel fibre -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw.Hom
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {f : Hom M P} {g : Hom N M} {h : Hom N P}

namespace KernelTorsor

variable (C : FiniteKernelModel h) (K : FiniteKernelModel f) (hfg : f.comp g = h)

include hfg in
/-- An actual zero of g is also an actual zero of its composite with f. -/
theorem kernel_le (A : CommAlgCat.{v} R) (x : g.kernelPoints A) :
    h.onAlgebraPoints x.val = 0 := by
  rw [← hfg, onAlgebraPoints_comp, x.property, map_zero]

/-- The quotient corepresentation of the kernel of g inside the kernel of h. -/
def quotientRepresents :
    g.kernelSetFunctor.CorepresentableBy (KernelQuotient.coordinateAlgebra C g) :=
  KernelQuotient.represents C g (kernel_le hfg)

/-- The map of coordinate algebras induced by g on the represented kernels. -/
def imageMap : K.coordinateAlgebra ⟶ C.coordinateAlgebra :=
  K.represents.homEquiv.symm ⟨g.onAlgebraPoints C.universalPoint.val, by
    change f.onAlgebraPoints (g.onAlgebraPoints C.universalPoint.val) = 0
    rw [← onAlgebraPoints_comp, hfg]
    exact C.universalPoint.property⟩

/-- The image coordinate map evaluates to the actual point map induced by g. -/
theorem imageMap_apply {A : CommAlgCat.{v} R} (c : C.coordinateAlgebra ⟶ A) :
    (K.represents.homEquiv (imageMap C K hfg ≫ c)).val =
      g.onAlgebraPoints (C.represents.homEquiv c).val := by
  rw [K.represents.homEquiv_comp]
  change M.algebraMapPoints c.hom
    (K.represents.homEquiv
      (K.represents.homEquiv.symm
        ⟨g.onAlgebraPoints C.universalPoint.val, _⟩)).val = _
  erw [Equiv.apply_symm_apply]
  rw [g.onAlgebraPoints_natural, C.universalPoint_map]

variable {B : CommAlgCat.{v} R} (β : K.coordinateAlgebra ⟶ B)
variable (η : h.kernelPoints B)
variable (hη : g.onAlgebraPoints η.val = (K.represents.homEquiv β).val)

/-- A kernel point of g translates by the selected lift into a kernel point of h. -/
def translatePoint {A : CommAlgCat.{v} R}
    (d : KernelQuotient.coordinateAlgebra C g ⟶ A) (b : B ⟶ A) : h.kernelPoints A :=
  ⟨((quotientRepresents C hfg).homEquiv d).val + N.algebraMapPoints b.hom η.val, by
    change h.onAlgebraPoints
      (((quotientRepresents C hfg).homEquiv d).val + N.algebraMapPoints b.hom η.val) = 0
    erw [map_add, kernel_le hfg A ((quotientRepresents C hfg).homEquiv d),
      ← h.onAlgebraPoints_natural, η.property, map_zero, add_zero]⟩

/-- The corresponding algebra map into the represented h-kernel. -/
def translateMap {A : CommAlgCat.{v} R}
    (d : KernelQuotient.coordinateAlgebra C g ⟶ A) (b : B ⟶ A) :
    C.coordinateAlgebra ⟶ A :=
  C.represents.homEquiv.symm (translatePoint C hfg η d b)

/-- Translation commutes with actual coefficient restrictions. -/
theorem translateMap_comp {A A' : CommAlgCat.{v} R}
    (d : KernelQuotient.coordinateAlgebra C g ⟶ A) (b : B ⟶ A) (ψ : A ⟶ A') :
    translateMap C hfg η d b ≫ ψ = translateMap C hfg η (d ≫ ψ) (b ≫ ψ) := by
  apply C.represents.homEquiv.injective
  rw [C.represents.homEquiv_comp]
  change h.kernelMap ψ
    (C.represents.homEquiv (C.represents.homEquiv.symm (translatePoint C hfg η d b))) = _
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply Subtype.ext
  change N.algebraMapPoints ψ.hom
    (((quotientRepresents C hfg).homEquiv d).val + N.algebraMapPoints b.hom η.val) =
      ((quotientRepresents C hfg).homEquiv (d ≫ ψ)).val +
        N.algebraMapPoints (b ≫ ψ).hom η.val
  erw [map_add, (quotientRepresents C hfg).homEquiv_comp]
  change _ = N.algebraMapPoints ψ.hom ((quotientRepresents C hfg).homEquiv d).val +
    N.algebraMapPoints (ψ.hom.comp b.hom) η.val
  rw [N.algebraMapPoints_comp]

include hη in
/-- Translation identifies the fibre over β with the zero fibre. -/
theorem imageMap_translateMap {A : CommAlgCat.{v} R}
    (d : KernelQuotient.coordinateAlgebra C g ⟶ A) (b : B ⟶ A) :
    imageMap C K hfg ≫ translateMap C hfg η d b = β ≫ b := by
  apply K.represents.homEquiv.injective
  apply Subtype.ext
  rw [imageMap_apply, K.represents.homEquiv_comp]
  change g.onAlgebraPoints
    (C.represents.homEquiv (C.represents.homEquiv.symm (translatePoint C hfg η d b))).val = _
  erw [Equiv.apply_symm_apply]
  change g.onAlgebraPoints
    (((quotientRepresents C hfg).homEquiv d).val + N.algebraMapPoints b.hom η.val) = _
  rw [map_add, ((quotientRepresents C hfg).homEquiv d).property,
    zero_add, ← g.onAlgebraPoints_natural, hη]
  rfl

/-- Translation by a fixed lift is injective on maps from the zero fibre. -/
theorem translateMap_injective {A : CommAlgCat.{v} R} (b : B ⟶ A) :
    Function.Injective (fun d : KernelQuotient.coordinateAlgebra C g ⟶ A =>
      translateMap C hfg η d b) := by
  intro d₁ d₂ hd
  apply (quotientRepresents C hfg).homEquiv.injective
  apply Subtype.ext
  have he := congrArg (fun c => (C.represents.homEquiv c).val) hd
  change (C.represents.homEquiv
    (C.represents.homEquiv.symm (translatePoint C hfg η d₁ b))).val =
    (C.represents.homEquiv
      (C.represents.homEquiv.symm (translatePoint C hfg η d₂ b))).val at he
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at he
  exact add_right_cancel he

/-- Subtracting the selected lift sends every point in that fibre into ker g. -/
def untranslatePoint {A : CommAlgCat.{v} R} (c : C.coordinateAlgebra ⟶ A) (b : B ⟶ A)
    (hc : imageMap C K hfg ≫ c = β ≫ b) : g.kernelPoints A :=
  ⟨(C.represents.homEquiv c).val - N.algebraMapPoints b.hom η.val, by
    change g.onAlgebraPoints
      ((C.represents.homEquiv c).val - N.algebraMapPoints b.hom η.val) = 0
    erw [map_sub, ← imageMap_apply C K hfg c,
      hc, K.represents.homEquiv_comp, ← g.onAlgebraPoints_natural, hη]
    exact sub_self _⟩

/-- The algebra map to the zero fibre obtained by subtracting the lift. -/
def untranslateMap {A : CommAlgCat.{v} R} (c : C.coordinateAlgebra ⟶ A) (b : B ⟶ A)
    (hc : imageMap C K hfg ≫ c = β ≫ b) :
    KernelQuotient.coordinateAlgebra C g ⟶ A :=
  (quotientRepresents C hfg).homEquiv.symm (untranslatePoint C K hfg β η hη c b hc)

/-- Addition after subtraction recovers the original point of the fibre. -/
theorem translate_untranslate {A : CommAlgCat.{v} R}
    (c : C.coordinateAlgebra ⟶ A) (b : B ⟶ A)
    (hc : imageMap C K hfg ≫ c = β ≫ b) :
    translateMap C hfg η (untranslateMap C K hfg β η hη c b hc) b = c := by
  apply C.represents.homEquiv.injective
  apply Subtype.ext
  change (C.represents.homEquiv
    (C.represents.homEquiv.symm
      (translatePoint C hfg η (untranslateMap C K hfg β η hη c b hc) b))).val = _
  erw [Equiv.apply_symm_apply]
  change ((quotientRepresents C hfg).homEquiv
    ((quotientRepresents C hfg).homEquiv.symm
      (untranslatePoint C K hfg β η hη c b hc))).val +
    N.algebraMapPoints b.hom η.val = _
  erw [Equiv.apply_symm_apply]
  exact sub_add_cancel _ _

/-- The tensor algebra of the zero fibre and the chosen cover. -/
def tensorAlgebra (C : FiniteKernelModel h) (g : Hom N M) (B : CommAlgCat.{v} R) :
    CommAlgCat.{v} R :=
  CommAlgCat.of R ((KernelQuotient.coordinateAlgebra C g) ⊗[R] B)

/-- Inclusion of the zero-fibre algebra in the product with the cover. -/
def tensorInl : KernelQuotient.coordinateAlgebra C g ⟶ tensorAlgebra C g B :=
  CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft (R := R) (S := R)
    (A := KernelQuotient.coordinateAlgebra C g) (B := B))

/-- Inclusion of the cover algebra in the product with the zero fibre. -/
def tensorInr : B ⟶ tensorAlgebra C g B :=
  CommAlgCat.ofHom (Algebra.TensorProduct.includeRight (R := R)
    (A := KernelQuotient.coordinateAlgebra C g) (B := B))

/-- The universal map from the tensor algebra specified by its two factors. -/
def tensorDesc {A : CommAlgCat.{v} R}
    (d : KernelQuotient.coordinateAlgebra C g ⟶ A) (b : B ⟶ A) :
    tensorAlgebra C g B ⟶ A :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lift d.hom b.hom fun _ _ => Commute.all _ _)

@[simp]
theorem tensorInl_desc {A : CommAlgCat.{v} R}
    (d : KernelQuotient.coordinateAlgebra C g ⟶ A) (b : B ⟶ A) :
    tensorInl C ≫ tensorDesc C d b = d := by
  apply CommAlgCat.hom_ext
  exact Algebra.TensorProduct.lift_comp_includeLeft d.hom b.hom (fun _ _ => Commute.all _ _)

@[simp]
theorem tensorInr_desc {A : CommAlgCat.{v} R}
    (d : KernelQuotient.coordinateAlgebra C g ⟶ A) (b : B ⟶ A) :
    tensorInr C ≫ tensorDesc C d b = b := by
  apply CommAlgCat.hom_ext
  exact Algebra.TensorProduct.lift_comp_includeRight d.hom b.hom (fun _ _ => Commute.all _ _)

/-- Maps out of this product of affine schemes are detected on both tensor factors. -/
theorem tensor_hom_ext {A : CommAlgCat.{v} R}
    {p q : tensorAlgebra C g B ⟶ A}
    (hl : tensorInl C ≫ p = tensorInl C ≫ q)
    (hr : tensorInr C ≫ p = tensorInr C ≫ q) : p = q := by
  apply CommAlgCat.hom_ext
  apply Algebra.TensorProduct.ext
  · exact congrArg CommAlgCat.Hom.hom hl
  · exact congrArg CommAlgCat.Hom.hom hr

/-- Translation of the two universal points gives the represented fibre map. -/
def fibreMap : C.coordinateAlgebra ⟶ tensorAlgebra C g B :=
  translateMap C hfg η (tensorInl C) (tensorInr C)

include hη in
/-- The zero fibre times the cover is the actual base change of the represented
kernel along that cover. -/
theorem isPushout :
    IsPushout (imageMap C K hfg) β (fibreMap C hfg η) (tensorInr C) := by
  have hs : imageMap C K hfg ≫ fibreMap C hfg η = β ≫ tensorInr C :=
    imageMap_translateMap C K hfg β η hη _ _
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk (fibreMap C hfg η) (tensorInr C) hs)
  refine PushoutCocone.IsColimit.mk hs
    (fun s => tensorDesc C
      (untranslateMap C K hfg β η hη s.inl s.inr s.condition) s.inr) ?_ ?_ ?_
  · intro s
    rw [fibreMap, translateMap_comp, tensorInl_desc, tensorInr_desc]
    exact translate_untranslate C K hfg β η hη s.inl s.inr s.condition
  · intro s
    exact tensorInr_desc C _ _
  · intro s m hm₁ hm₂
    apply tensor_hom_ext C
    · rw [tensorInl_desc]
      apply translateMap_injective C hfg η s.inr
      calc
        translateMap C hfg η (tensorInl C ≫ m) s.inr =
            translateMap C hfg η (tensorInl C ≫ m) (tensorInr C ≫ m) := by rw [hm₂]
        _ = fibreMap C hfg η ≫ m := (translateMap_comp C hfg η _ _ m).symm
        _ = s.inl := hm₁
        _ = translateMap C hfg η
            (untranslateMap C K hfg β η hη s.inl s.inr s.condition) s.inr :=
          (translate_untranslate C K hfg β η hη s.inl s.inr s.condition).symm
    · rw [tensorInr_desc]
      exact hm₂

include hη in
/-- Flatness of the cover pulls back to flatness of the translated fibre map. -/
theorem fibreMap_flat (hβ : β.hom.Flat) : (fibreMap C hfg η).hom.Flat := by
  let : PreservesColimitsOfShape WalkingSpan
      (forget₂ (CommAlgCat.{v} R) CommRingCat.{v}) := by
    change PreservesColimitsOfShape WalkingSpan
      ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget (CommRingCat.of R))
    infer_instance
  have hs := (isPushout C K hfg β η hη).map
    (forget₂ (CommAlgCat.{v} R) CommRingCat.{v})
  exact CommRingCat.flat.of_isPushout hs hβ

end KernelTorsor
end Langlands.FormalGroup.ModuleLaw.Hom
