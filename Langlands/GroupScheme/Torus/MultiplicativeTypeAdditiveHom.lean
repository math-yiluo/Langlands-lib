import Langlands.GroupScheme.Rational.PTorsionHopfCoordinates
import Langlands.GroupScheme.Rational.CorepresentedPrimitiveGenerators
import Langlands.GroupScheme.Unipotent.AdditiveCharacter
import Langlands.GroupScheme.HopfPrimitiveQuotient

/-! # Homomorphisms to the additive group and primitive coordinate functions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MultiplicativeTypeCharacterization

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- If every homomorphism to `𝔾ₐ` is trivial, the coordinate Hopf algebra has no nonzero
primitive element. -/
theorem eq_zero_of_isPrimitiveElem_of_subsingleton
    (hG : Subsingleton (G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1))
    (a : AffineCoordinates.hopfAlgebra G) (ha : Bialgebra.IsPrimitiveElem k a) : a = 0 := by
  by_contra h0
  let e := AffineCoordinates.corepresentation G
  have hy :
      VectorGroup.IsPrimitiveFamily e (fun _ : Fin 1 => (a : AffineCoordinates.algebra G)) :=
    fun A x x' _ => AffineCoordinates.isPrimitiveFunction_of_isPrimitiveElem G ha A x x'
  apply Unipotent.quotientMap_ne_zero e hy h0
  have h : (AffineCoordinates.groupSchemeIso G).inv ≫ VectorGroup.quotientMap hy = 0 :=
    Subsingleton.elim _ _
  calc VectorGroup.quotientMap hy =
      (AffineCoordinates.groupSchemeIso G).hom ≫
        ((AffineCoordinates.groupSchemeIso G).inv ≫ VectorGroup.quotientMap hy) := by simp
    _ = 0 := by rw [h, Limits.comp_zero]

/-- The coordinate of a scheme point of `𝔾ₐ`, pulled back to the ring of an affine test scheme. -/
abbrev gaCoord (B : Type u) [CommRing B] [Algebra k B]
    (x : (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of k)) ⟶
      (VectorGroup.groupScheme (CommRingCat.of k) 1).X) : B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom
    ((VectorGroup.coordinates (CommRingCat.of k) 1 _ x).toAdd 0)

/-- Coordinate points of `G` are pulled back from the universal coordinate point. -/
theorem coordinatePointEquiv_eq_comp (B : Type u) [CommRing B] [Algebra k B]
    (χ : AffineCoordinates.hopfAlgebra G →ₐ[k] B) :
    AffineCoordinates.coordinatePointEquiv G B (toConv χ) =
      (Spec.map (CommRingCat.ofHom χ.toRingHom)).asOver (Spec (CommRingCat.of k)) ≫
        (AffineCoordinates.hopfSpecIso G).hom.hom.hom :=
  rfl

/-- Coordinates of products of points of `𝔾ₐ` add. -/
theorem gaCoord_mul (B : Type u) [CommRing B] [Algebra k B]
    (x y : (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of k)) ⟶
      (VectorGroup.groupScheme (CommRingCat.of k) 1).X) :
    gaCoord B (x * y) = gaCoord B x + gaCoord B y := by
  unfold gaCoord
  rw [VectorGroup.coordinates_mul, Pi.add_apply]
  exact map_add _ _ _

/-- The convolution product of the two tensor inclusions is the comultiplication. -/
theorem includeLeft_mul_includeRight (A : Type u) [CommRing A] [Bialgebra k A] :
    toConv (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A) *
        toConv (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A) =
      toConv (Bialgebra.comulAlgHom k A) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  change (toConv (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A) *
      toConv (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A)) x = _
  rw [AlgHom.convMul_apply]
  simp

/-- If the coordinate Hopf algebra has no nonzero primitive element, every homomorphism to `𝔾ₐ`
is trivial. -/
theorem hom_eq_one_of_noPrimitive
    (hP : ∀ a : AffineCoordinates.hopfAlgebra G, Bialgebra.IsPrimitiveElem k a → a = 0)
    (q : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1) : q.hom.hom = 1 := by
  let A := AffineCoordinates.hopfAlgebra G
  let e := AffineCoordinates.hopfSpecIso G
  let E := e.hom.hom.hom
  have : IsMonHom q.hom.hom := q.hom.isMonHom_hom
  have hIso : IsIso E := ⟨e.inv.hom.hom, congrArg (fun φ => φ.hom.hom) e.hom_inv_id,
    congrArg (fun φ => φ.hom.hom) e.inv_hom_id⟩
  let u : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k)) ⟶
      (VectorGroup.groupScheme (CommRingCat.of k) 1).X := E ≫ q.hom.hom
  let a : A := gaCoord A u
  have hu : (VectorGroup.coordinates (CommRingCat.of k) 1 _ u).toAdd 0 =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv a := by
    exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of A)) _).symm
  have hnat : ∀ (B : Type u) [CommRing B] [Algebra k B] (χ : A →ₐ[k] B),
      gaCoord B (AffineCoordinates.coordinatePointEquiv G B (toConv χ) ≫ q.hom.hom) = χ a := by
    intro B _ _ χ
    have h1 : AffineCoordinates.coordinatePointEquiv G B (toConv χ) ≫ q.hom.hom =
        (Spec.map (CommRingCat.ofHom χ.toRingHom)).asOver (Spec (CommRingCat.of k)) ≫ u := by
      rw [coordinatePointEquiv_eq_comp]
      exact Category.assoc _ _ _
    have h2 := VectorGroup.coordinates_comp
      ((Spec.map (CommRingCat.ofHom χ.toRingHom)).asOver (Spec (CommRingCat.of k))) u
    unfold gaCoord
    rw [h1, h2]
    change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      ((Spec.map (CommRingCat.ofHom χ.toRingHom)).appTop
        ((VectorGroup.coordinates (CommRingCat.of k) 1 _ u).toAdd 0)) = _
    rw [hu, HopfPrimitive.appTop_specMap_inv]
    simp
  have hprim : Bialgebra.IsPrimitiveElem k a := by
    rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul]
    have key := congrArg (fun x => gaCoord (A ⊗[k] A) (x ≫ q.hom.hom))
      (map_mul (AffineCoordinates.coordinatePointEquiv G (A ⊗[k] A))
        (toConv (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A))
        (toConv (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A)))
    simp only at key
    rw [MonObj.mul_comp, gaCoord_mul, includeLeft_mul_includeRight, hnat, hnat, hnat] at key
    rw [Bialgebra.comulAlgHom_apply] at key
    rw [key, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      add_comm]
  have ha0 : a = 0 := hP a hprim
  have hu1 : u = 1 := by
    apply VectorGroup.points_ext
    intro i
    rw [Subsingleton.elim i 0, hu, ha0, map_zero, map_one, toAdd_one, Pi.zero_apply]
    rfl
  have hE : E ≫ q.hom.hom = 1 := hu1
  calc q.hom.hom = inv E ≫ (E ≫ q.hom.hom) := (IsIso.inv_hom_id_assoc E q.hom.hom).symm
    _ = inv E ≫ 1 := by rw [hE]
    _ = 1 := MonObj.comp_one _

/-- Without nonzero primitive coordinate functions there is only one homomorphism to `𝔾ₐ`. -/
theorem subsingleton_of_noPrimitive
    (hP : ∀ a : AffineCoordinates.hopfAlgebra G, Bialgebra.IsPrimitiveElem k a → a = 0) :
    Subsingleton (G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1) :=
  ⟨fun q q' => Grp.hom_ext _ _ ((hom_eq_one_of_noPrimitive G hP q).trans
    (hom_eq_one_of_noPrimitive G hP q').symm)⟩

end Langlands.GroupScheme.MultiplicativeTypeCharacterization
