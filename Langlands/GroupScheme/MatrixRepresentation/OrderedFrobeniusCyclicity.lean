import Langlands.GroupScheme.MatrixRepresentation.FrobeniusCyclicDetection
import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive

/-! # The actual ordered top coefficient and Frobenius cyclicity -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.MatrixRepresentation.OrderedFrobeniusCyclicity

open OrderedAdditiveProducts OrderedAdditiveCoordinates OrderedAdditiveTruncation
open FrobeniusCoordinateModel FrobeniusPolynomialBox FrobeniusOrderedDistributions
open FrobeniusTopIntegral FrobeniusCyclicDetection

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {d : ℕ} (x : Fin d → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))

/-- Bijectivity on all coefficient algebras forces bijectivity of the actual
ordered coordinate pullback, by its two universal points. -/
theorem coordinateMap_bijective_of_orderedPoint
    (hpoint : ∀ A : CommAlgCat.{u} k, Function.Bijective (orderedPoint x A)) :
    Function.Bijective (coordinateMap x) := by
  obtain ⟨t, ht⟩ := (hpoint (CharacterUnits.Coord G)).surjective
    (CharacterUnits.universalPoint G)
  let F : MvPolynomial (Fin d) k →ₐ[k] CharacterUnits.Coord G := aeval t
  have hleft : F.comp (coordinateMap x) = AlgHom.id k (CharacterUnits.Coord G) := by
    rw [← pointCoordinates_orderedPoint, ht]
    exact CharacterUnits.pointCoordinates_universalPoint G
  have htuple : (fun i => coordinateMap x (t i)) = MvPolynomial.X := by
    apply (hpoint (CommAlgCat.of k (MvPolynomial (Fin d) k))).injective
    have hn := orderedPoint_naturality x
      (CommAlgCat.ofHom (coordinateMap x) :
        CharacterUnits.Coord G ⟶ CommAlgCat.of k (MvPolynomial (Fin d) k)) t
    simp only [CommAlgCat.hom_ofHom] at hn
    apply hn.symm.trans
    apply (congrArg (Lie.affineMap G (coordinateMap x)) ht).trans
    apply (Lie.pointCoordinates G).injective
    rw [Lie.pointCoordinates_naturality]
    exact (congrArg (coordinateMap x).comp
      (CharacterUnits.pointCoordinates_universalPoint G)).trans (AlgHom.comp_id _)
  have hright : (coordinateMap x).comp F = AlgHom.id k (MvPolynomial (Fin d) k) := by
    apply MvPolynomial.algHom_ext
    intro i
    change coordinateMap x (aeval t (X i)) = X i
    rw [aeval_X]
    exact congrFun htuple i
  exact ⟨Function.LeftInverse.injective
    (show Function.LeftInverse F (coordinateMap x) from fun a => AlgHom.congr_fun hleft a),
    Function.RightInverse.surjective
      (show Function.RightInverse F (coordinateMap x) from fun a => AlgHom.congr_fun hright a)⟩

variable (hx : Function.Bijective (coordinateMap x))

/-- The actual coordinate functions dual to the ordered additive parameters. -/
def generator (i : Fin d) : CharacterUnits.Coord G :=
  (coordinateEquiv x hx).symm (X i)

@[simp] theorem coordinateMap_generator (i : Fin d) :
    coordinateMap x (generator x hx i) = X i :=
  (coordinateEquiv x hx).apply_symm_apply _

/-- Evaluation in these generators is the inverse of the actual ordered chart. -/
theorem aeval_generator :
    (aeval (generator x hx) : MvPolynomial (Fin d) k →ₐ[k] CharacterUnits.Coord G) =
      (coordinateEquiv x hx).symm.toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  exact aeval_X _ i

/-- The ordered parameters give polynomial coordinates of the whole group. -/
theorem aeval_generator_bijective :
    Function.Bijective (aeval (generator x hx) :
      MvPolynomial (Fin d) k →ₐ[k] CharacterUnits.Coord G) := by
  rw [aeval_generator]
  exact (coordinateEquiv x hx).symm.bijective

/-- The ordered coordinate functions vanish at the actual identity. -/
theorem generator_origin_zero (i : Fin d) :
    TorusUnipotence.coordCounit G (generator x hx i) = 0 := by
  change Lie.coordinateOrigin G (generator x hx i) = 0
  rw [← coordinateMap_origin x, coordinateMap_generator]
  simp

/-- Ordered coordinate functions recover the original parameter on every
commutative coefficient algebra. -/
theorem generator_orderedPoint (A : CommAlgCat.{u} k) (t : Fin d → A) (i : Fin d) :
    Lie.pointCoordinates G (orderedPoint x A t) (generator x hx i) = t i := by
  rw [pointCoordinates_orderedPoint, AlgHom.comp_apply, coordinateMap_generator, aeval_X]

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) (w : Fin d → characterLattice S)
    (hscale : ∀ (A : CommAlgCat.{u} k) (s : GroupScheme.affinePoints S.toGrp A)
      (c : A) (i : Fin d),
      b.act s (VectorGroup.affinePoint (R := CommRingCat.of k) A (fun _ : Fin 1 => c) ≫ (x i).hom.hom) =
        VectorGroup.affinePoint (R := CommRingCat.of k) A
          (fun _ : Fin 1 => (Lie.characterValue (w i) s : A) * c) ≫ (x i).hom.hom)

include hscale in
omit [IsAffineHom G.X.hom] in
/-- The actual ordered chart intertwines the torus action with parameter scaling,
even when the additive factors do not commute. -/
theorem orderedPoint_act (A : CommAlgCat.{u} k) (s : GroupScheme.affinePoints S.toGrp A)
    (t : Fin d → A) :
    b.act s (orderedPoint x A t) =
      orderedPoint x A (fun i => (Lie.characterValue (w i) s : A) * t i) := by
  change (b.pointAut _ s) (List.ofFn (fun i =>
      VectorGroup.affinePoint (R := CommRingCat.of k) A (fun _ : Fin 1 => t i) ≫ (x i).hom.hom)).prod = _
  rw [map_list_prod, List.map_ofFn]
  change (List.ofFn (fun i => b.act s
    (VectorGroup.affinePoint (R := CommRingCat.of k) A (fun _ : Fin 1 => t i) ≫ (x i).hom.hom))).prod = _
  simp only [hscale]
  rfl

include hscale in
/-- Inverse ordered coordinates are actual torus eigenfunctions on all algebras. -/
theorem generator_mem_weightSpace (i : Fin d) :
    generator x hx i ∈ CoordinateWeights.weightSpace b (w i) := by
  intro A _ _ s g
  obtain ⟨t, rfl⟩ := (orderedPoint_bijective x hx (CommAlgCat.of k A)).surjective g
  rw [orderedPoint_act x b w hscale]
  exact (generator_orderedPoint x hx (CommAlgCat.of k A) _ i).trans
    (congrArg ((Lie.characterValue (w i) s : A) * ·)
      (generator_orderedPoint x hx (CommAlgCat.of k A) t i).symm)

/-- Eigenfunction coordinates recover exactly the original ordered chart. -/
theorem polynomialCoordinates_generator :
    polynomialCoordinates (generator x hx) (aeval_generator_bijective x hx) =
      coordinateEquiv x hx := by
  apply AlgEquiv.ext
  intro f
  apply (coordinateEquiv x hx).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  have h := AlgHom.congr_fun (aeval_generator x hx)
    (polynomialCoordinates (generator x hx) (aeval_generator_bijective x hx) f)
  exact h.symm.trans ((AlgEquiv.ofBijective (aeval (generator x hx))
    (aeval_generator_bijective x hx)).apply_symm_apply f)

variable (p : ℕ) [ExpChar k p] (r : ℕ)

/-- The actual top distribution is the original ordered coefficient functional. -/
theorem topDistribution_eq_basis :
    (topDistribution p r (generator x hx) (aeval_generator_bijective x hx)
      (generator_origin_zero x hx)).ofConv =
        distributionBasis p r x hx ⟨bound p d r, le_refl (bound p d r)⟩ := by
  apply LinearMap.ext
  intro a
  obtain ⟨f, rfl⟩ := (Ideal.Quotient.mkₐ_surjective k
    (quotientIdeal G p r)) a
  apply (topDistribution_quotientMap p r (generator x hx)
    (aeval_generator_bijective x hx) (generator_origin_zero x hx) f).trans
  apply (congrArg (fun e : CharacterUnits.Coord G ≃ₐ[k] MvPolynomial (Fin d) k =>
    (e f).coeff (bound p d r)) (polynomialCoordinates_generator x hx)).trans
  exact (distributionBasis_quotientMap p r x hx
    ⟨bound p d r, le_refl (bound p d r)⟩ f).symm

variable {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)

/-- The top convolution functional acts by the original ordered divided powers. -/
theorem distributionAction_top :
    distributionAction p r ρ
      (topDistribution p r (generator x hx) (aeval_generator_bijective x hx)
        (generator_origin_zero x hx)).ofConv =
      coefficientOperator ρ x (bound p d r) := by
  exact (congrArg (distributionAction p r ρ)
    (topDistribution_eq_basis x hx p r)).trans
      (distributionAction_basis p r x hx ρ
        ⟨bound p d r, le_refl (bound p d r)⟩)

variable (hS : IsSplitTorus S.toGrp) (ν : cocharacterLattice S)
    (hw : ∀ i, 0 < latticePairing S (w i) ν) (v : n → k)

include hx hS hscale hw in
/-- A nonzero original ordered top coefficient detects the entire actual
Frobenius quotient dual by its action on the original vector. -/
theorem distributionOrbitMap_injective
    (hv : coefficientOperator ρ x (bound p d r) v ≠ 0) :
    Function.Injective
      (FrobeniusOriginUniversality.distributionOrbitMap p r ρ v) := by
  apply distributionOrbitMap_injective_of_topAction_ne_zero p r hS b ν w
    (generator x hx) (aeval_generator_bijective x hx)
    (generator_mem_weightSpace x hx b w hscale) (generator_origin_zero x hx) hw ρ v
  rw [distributionAction_top]
  exact hv

include hx hS hscale hw in
/-- The intrinsic Frobenius-origin orbit has the full expected dimension
when the original ordered top coefficient is nonzero. -/
theorem finrank_originOrbitSpan
    (hv : coefficientOperator ρ x (bound p d r) v ≠ 0) :
    Module.finrank k (originOrbitSpan p r ρ v) = (p ^ r) ^ d := by
  apply finrank_originOrbitSpan_of_topAction_ne_zero p r hS b ν w
    (generator x hx) (aeval_generator_bijective x hx)
    (generator_mem_weightSpace x hx b w hscale) (generator_origin_zero x hx) hw ρ v
  rw [distributionAction_top]
  exact hv

include hx hS hscale hw in
/-- A separate bound on the whole representation turns the nonzero original
top coefficient into spanning by all intrinsic Frobenius-origin tests. -/
theorem originOrbitSpan_eq_top_of_finrank_le
    (hv : coefficientOperator ρ x (bound p d r) v ≠ 0)
    (hdim : Module.finrank k (n → k) ≤ (p ^ r) ^ d) :
    originOrbitSpan p r ρ v = ⊤ := by
  apply originOrbitSpan_eq_top_of_topAction_ne_zero_of_finrank_le p r hS b ν w
    (generator x hx) (aeval_generator_bijective x hx)
    (generator_mem_weightSpace x hx b w hscale) (generator_origin_zero x hx) hw ρ v _ hdim
  rw [distributionAction_top]
  exact hv

end Langlands.GroupScheme.MatrixRepresentation.OrderedFrobeniusCyclicity
