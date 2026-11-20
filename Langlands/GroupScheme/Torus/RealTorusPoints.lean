import Langlands.GroupScheme.GaloisPointTower
import Langlands.GroupScheme.Rational.CoordinateCotangentWeights
import Langlands.GroupScheme.Torus.EquivariantCharacterValueDescent
import Langlands.GroupScheme.Torus.SplitCharacterPoint
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Complex character coordinates for real points of rational tori -/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj ComplexConjugate

namespace Langlands.GroupScheme.RealTorus

variable (E : Type) [Field E] [Algebra ℚ E] [Algebra E ℂ] [IsScalarTower ℚ E ℂ]
variable (T : CommGroupScheme (Spec (CommRingCat.of ℚ)))

local notation "T_E" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap ℚ E)) T

/-- Values of the characters over a splitting field at an actual complex point. -/
def complexCharacter (p : Lie.AffinePoints T.toGrp ℂ) :
    Multiplicative (characterLattice T_E) →* ℂˣ :=
  SplitCharacterPoint.valueHom ((Lie.affineBaseChangeEquiv ℚ E T.toGrp ℂ).symm p)

theorem complexCharacter_apply (p : Lie.AffinePoints T.toGrp ℂ) (χ : characterLattice T_E) :
    complexCharacter E T p (Multiplicative.ofAdd χ) =
      Lie.characterValue χ ((Lie.affineBaseChangeEquiv ℚ E T.toGrp ℂ).symm p) := rfl

theorem complexCharacter_injective (hT : IsSplitTorus (T_E).toGrp) :
    Function.Injective (complexCharacter E T) := by
  intro p q h
  apply (Lie.affineBaseChangeEquiv ℚ E T.toGrp ℂ).symm.injective
  apply SplitCharacterPoint.ext_of_isSplitTorus hT
  intro χ
  exact congrArg (fun c : Multiplicative (characterLattice T_E) →* ℂˣ =>
    c (Multiplicative.ofAdd χ)) h

theorem complexCharacter_surjective (hT : IsSplitTorus (T_E).toGrp) :
    Function.Surjective (complexCharacter E T) := by
  intro x
  let A := (algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E ℂ))
  let g := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let xΓ : Multiplicative (characterLattice T_E) →* (Γ(A.left, ⊤))ˣ :=
    (Units.map g.toMonoidHom).comp x
  let q : Lie.AffinePoints ((GroupScheme.baseChange (algebraBaseMap ℚ E)).obj T.toGrp) ℂ :=
    (characterLattice.pointCharactersEquiv T_E hT A).symm xΓ
  refine ⟨Lie.affineBaseChangeEquiv ℚ E T.toGrp ℂ q, ?_⟩
  apply MonoidHom.ext
  intro χ
  change complexCharacter E T _ (Multiplicative.ofAdd χ.toAdd) = _
  rw [complexCharacter_apply, MulEquiv.symm_apply_apply]
  rw [Lie.characterValue_eq_globalUnits]
  change Units.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.toMonoidHom
    (characterLattice.pointCharactersEquiv T_E hT A q χ) = x χ
  have hq : characterLattice.pointCharactersEquiv T_E hT A q = xΓ :=
    (characterLattice.pointCharactersEquiv T_E hT A).apply_symm_apply xΓ
  rw [hq]
  apply Units.ext
  change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom (x χ : ℂ) = (x χ : ℂ)
  rw [Iso.inv_hom_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem complexCharacter_comp {P : CommGroupScheme (Spec (CommRingCat.of ℚ))} (f : P ⟶ T)
    (p : Lie.AffinePoints P.toGrp ℂ) (χ : characterLattice T_E) :
    complexCharacter E T (p ≫ (CommGroupScheme.groupHom f).hom.hom) (Multiplicative.ofAdd χ) =
      complexCharacter E P p (Multiplicative.ofAdd
        ((CommGroupScheme.baseChange (algebraBaseMap ℚ E)).map f ≫ χ)) := by
  rw [complexCharacter_apply, complexCharacter_apply, Lie.characterValue_comp]
  congr 1
  apply (Lie.affineBaseChangeEquiv ℚ E T.toGrp ℂ).injective
  rw [MulEquiv.apply_symm_apply]
  rw [show CommGroupScheme.groupHom ((CommGroupScheme.baseChange (algebraBaseMap ℚ E)).map f) =
    (GroupScheme.baseChange (algebraBaseMap ℚ E)).map (CommGroupScheme.groupHom f) from rfl]
  rw [affineBaseChangeEquiv_comp_baseChange, MulEquiv.apply_symm_apply]

section TwistedPoints

variable {k K A : Type} [Field k] [Field K] [Algebra k K]
  [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
  (σ : K ≃ₐ[k] K) (f : Lie.GaloisTestAlgebra σ A →ₐ[K] A)

private theorem affineBaseChangeEquiv_symm_affineMap
    (G : GroupScheme (Spec (CommRingCat.of k))) (p : Lie.AffinePoints G A) :
    (Lie.affineBaseChangeEquiv k K G A).symm (Lie.affineMap G (f.restrictScalars k) p) =
      Lie.affineMap ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) f
        (Lie.galoisTestPoint k K σ A G ((Lie.affineBaseChangeEquiv k K G A).symm p)) := by
  apply (Lie.affineBaseChangeEquiv k K G A).injective
  rw [MulEquiv.apply_symm_apply, Lie.affineBaseChangeEquiv_naturality,
    Lie.affineBaseChangeEquiv_galoisTestPoint, MulEquiv.apply_symm_apply]

omit [Algebra k A] [IsScalarTower k K A] in
set_option backward.isDefEq.respectTransparency false in
private theorem characterValue_twistedPoint
    (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj S))
    (p : Lie.AffinePoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj S.toGrp) A) :
    (Lie.characterValue χ (Lie.affineMap ((GroupScheme.baseChange (algebraBaseMap k K)).obj S.toGrp)
      f (Lie.galoisTestPoint k K σ A S.toGrp p)) : A) =
      f ((Lie.characterValue (characterLattice.galoisRepresentation k K S σ χ) p : A)) := by
  let S' := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S
  let q : Lie.AffinePoints S'.toGrp (Lie.GaloisTestAlgebra σ A) :=
    Lie.galoisTestPoint k K σ A S.toGrp p
  change (Lie.characterValue χ (Lie.affineMap S'.toGrp f q) : A) = _
  rw [CoordinateWeights.characterValue_affineMap f χ q]
  exact congrArg (fun z : (Lie.GaloisTestAlgebra σ A)ˣ => f (z : Lie.GaloisTestAlgebra σ A))
    (Lie.characterValue_galoisRepresentation k K σ A S χ p).symm

end TwistedPoints

variable (s : E ≃ₐ[ℚ] E)
variable (hs : ∀ a : E, algebraMap E ℂ (s a) = conj (algebraMap E ℂ a))

private def conjugateTestHom : Lie.GaloisTestAlgebra s ℂ →ₐ[E] ℂ where
  toRingHom := starRingEnd ℂ
  commutes' a := by
    change conj (algebraMap E ℂ (s a)) = algebraMap E ℂ a
    rw [hs a]
    exact star_star _

include hs in
set_option backward.isDefEq.respectTransparency false in
/-- Complex conjugation acts on character values through the restricted automorphism
of the splitting field and conjugation of the value. -/
theorem complexCharacter_conjugate (p : Lie.AffinePoints T.toGrp ℂ) (χ : characterLattice T_E) :
    (complexCharacter E T (GaloisPoint.relativeConjugate ℚ ℝ ℂ T.toGrp Complex.conjAe p)
      (Multiplicative.ofAdd χ) : ℂ) =
      conj (complexCharacter E T p (Multiplicative.ofAdd
        (characterLattice.galoisRepresentation ℚ E T s χ)) : ℂ) := by
  let f := conjugateTestHom E s hs
  have hp : GaloisPoint.relativeConjugate ℚ ℝ ℂ T.toGrp Complex.conjAe p =
      Lie.affineMap T.toGrp (f.restrictScalars ℚ) p := rfl
  rw [hp, complexCharacter_apply, complexCharacter_apply,
    affineBaseChangeEquiv_symm_affineMap]
  exact characterValue_twistedPoint s f T χ ((Lie.affineBaseChangeEquiv ℚ E T.toGrp ℂ).symm p)

include hs in
/-- The complex character of an actual real point is equivariant under conjugation. -/
theorem complexCharacter_real (p : Lie.AffinePoints T.toGrp ℝ) (χ : characterLattice T_E)
    [IsAffine T.X.left] :
    (complexCharacter E T (GaloisPoint.relativeExtend ℚ ℝ ℂ T.toGrp p) (Multiplicative.ofAdd
        (characterLattice.galoisRepresentation ℚ E T s χ)) : ℂ) =
      conj (complexCharacter E T (GaloisPoint.relativeExtend ℚ ℝ ℂ T.toGrp p)
        (Multiplicative.ofAdd χ) : ℂ) := by
  have h := complexCharacter_conjugate E T s hs (GaloisPoint.relativeExtend ℚ ℝ ℂ T.toGrp p) χ
  rw [GaloisPoint.relativeConjugate_extend] at h
  have h' := congrArg (starRingEnd ℂ) h
  simpa only [starRingEnd_apply, star_star] using h'.symm

/-- A complex point fixed by conjugation comes from the original real point group. -/
theorem exists_relativeExtend_eq_of_conjugate_eq
    (G : GroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine G.X.left]
    (p : Lie.AffinePoints G ℂ)
    (hp : GaloisPoint.relativeConjugate ℚ ℝ ℂ G Complex.conjAe p = p) :
    ∃ r : Lie.AffinePoints G ℝ, GaloisPoint.relativeExtend ℚ ℝ ℂ G r = p := by
  let : Algebra.IsQuadraticExtension ℝ ℂ := ⟨Complex.finrank_real_complex⟩
  have hfix : p ∈ GaloisPoint.relativeFixedSubgroup ℚ ℝ ℂ G := by
    intro σ
    rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with h | h
    · have hσ : σ = 1 := AlgEquiv.ext fun a => DFunLike.congr_fun h a
      subst σ
      exact GaloisPoint.conjugate_one ℚ ℂ G p
    · have hσ : σ = Complex.conjAe := AlgEquiv.ext fun a => DFunLike.congr_fun h a
      subst σ
      exact hp
  let q : GaloisPoint.relativeFixedSubgroup ℚ ℝ ℂ G := ⟨p, hfix⟩
  exact ⟨GaloisPoint.relativeDescend ℚ ℝ ℂ G q, GaloisPoint.relativeExtend_descend ℚ ℝ ℂ G q⟩

include hs in
/-- Every equivariant character is evaluation at an actual real point of the torus. -/
theorem exists_realPoint_of_complexCharacter_equivariant (hT : IsSplitTorus (T_E).toGrp)
    [IsAffine T.X.left] (x : Multiplicative (characterLattice T_E) →* ℂˣ)
    (hx : ∀ χ : characterLattice T_E,
      (x (Multiplicative.ofAdd (characterLattice.galoisRepresentation ℚ E T s χ)) : ℂ) =
        conj (x (Multiplicative.ofAdd χ) : ℂ)) :
    ∃ p : Lie.AffinePoints T.toGrp ℝ,
      complexCharacter E T (GaloisPoint.relativeExtend ℚ ℝ ℂ T.toGrp p) = x := by
  obtain ⟨q, hq⟩ := complexCharacter_surjective E T hT x
  have hfix : GaloisPoint.relativeConjugate ℚ ℝ ℂ T.toGrp Complex.conjAe q = q := by
    apply complexCharacter_injective E T hT
    apply MonoidHom.ext
    intro χ
    apply Units.ext
    change (complexCharacter E T _ (Multiplicative.ofAdd χ.toAdd) : ℂ) = _
    rw [complexCharacter_conjugate E T s hs, hq, hx]
    exact star_star _
  obtain ⟨p, hp⟩ := exists_relativeExtend_eq_of_conjugate_eq T.toGrp q hfix
  exact ⟨p, by rw [hp, hq]⟩

end Langlands.GroupScheme.RealTorus
