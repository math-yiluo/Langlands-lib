import Langlands.Global.AdelicGaloisTwistDescent
import Langlands.Global.RelativeRootChamber
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCocharacters

/-! # The Galois twist on ground-field homomorphisms and on torus characters -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] [FiniteDimensional F L]

section Naturality

variable (G H : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- The Galois twist commutes with the base change of a ground-field homomorphism. -/
theorem galoisTwist_comp_baseChange (σ : L ≃ₐ[F] L) (f : H ⟶ G)
    (t : adeleTest L ⟶ ((GroupScheme.baseChange (algebraBaseMap F L)).obj H).X) :
    galoisTwist F L G σ (t ≫ ((GroupScheme.baseChange (algebraBaseMap F L)).map f).hom.hom) =
      galoisTwist F L H σ t ≫ ((GroupScheme.baseChange (algebraBaseMap F L)).map f).hom.hom := by
  apply descentPoint_injective (algebraBaseMap F L) (galoisBaseMap F L σ)
    (galoisBaseMap_over F L σ) G (adeleTest L)
  rw [descentPoint_galoisTwist, descentPoint_comp_baseChange, descentPoint_galoisTwist,
    Category.assoc]

end Naturality

section Torus

variable (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffine T₀.toGrp.X.left] [LocallyOfFiniteType T₀.toGrp.X.hom]

omit [NumberField F] [FiniteDimensional F L] in
/-- A character value on an adelic point, through the points of `𝔾_m` over the adelic test
object and the global sections of `Spec 𝔸_L`. -/
theorem characterValue_val {T : CommGroupScheme (Spec (CommRingCat.of L))}
    (χ : characterLattice T) (t : adeleTest L ⟶ T.X) :
    (Lie.characterValue χ t : Adeles L) =
      (Scheme.ΓSpecIso (CommRingCat.of (Adeles L))).hom
        (Gm.pointsEquiv _ (adeleTest L) (t ≫ (CommGroupScheme.groupHom χ).hom.hom)).val :=
  rfl

/-- The Galois twist on the adelic points of the base change of a commutative ground group,
with the point type written in its commutative-group form. -/
def galoisTwistComm (σ : L ≃ₐ[F] L)
    (t : adeleTest L ⟶ ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).X) :
    adeleTest L ⟶ ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).X :=
  galoisTwist F L T₀.toGrp σ t

/-- The descended point of a twisted torus point is its restriction along `Spec σ̃`. -/
theorem descentPoint_galoisTwistComm (σ : L ≃ₐ[F] L)
    (t : adeleTest L ⟶ ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).X) :
    descentPoint (algebraBaseMap F L) (galoisBaseMap F L σ) (galoisBaseMap_over F L σ)
        T₀.toGrp (adeleTest L) (galoisTwistComm F L T₀ σ t) = (adeleTestIso F L σ).hom ≫ t :=
  descentPoint_galoisTwist F L T₀.toGrp σ t

/-- On points of `𝔾_m`, the Galois translate `σ χ` at the twisted point is `χ` at the original
point, restricted along `Spec σ̃`. -/
theorem pointsEquiv_galoisTwist_character (σ : L ≃ₐ[F] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀))
    (t : adeleTest L ⟶ ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).X) :
    Gm.pointsEquiv _ (adeleTest L) (galoisTwistComm F L T₀ σ t ≫
        (CommGroupScheme.groupHom (characterLattice.galoisRepresentation F L T₀ σ χ)).hom.hom) =
      Units.map (adeleTestIso F L σ).hom.left.appTop.hom.toMonoidHom
        (Gm.pointsEquiv _ (adeleTest L) (t ≫ (CommGroupScheme.groupHom χ).hom.hom)) := by
  rw [characterLattice.galoisRepresentation_points, descentPoint_galoisTwistComm, Category.assoc,
    Gm.pointsEquiv_naturality]

omit [FiniteDimensional F L] in
/-- Global sections of `Spec σ̃` on `Spec 𝔸_L` are `σ̃`. -/
theorem ΓSpecIso_adeleTestIso (σ : L ≃ₐ[F] L)
    (x : Γ(Spec (CommRingCat.of (Adeles L)), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (Adeles L))).hom
        ((adeleTestIso F L σ).hom.left.appTop.hom x) =
      AdeleGalois.ringEquiv F L σ ((Scheme.ΓSpecIso (CommRingCat.of (Adeles L))).hom x) := by
  rw [adeleTestIso_hom_left]
  change ((Spec.map (CommRingCat.ofHom
      (AdeleGalois.ringEquiv F L σ : Adeles L →+* Adeles L))).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of (Adeles L))).hom) x = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

/-- The value of the Galois translate `σ χ` of a character at the twisted point is the
adele automorphism `σ̃` applied to the value of `χ` at the original point. -/
theorem characterValue_galoisTwist (σ : L ≃ₐ[F] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀))
    (t : adeleTest L ⟶ ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).X) :
    Lie.characterValue (characterLattice.galoisRepresentation F L T₀ σ χ)
        (galoisTwistComm F L T₀ σ t) =
      Units.map (AdeleGalois.ringEquiv F L σ).toRingHom.toMonoidHom
        (Lie.characterValue χ t) := by
  apply Units.ext
  rw [Units.coe_map, characterValue_val, characterValue_val, pointsEquiv_galoisTwist_character,
    Units.coe_map]
  exact ΓSpecIso_adeleTestIso F L σ _

/-- The Galois twist on the adelic points of the base change of a commutative ground group,
with the point type written as affine points over the adeles. -/
def galoisTwistLie (σ : L ≃ₐ[F] L)
    (t : Lie.AffinePoints ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp
      (Adeles L)) :
    Lie.AffinePoints ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp
      (Adeles L) :=
  galoisTwist F L T₀.toGrp σ t

/-- The character-value identity of `characterValue_galoisTwist`, with both sides read as ideles. -/
theorem characterValue_galoisTwistLie (σ : L ≃ₐ[F] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀))
    (t : Lie.AffinePoints ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp
      (Adeles L)) :
    (Lie.characterValue (characterLattice.galoisRepresentation F L T₀ σ χ)
        (galoisTwistLie F L T₀ σ t) : Ideles L) =
      AdeleGalois.idelesMap σ (Lie.characterValue χ t) :=
  characterValue_galoisTwist F L T₀ σ χ t

/-- The idele norm of `σ χ` at the twisted point is the idele norm of `χ` at the original
point. -/
theorem full_characterValue_galoisTwistLie (σ : L ≃ₐ[F] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀))
    (t : Lie.AffinePoints ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp
      (Adeles L)) :
    IdeleAbsoluteValue.full L (Lie.characterValue
        (characterLattice.galoisRepresentation F L T₀ σ χ) (galoisTwistLie F L T₀ σ t)) =
      IdeleAbsoluteValue.full L (Lie.characterValue χ t) :=
  (congrArg (IdeleAbsoluteValue.full L) (characterValue_galoisTwistLie F L T₀ σ χ t)).trans
    (AdeleGalois.full_idelesMap σ _)

omit [NumberField F] [FiniteDimensional F L] [IsAffine T₀.toGrp.X.left]
  [LocallyOfFiniteType T₀.toGrp.X.hom] in
/-- `normCharacter_apply`, restated for the base change of a commutative ground group. -/
theorem normCharacter_eq_full
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀))
    (t : Lie.AffinePoints ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp
      (Adeles L)) :
    PositiveRealTorus.normCharacter L ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)
        χ t = IdeleAbsoluteValue.full L (Lie.characterValue χ t) :=
  PositiveRealTorus.normCharacter_apply L _ χ t

/-- The normalized adelic norm of the Galois translate `σ χ` at the twisted point equals the
norm of `χ` at the original point. -/
theorem normCharacter_galoisTwist (σ : L ≃ₐ[F] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀))
    (t : Lie.AffinePoints ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀).toGrp
      (Adeles L)) :
    PositiveRealTorus.normCharacter L ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀)
        (characterLattice.galoisRepresentation F L T₀ σ χ) (galoisTwistLie F L T₀ σ t) =
      PositiveRealTorus.normCharacter L
        ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T₀) χ t :=
  (normCharacter_eq_full F L T₀ _ _).trans
    ((full_characterValue_galoisTwistLie F L T₀ σ χ t).trans (normCharacter_eq_full F L T₀ χ t).symm)

end Torus

end Langlands.Global.AdelicGaloisUnit
