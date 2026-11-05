import Langlands.GroupScheme.Torus.AffineSchemeAction
import Langlands.GroupScheme.Torus.TwistedTransporter
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.CommutativeAlgebra.FixedQuotientFinitePresentation

/-! # Actual smooth fixed schemes and diagonalizable transporters -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace PointwiseSchemeAction

variable {S : Scheme.{u}} {H : GroupScheme S} {X : Over S}
  {a : PointwiseSchemeAction H X}

/-- All-refinement fixedness is preserved by restriction of the test scheme. -/
theorem IsFixed.comp {T T' : Over S} {x : T ⟶ X} (hx : a.IsFixed x) (b : T' ⟶ T) :
    a.IsFixed (b ≫ x) := by
  intro V c h
  simpa only [Category.assoc] using hx V (c ≫ b) h

end PointwiseSchemeAction

namespace CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (a : PointwiseSchemeAction (Diagonalizable.groupScheme R M).toGrp G.X)

/-- The coordinate algebra of the fixed scheme of the actual scheme action. -/
abbrev schemeActionFixedAlgebra : CommAlgCat.{u} R :=
  Corepresented.quotientAlgebra (schemeActionFixedIdeal a)

/-- The spectrum of the full actual fixed ideal, as a scheme over the base. -/
abbrev schemeActionFixedScheme : Over (Spec R) :=
  (algSpec R).obj (op (schemeActionFixedAlgebra a))

/-- The fixed-scheme map into the original group scheme. -/
def schemeActionFixedHom : schemeActionFixedScheme a ⟶ G.X :=
  (algSpec R).map (Corepresented.quotientMap (schemeActionFixedIdeal a)).op ≫
    (AffineCoordinates.coordinateSchemeIso G).hom

instance isClosedImmersion_schemeActionFixedHom :
    IsClosedImmersion (schemeActionFixedHom a).left := by
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (schemeActionFixedIdeal a)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  change IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (schemeActionFixedIdeal a))) ≫
      (AffineCoordinates.coordinateSchemeIso G).hom.left)
  infer_instance

instance mono_schemeActionFixedHom : Mono (schemeActionFixedHom a) :=
  Over.mono_of_mono_left _

/-- The fixed-scheme map is itself fixed on every scheme refinement. -/
theorem schemeActionFixedHom_isFixed : a.IsFixed (schemeActionFixedHom a) := by
  change a.IsFixed (AffineCoordinates.pointEquiv G (schemeActionFixedAlgebra a)
    (Corepresented.quotientMap (schemeActionFixedIdeal a)))
  apply (schemeActionFixedIdeal_le_ker_iff a _).mp
  change schemeActionFixedIdeal a ≤ RingHom.ker (Ideal.Quotient.mk (schemeActionFixedIdeal a))
  rw [Ideal.mk_ker]

/-- On every affine test scheme, the fixed-scheme inclusion represents exactly
the actual all-refinement fixedness condition. -/
theorem exists_schemeActionFixed_factor_iff {C : CommAlgCat.{u} R}
    (x : (algSpec R).obj (op C) ⟶ G.X) :
    (∃ y : (algSpec R).obj (op C) ⟶ schemeActionFixedScheme a,
      y ≫ schemeActionFixedHom a = x) ↔ a.IsFixed x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact (schemeActionFixedHom_isFixed a).comp y
  · intro hx
    let φ := (AffineCoordinates.pointEquiv G C).symm x
    have hφ : AffineCoordinates.pointEquiv G C φ = x :=
      Equiv.apply_symm_apply _ _
    have hker := (schemeActionFixedIdeal_le_ker_iff a φ).mpr (hφ.symm ▸ hx)
    let ψ : schemeActionFixedAlgebra a ⟶ C := CommAlgCat.ofHom
      (Ideal.Quotient.liftₐ (schemeActionFixedIdeal a) φ.hom hker)
    have hcomp : Corepresented.quotientMap (schemeActionFixedIdeal a) ≫ ψ = φ := by
      apply CommAlgCat.hom_ext
      exact Ideal.Quotient.liftₐ_comp _ _ _
    refine ⟨(algSpec R).map ψ.op, ?_⟩
    rw [schemeActionFixedHom, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
    change (algSpec R).map (Corepresented.quotientMap (schemeActionFixedIdeal a) ≫ ψ).op ≫
      (AffineCoordinates.coordinateSchemeIso G).hom = x
    rw [hcomp]
    exact hφ

/-- The fixed coordinate quotient is smooth over an arbitrary base ring. -/
theorem smooth_schemeActionFixedAlgebra [Algebra.Smooth R (AffineCoordinates.algebra G)] :
    Algebra.Smooth R (schemeActionFixedAlgebra a) where
  finitePresentation :=
    Langlands.CommutativeAlgebra.GradedFixedQuotient.finitePresentation_fixedQuotient
      (coaction (ofPointwiseSchemeAction a)).hom
  formallySmooth := formallySmooth_schemeActionFixedQuotient a

/-- The actual fixed scheme is smooth over an arbitrary base ring when the
ambient affine group scheme is smooth. -/
theorem smooth_schemeActionFixedScheme (hG : Smooth G.X.hom) :
    Smooth (schemeActionFixedScheme a).hom := by
  let := AffineCoordinates.smooth_algebra G hG
  let := smooth_schemeActionFixedAlgebra a
  have h : Smooth
      (Spec.map (CommRingCat.ofHom (algebraMap R (schemeActionFixedAlgebra a)))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  exact h

end CharacterAction

namespace PointwiseSchemeAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (i₁ i₂ : (Diagonalizable.groupScheme R M).toGrp ⟶ G)

/-- The actual affine transporter scheme, cut out by the fixed ideal of the
left-right action. -/
abbrev relativeTransporterScheme : Over (Spec R) :=
  CharacterAction.schemeActionFixedScheme (twistedTransporter i₁ i₂)

/-- The actual closed transporter inclusion into the ambient group. -/
def relativeTransporterHom : relativeTransporterScheme i₁ i₂ ⟶ G.X :=
  CharacterAction.schemeActionFixedHom (twistedTransporter i₁ i₂)

instance isClosedImmersion_relativeTransporterHom :
    IsClosedImmersion (relativeTransporterHom i₁ i₂).left :=
  CharacterAction.isClosedImmersion_schemeActionFixedHom _

/-- Every point of this scheme satisfies the all-test transporter equation. -/
theorem relativeTransporterHom_isTransporter :
    IsTransporter i₁ i₂ (relativeTransporterHom i₁ i₂) :=
  (twistedTransporter_isFixed_iff _ _ _).mp
    (CharacterAction.schemeActionFixedHom_isFixed _)

/-- Every affine-test transporter, including a specified field-valued point,
factors through the actual transporter scheme. -/
theorem exists_relativeTransporter_factor_iff {C : CommAlgCat.{u} R}
    (x : (algSpec R).obj (op C) ⟶ G.X) :
    (∃ y : (algSpec R).obj (op C) ⟶ relativeTransporterScheme i₁ i₂,
      y ≫ relativeTransporterHom i₁ i₂ = x) ↔ IsTransporter i₁ i₂ x := by
  rw [← twistedTransporter_isFixed_iff]
  exact CharacterAction.exists_schemeActionFixed_factor_iff _ _

/-- The actual transporter scheme is smooth, even when its fibres are empty. -/
theorem smooth_relativeTransporterScheme (hG : Smooth G.X.hom) :
    Smooth (relativeTransporterScheme i₁ i₂).hom :=
  CharacterAction.smooth_schemeActionFixedScheme _ hG

end PointwiseSchemeAction

end Langlands.GroupScheme
