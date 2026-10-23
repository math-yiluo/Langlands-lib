import Langlands.Geometry.Analytic.StrictTestDomain.RationalBaseChange
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Continuity of base change on finite rational sites -/

noncomputable section

universe u v w

namespace Langlands.Analytic.StrictTestDomain.RationalData

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P Q : PresentedStrictAffinoidAlgebra K}

omit [CompleteSpace K] in
private theorem hom_unique {B : PresentedStrictAffinoidAlgebra K}
    {d e : RationalData K B} (f g : d ⟶ e) : f = g :=
  (inferInstance : Subsingleton (Inclusion d e)).elim f g

omit [CompleteSpace K] in
@[simp]
theorem locus_pullback_whole (φ : BoundedAlgHom K P Q) :
    ((whole K P).pullback φ).locus = Set.univ := by
  rw [locus_pullback, locus_whole, Set.preimage_univ]

@[simp]
theorem locus_pullback_inter (d e : RationalData K P) (φ : BoundedAlgHom K P Q) :
    ((d.inter e).pullback φ).locus =
      (d.pullback φ).locus ∩ (e.pullback φ).locus := by
  rw [locus_pullback, locus_inter, Set.preimage_inter]
  rfl

/-- Every locus over Q maps to the inverse image of the whole spectrum of P. -/
def toPullbackWhole (φ : BoundedAlgHom K P Q) (d : RationalData K Q) :
    d ⟶ (whole K P).pullback φ :=
  ⟨by rw [locus_pullback_whole]; exact Set.subset_univ _⟩

/-- The image of the explicit whole-spectrum object is terminal. -/
def pullbackWholeIsTerminal (φ : BoundedAlgHom K P Q) :
    IsTerminal ((whole K P).pullback φ) :=
  IsTerminal.ofUniqueHom (toPullbackWhole φ) (fun _ _ => hom_unique _ _)

/-- Construct the lift into the inverse image of an intersection. -/
def pullbackInterLift (φ : BoundedAlgHom K P Q) {c : RationalData K Q}
    {d e : RationalData K P} (f : c ⟶ d.pullback φ) (g : c ⟶ e.pullback φ) :
    c ⟶ (d.inter e).pullback φ :=
  ⟨by rw [locus_pullback_inter]; exact fun _ hx => ⟨f.subset hx, g.subset hx⟩⟩

/-- Base change commutes with the chosen intersection up to the actual
isomorphism supplied by equality of its loci. -/
def pullbackInterIso (d e : RationalData K P) (φ : BoundedAlgHom K P Q) :
    (d.inter e).pullback φ ≅ (d.pullback φ).inter (e.pullback φ) where
  hom := interLift ((interLeft d e).pullback φ) ((interRight d e).pullback φ)
  inv := pullbackInterLift φ (interLeft _ _) (interRight _ _)
  hom_inv_id := hom_unique _ _
  inv_hom_id := hom_unique _ _

/-- The image of the constructed intersection cone is a pullback cone. -/
def pullbackMapConeIsLimit (φ : BoundedAlgHom K P Q)
    {d e t : RationalData K P} (f : d ⟶ t) (g : e ⟶ t) :
    IsLimit ((pullbackCone f g).map (pullbackFunctor φ)) :=
  PullbackCone.IsLimit.mk _ (fun s => pullbackInterLift φ s.fst s.snd)
    (fun _ => hom_unique _ _) (fun _ => hom_unique _ _)
    (fun _ _ _ _ => hom_unique _ _)

/-- Base change preserves terminal objects in the rational inclusion category. -/
instance pullbackFunctor_preservesTerminal (φ : BoundedAlgHom K P Q) :
    PreservesLimit (Functor.empty.{0} (RationalData K P)) (pullbackFunctor φ) :=
  preservesLimit_of_preserves_limit_cone wholeIsTerminal
    ((isLimitMapConeEmptyConeEquiv _ _).symm (pullbackWholeIsTerminal φ))

/-- Base change preserves the pullback of any pair of rational inclusions. -/
instance pullbackFunctor_preservesPullback (φ : BoundedAlgHom K P Q)
    {d e t : RationalData K P} (f : d ⟶ t) (g : e ⟶ t) :
    PreservesLimit (cospan f g) (pullbackFunctor φ) :=
  preservesLimit_of_preserves_limit_cone (pullbackConeIsLimit f g)
    (((pullbackCone f g).isLimitMapConeEquiv _).symm (pullbackMapConeIsLimit φ f g))

/-- Any pair of arrows to pulled-back domains factors through the pulled-back
intersection, so compatible families remain compatible. -/
theorem pullbackFunctor_compatiblePreserving (φ : BoundedAlgHom K P Q) :
    CompatiblePreserving.{w} (finiteRationalTopology K Q) (pullbackFunctor φ) := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ _
  let l : X ⟶ (pullbackFunctor φ).obj (Y₁.inter Y₂) := pullbackInterLift φ f₁ f₂
  have h := hx (interLeft Y₁ Y₂) (interRight Y₁ Y₂) hg₁ hg₂ (hom_unique _ _)
  have h' := congrArg (ℱ.obj.map l.op) h
  have e₁ : l ≫ (pullbackFunctor φ).map (interLeft Y₁ Y₂) = f₁ := hom_unique _ _
  have e₂ : l ≫ (pullbackFunctor φ).map (interRight Y₁ Y₂) = f₂ := hom_unique _ _
  rw [← e₁, ← e₂, op_comp, op_comp, ℱ.obj.map_comp, ℱ.obj.map_comp]
  exact h'

/-- Rational base change is continuous for the finite rational topologies. -/
instance pullbackFunctor_isContinuous (φ : BoundedAlgHom K P Q) :
    (pullbackFunctor φ).IsContinuous
      (finiteRationalTopology K P) (finiteRationalTopology K Q) :=
  Functor.isContinuous_of_coverPreserving
    (pullbackFunctor_compatiblePreserving φ) (pullbackFunctor_coverPreserving φ)

/-- Precomposition with rational base change carries sheaves over Q to sheaves
over P, for any coefficient category. -/
def rationalSheafPushforward (φ : BoundedAlgHom K P Q)
    (A : Type v) [Category.{w} A] :
    Sheaf (finiteRationalTopology K Q) A ⥤ Sheaf (finiteRationalTopology K P) A :=
  (pullbackFunctor φ).sheafPushforwardContinuous A
    (finiteRationalTopology K P) (finiteRationalTopology K Q)

end Langlands.Analytic.StrictTestDomain.RationalData
