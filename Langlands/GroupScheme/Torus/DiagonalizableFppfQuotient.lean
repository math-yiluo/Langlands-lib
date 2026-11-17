import Langlands.GroupScheme.Torus.TranslationQuotient
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.NormalQuotientGroup
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Affine fppf quotients by diagonalizable normal subgroups -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Diagonalizable

/-- A finitely generated character group gives local finite presentation over
any ring, including torsion and non-Noetherian bases. -/
theorem locallyOfFinitePresentation (R : CommRingCat.{u}) (M : Type u)
    [AddCommGroup M] [AddGroup.FG M] :
    LocallyOfFinitePresentation (groupScheme R M).X.hom := by
  let R₀ := CommRingCat.of (ULift.{u} ℤ)
  let b := Gm.toSpecZ (Spec R)
  let e := baseChangeIso b M
  let : IsNoetherianRing R₀ :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : LocallyOfFinitePresentation (groupScheme R₀ M).X.hom := inferInstance
  have : LocallyOfFinitePresentation
      ((GroupScheme.baseChange b).obj (groupScheme R₀ M).toGrp).X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation
      (pullback.snd (groupScheme R₀ M).X.hom b))
  have : IsIso e.inv.hom.hom := (Grp.forget (Over (Spec R))).map_isIso e.inv
  have : IsIso e.inv.hom.hom.left :=
    (Over.forget (Spec R)).map_isIso e.inv.hom.hom
  rw [← Over.w e.inv.hom.hom]
  infer_instance

end Langlands.GroupScheme.Diagonalizable

namespace Langlands.GroupScheme.CharacterAction

instance quotientScheme_isAffine {R : CommRingCat.{u}} {M : Type u}
    [AddCommGroup M] {B : CommAlgCat.{u} R} (a : Action (M := M) B) :
    IsAffine (quotientScheme a).left := by
  change IsAffine (Spec _)
  infer_instance

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
variable {G : GroupScheme (Spec R)} [IsAffine G.X.left]
variable (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G)

/-- Local finite presentation descends from the actual translation relation. -/
theorem translationProjection_locallyOfFinitePresentation [AddGroup.FG M]
    (hi : IsClosedSubgroup i) :
    LocallyOfFinitePresentation (translationProjection i).left := by
  have := Diagonalizable.locallyOfFinitePresentation R M
  obtain ⟨hf, hs⟩ := translationProjection_flat_surjective i hi
  let := hf
  let := hs
  have hp := (translationProjection_isPullback i hi).map (Over.forget (Spec R))
  have hfpqc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (translationProjection i).left :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  apply MorphismProperty.of_isPullback_of_descendsAlong hp hfpqc
  exact inferInstanceAs (LocallyOfFinitePresentation
    (pullback.snd (Diagonalizable.groupScheme R M).X.hom G.X.hom))

variable (hi : IsClosedSubgroup i) (hn : (SubgroupFunctor.range i).IsNormal)

/-- The actual invariant spectrum with its descended normal quotient group
structure. -/
def quotientGroup : GroupScheme (Spec R) := by
  letI := (translationProjection_flat_surjective i hi).1
  letI := (translationProjection_flat_surjective i hi).2
  exact NormalQuotient.groupScheme G (SubgroupFunctor.range i) hn
    (translationProjection i) (translationProjection_fibers i hi hn)

/-- The actual projection as a group-scheme homomorphism. -/
def quotientHom : G ⟶ quotientGroup i hi hn := by
  letI := (translationProjection_flat_surjective i hi).1
  letI := (translationProjection_flat_surjective i hi).2
  exact NormalQuotient.hom G (SubgroupFunctor.range i) hn
    (translationProjection i) (translationProjection_fibers i hi hn)

/-- The quotient is affine over the original base. -/
theorem quotientGroup_isAffineHom : IsAffineHom (quotientGroup i hi hn).X.hom := by
  change IsAffineHom (quotientScheme (ofTranslation i)).hom
  infer_instance

/-- The projection is flat, surjective and locally finitely presented, and its
actual kernel has exactly the prescribed subgroup functor on every test. -/
theorem quotientHom_isFppfQuotient [AddGroup.FG M] :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) (quotientHom i hi hn) := by
  let := (translationProjection_flat_surjective i hi).1
  let := (translationProjection_flat_surjective i hi).2
  let := translationProjection_locallyOfFinitePresentation i hi
  exact NormalQuotient.isFppfQuotient G (SubgroupFunctor.range i) hn
    (translationProjection i) (translationProjection_fibers i hi hn)

end Langlands.GroupScheme.CharacterAction
