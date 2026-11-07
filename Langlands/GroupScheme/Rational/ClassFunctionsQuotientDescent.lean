import Langlands.GroupScheme.Rational.ClassFunctionsBaseChange
import Langlands.GroupScheme.Rational.SteinbergRootProduct
import Langlands.GroupScheme.BaseChangeReflection

/-! # Detection of the actual quotient-isomorphism property after field extension -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

private theorem isIso_overMap_of_fpqc_pullback {S S' : Scheme.{u}} (b : S' ⟶ S)
    [Surjective b] [Flat b] [QuasiCompact b] {X Y : Over S} (f : X ⟶ Y)
    [IsIso ((Over.pullback b).map f)] : IsIso f := by
  have : IsIso ((Over.pullback b).map f).left :=
    inferInstanceAs (IsIso ((Over.forget S').map ((Over.pullback b).map f)))
  have houter : IsPullback
      (((Over.pullback b).map f).left ≫ pullback.snd Y.hom b)
      (pullback.fst X.hom b) b (f.left ≫ Y.hom) := by
    simpa only [Over.w f, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback X.hom b).flip
  have hp := houter.of_right
    (show ((Over.pullback b).map f).left ≫ pullback.fst Y.hom b =
        pullback.fst X.hom b ≫ f.left by
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback Y.hom b).flip
  have : IsIso f.left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have : IsIso ((Over.forget S).map f) := by
    change IsIso f.left
    infer_instance
  exact isIso_of_reflects_iso f (Over.forget S)

namespace ClassFunctions.BaseChange

variable (K F : Type u) [Field K] [Field F] [Algebra K F]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]

local notation "b" => algebraBaseMap K F
local notation "GF" => Functor.obj (GroupScheme.baseChange b) G

local instance : IsAffineHom (GF).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

/-- The scalar extension of a supplied actual morphism followed by the new canonical quotient. -/
def quotientComposite {X : Over (Spec (CommRingCat.of K))} (f : X ⟶ G.X) :
    (Over.pullback b).obj X ⟶ ClassFunctions.quotient GF :=
  (Over.pullback b).map f ≫ ClassFunctions.rho GF

/-- The actual quotient comparison identifies this composite with the pullback of the original. -/
theorem quotientComposite_eq {X : Over (Spec (CommRingCat.of K))} (f : X ⟶ G.X) :
    quotientComposite K F G f =
      (Over.pullback b).map (f ≫ ClassFunctions.rho G) ≫
        (quotientComparison K F G).hom := by
  rw [Functor.map_comp, Category.assoc, quotientComparison_rho]
  rfl

/-- Every extension field detects the actual canonical-quotient isomorphism property,
without any reductivity or splitness hypothesis. -/
theorem isIso_quotientComposite_iff {X : Over (Spec (CommRingCat.of K))} (f : X ⟶ G.X) :
    IsIso (quotientComposite K F G f) ↔ IsIso (f ≫ ClassFunctions.rho G) := by
  rw [quotientComposite_eq, isIso_comp_right_iff]
  constructor
  · intro h
    let := h
    obtain ⟨hs, hf, hqc⟩ := fieldExtension_fpqc K F
    let := hs
    let := hf
    let := hqc
    exact isIso_overMap_of_fpqc_pullback b (f ≫ ClassFunctions.rho G)
  · intro h
    let := h
    infer_instance

end ClassFunctions.BaseChange

namespace SplitPinning

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {r : ℕ} (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations) (n : p.SimpleReflectionRepresentatives)

/-- The original supplied Steinberg morphism satisfies the desired property exactly when
its actual scalar extension followed by the new canonical quotient does. -/
theorem isIso_steinbergQuotient_fieldExtension_iff :
    IsIso (ClassFunctions.BaseChange.quotientComposite k F G (steinbergProduct e x n)) ↔
      IsIso (steinbergProduct e x n ≫ ClassFunctions.rho G) :=
  ClassFunctions.BaseChange.isIso_quotientComposite_iff k F G (steinbergProduct e x n)

end SplitPinning

end Langlands.GroupScheme
