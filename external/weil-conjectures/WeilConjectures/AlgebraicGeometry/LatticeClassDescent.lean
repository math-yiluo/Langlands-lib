/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite

public import WeilConjectures.AlgebraicGeometry.LatticeSheafBasic
import WeilConjectures.AlgebraicGeometry.LatticePairEffectiveDescent

/-!
# Descent of integral lattice classes

Source: Bhatt--Scholze, Proposition 6.8.4(6), pp. 59--60
(auxiliary; not a blueprint node).
-/

@[expose] public section

attribute [local instance] AlgebraicGeometry.ProEtale.latticeWeakSheafifyOver
  AlgebraicGeometry.Scheme.strictPerfectSliceLocallyBijective

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Integral lattice pairs admit an exact sheaf presentation by embedded images.
Source: Bhatt--Scholze, Proposition 6.8.4(6), descent of lattice pairs
(auxiliary; not a blueprint node).
Proof: use the presheaf of image families represented by actual integral lattice pairs.
The slice tensor comparison restricts pairs and their images. Equality of these image
families is equivalent to intertwining integral isomorphism by image classification.
Membership in each image is local, since a locally lifted section glues uniquely
using injectivity of the integral embedding. This proves separatedness of the image
presheaf. Effective descent supplies a representative for every compatible family,
so the presheaf is a sheaf. Its class maps are surjective by their definition; image
classification proves their exact kernel relation, and the restriction clause is
exactly the definition of the presheaf maps. No rank condition on L is used. -/
theorem exists_latticeClassPresentation (X : Scheme.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))) :
    ∃ (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
      (c : ∀ U : X.ProEt,
        IntegralLatticePair (integralLatticeCoefficientMap X l E) L U → F.obj.obj (op U)),
      IsLatticeClassPresentation (integralLatticeCoefficientMap X l E) L F c := by
  let a := integralLatticeCoefficientMap X l E
  have ha (U : X.ProEt) (T : (Over U)ᵒᵖ) :
      Function.Injective (((latticeScalarMap a U).hom.app T).hom) := by
    intro f g h
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun s ↦ s.down x) h
  have hs : Presieve.IsSheaf (Scheme.ProEt.topology X) (latticeClassPresheaf a L) := by
    intro U r hr x hx
    obtain ⟨P, hP⟩ := exists_latticePair_of_compatible_classes a L ha U r hr x hx
    let t := ULift.up (latticeImageClass a L U P)
    have ht : x.IsAmalgamation t := by
      intro V f hf
      apply ULift.ext
      apply Subtype.ext
      funext T
      exact hP V f hf T
    exact ⟨t, ht, fun t' ht' ↦
      latticeClassPresheaf_isSeparated a L ha r hr x t' t ht' ht⟩
  let F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)) :=
    ⟨latticeClassPresheaf a L, (isSheaf_iff_isSheaf_of_type _ _).mpr hs⟩
  let c (U : X.ProEt) (P : IntegralLatticePair a L U) : F.obj.obj (op U) :=
    ULift.up (latticeImageClass a L U P)
  refine ⟨F, c, ?_, ?_, ?_⟩
  · intro U s
    obtain ⟨P, hP⟩ := s.down.property
    refine ⟨P, ?_⟩
    apply ULift.ext
    apply Subtype.ext
    funext T
    exact hP T
  · intro U P Q
    rw [integralLatticePair_equivalent_iff_image_eq U l E L P Q]
    constructor
    · intro h T
      exact congrArg (fun s ↦ s.down.val T.unop) h
    · intro h
      apply ULift.ext
      apply Subtype.ext
      funext T
      exact h (op T)
  · intro U V f P Q
    constructor
    · intro h T
      exact congrArg (fun s ↦ s.down.val T) h
    · intro h
      apply ULift.ext
      apply Subtype.ext
      funext T
      exact h T

end AlgebraicGeometry.ProEtale
