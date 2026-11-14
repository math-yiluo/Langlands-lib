import Langlands.Geometry.FormalGroup.SpecialAtlasClassBaseChangeAlong
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlongComposition

/-! # Successive supplied coefficient maps on actual special-atlas classes -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S T : Type v} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra 𝒪[K] R] [Algebra 𝒪[K] S] [Algebra 𝒪[K] T]

/-- The special-atlas composition isomorphism is exactly the full-order formal comparison. -/
def baseAlongCompIso (X : SpecialAtlas K D ι R)
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T) :
    ((X.baseChangeAlong f).baseChangeAlong g).Iso (X.baseChangeAlong (g.comp f))
      (X.atlas.baseAlongCompOpens_eq f g) :=
  X.order.baseAlongCompIso f g

/-- The specified actual formal isomorphism realizes the entire-family composition square. -/
theorem baseAlongComp_onPoints (X : SpecialAtlas K D ι R)
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T) (A : CommAlgCat.{v} T)
    (x : X.Point (restrictCoefficientAlgebra (g.comp f) A)) :
    (X.baseAlongCompIso f g).onPoints A
      ((X.baseChangeAlong f).baseChangeAlongPointEquiv g A
        (X.baseChangeAlongPointEquiv f (restrictCoefficientAlgebra g A) x)) =
      X.baseChangeAlongPointEquiv (g.comp f) A x :=
  X.order.baseAlongComp_onPoints f g A x

/-- The same actual inverse realizes the reverse complete-family composition equation. -/
theorem baseAlongComp_inv_onPoints (X : SpecialAtlas K D ι R)
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T) (A : CommAlgCat.{v} T)
    (x : X.Point (restrictCoefficientAlgebra (g.comp f) A)) :
    ((X.baseAlongCompIso f g).onPoints A).symm
      (X.baseChangeAlongPointEquiv (g.comp f) A x) =
      (X.baseChangeAlong f).baseChangeAlongPointEquiv g A
        (X.baseChangeAlongPointEquiv f (restrictCoefficientAlgebra g A) x) :=
  X.order.baseAlongComp_inv_onPoints f g A x

/-- Successive supplied-map extensions compare by actual formal maps after refinement. -/
def baseAlongCompComparison (X : SpecialAtlas K D ι R)
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T) :
    Comparison ((X.baseChangeAlong f).baseChangeAlong g) (X.baseChangeAlong (g.comp f)) where
  left := BasicAtlas.CoverRefinement.refl _
  right := (BasicAtlas.CoverRefinement.refl _).retarget _ (X.atlas.baseAlongCompOpens_eq f g)
  sameCover := rfl
  coordinateIso := (X.baseAlongCompIso f g).restrict (BasicAtlas.CoverRefinement.refl _)

/-- The actual comparison identifies the successive and composite special-atlas classes. -/
theorem classOf_baseChangeAlong_comp (X : SpecialAtlas K D ι R)
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T) :
    classOf ((X.baseChangeAlong f).baseChangeAlong g) = classOf (X.baseChangeAlong (g.comp f)) :=
  classOf_eq_of_comparison (X.baseAlongCompComparison f g)

namespace IsoClass

/-- Supplied coefficient maps compose on the actual refined-comparison quotient. -/
theorem baseChangeAlong_comp (q : IsoClass (K := K) (D := D) (ι := ι) (R := R))
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T) :
    (q.baseChangeAlong f).baseChangeAlong g = q.baseChangeAlong (g.comp f) := by
  refine Quotient.inductionOn q ?_
  intro X
  exact classOf_baseChangeAlong_comp X f g

end IsoClass

namespace HeightSquaredAtlas

variable {π : 𝒪[K]}

/-- Both representatives retain their own actual height certificates under composition. -/
theorem classOf_baseChangeAlong_comp
    (X : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π)
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T) :
    classOf ((X.baseChangeAlong f).baseChangeAlong g) = classOf (X.baseChangeAlong (g.comp f)) :=
  classOf_eq_of_comparison (X.val.baseAlongCompComparison f g)

namespace IsoClass

/-- Supplied coefficient maps compose inside the actual height-certified quotient. -/
theorem baseChangeAlong_comp (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π)
    (f : R →ₐ[𝒪[K]] S) (g : S →ₐ[𝒪[K]] T) :
    (q.baseChangeAlong f).baseChangeAlong g = q.baseChangeAlong (g.comp f) := by
  refine Quotient.inductionOn q ?_
  intro X
  exact classOf_baseChangeAlong_comp X f g

end IsoClass
end HeightSquaredAtlas

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
