import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeAlong

/-! # Supplied scalar extension of actual special formal atlases -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S : Type v} [CommRing R] [CommRing S]

attribute [local instance] coefficientAlgebra coefficientScalarTower

section AlgebraTransport

variable {α : Algebra 𝒪[K] R}

/-- Retype all actual special data along equal scalar algebra structures. -/
def reAlgebra (X : (letI := α; SpecialAtlas K D ι R))
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := β; SpecialAtlas K D ι R) where
  atlas := letI := α; X.atlas.reAlgebra β e
  order := letI := α; X.order.reAlgebra β e
  unramified := letI := α; X.unramified
  tangent b := by
    cases e
    exact X.tangent b

/-- The underlying atlas is exactly the transported original atlas. -/
@[simp]
theorem reAlgebra_atlas (X : (letI := α; SpecialAtlas K D ι R))
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := β; (X.reAlgebra β e).atlas) = (letI := α; X.atlas.reAlgebra β e) := rfl

/-- The full division-order action is exactly the transported original action. -/
@[simp]
theorem reAlgebra_order (X : (letI := α; SpecialAtlas K D ι R))
    (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := β; (X.reAlgebra β e).order) = (letI := α; X.order.reAlgebra β e) := rfl

/-- Reflexive transport returns the original special atlas. -/
@[simp]
theorem reAlgebra_refl (X : (letI := α; SpecialAtlas K D ι R)) :
    X.reAlgebra α rfl = X := rfl

/-- Successive scalar retypings retain the same actual special data. -/
theorem reAlgebra_trans (X : (letI := α; SpecialAtlas K D ι R))
    (β γ : Algebra 𝒪[K] R) (e : α = β) (d : β = γ) :
    (X.reAlgebra β e).reAlgebra γ d = X.reAlgebra γ (e.trans d) := by
  cases e
  cases d
  rfl

/-- Retyping preserves both base nilpotence and every actual chart height. -/
theorem reAlgebra_height_iff (X : (letI := α; SpecialAtlas K D ι R))
    (β : Algebra 𝒪[K] R) (e : α = β) (π : 𝒪[K]) :
    (letI := β; (X.reAlgebra β e).HasHeightSquared π) ↔
      (letI := α; X.HasHeightSquared π) := by
  cases e
  rfl

/-- Scalar retyping identifies the entire compatible-family division-order modules. -/
def reAlgebraPointEquiv (X : (letI := α; SpecialAtlas K D ι R))
    (β : Algebra 𝒪[K] R) (e : α = β) (A : CommAlgCat.{v} R) :
    (letI := α; X.Point A) ≃ₗ[IntegerRing K D]
      (letI := β; (X.reAlgebra β e).Point A) :=
  letI := α; X.order.reAlgebraPointEquiv β e A

/-- Scalar retyping commutes with every map of coefficient tests. -/
theorem reAlgebraPointEquiv_natural (X : (letI := α; SpecialAtlas K D ι R))
    (β : Algebra 𝒪[K] R) (e : α = β) {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (x : (letI := α; X.Point A)) :
    (letI := β; (X.reAlgebra β e).order.mapPoints φ (X.reAlgebraPointEquiv β e A x)) =
      X.reAlgebraPointEquiv β e B (letI := α; X.order.mapPoints φ x) :=
  letI := α; X.order.reAlgebraPointEquiv_natural β e φ x

end AlgebraTransport

variable [Algebra 𝒪[K] R] [Algebra 𝒪[K] S]

/-- Extend a special atlas to the supplied target scalar structure. -/
def baseChangeAlong (X : SpecialAtlas K D ι R) (f : R →ₐ[𝒪[K]] S) :
    SpecialAtlas K D ι S :=
  (X.baseChange (BasicAtlas.coefficientTest f)).reAlgebra _
    (BasicAtlas.coefficientAlgebraAlong_eq f)

/-- The underlying atlas is exactly supplied-target coefficient extension. -/
@[simp]
theorem baseChangeAlong_atlas (X : SpecialAtlas K D ι R) (f : R →ₐ[𝒪[K]] S) :
    (X.baseChangeAlong f).atlas = X.atlas.baseChangeAlong f := rfl

/-- Every element of the division order acts by its supplied-target formal extension. -/
@[simp]
theorem baseChangeAlong_order (X : SpecialAtlas K D ι R) (f : R →ₐ[𝒪[K]] S) :
    (X.baseChangeAlong f).order = X.order.baseChangeAlong f := rfl

/-- The actual principal generators are the images under the supplied scalar map. -/
@[simp]
theorem baseChangeAlong_opens (X : SpecialAtlas K D ι R) (f : R →ₐ[𝒪[K]] S) :
    (X.baseChangeAlong f).atlas.opens = f '' X.atlas.opens := rfl

/-- Actual height d² and the nilpotent uniformizer image survive arbitrary scalar maps. -/
theorem baseChangeAlong_height (X : SpecialAtlas K D ι R) (f : R →ₐ[𝒪[K]] S)
    {π : 𝒪[K]} (h : X.HasHeightSquared π) : (X.baseChangeAlong f).HasHeightSquared π :=
  ((X.baseChange (BasicAtlas.coefficientTest f)).reAlgebra_height_iff _
    (BasicAtlas.coefficientAlgebraAlong_eq f) π).mpr
      (X.baseChange_height (BasicAtlas.coefficientTest f) h)

/-- The full compatible-family comparison retains the complete division-order action. -/
def baseChangeAlongPointEquiv (X : SpecialAtlas K D ι R) (f : R →ₐ[𝒪[K]] S)
    (A : CommAlgCat.{v} S) :
    X.Point (restrictCoefficientAlgebra f A) ≃ₗ[IntegerRing K D]
      (X.baseChangeAlong f).Point A :=
  X.order.baseChangeAlongPointEquiv f A

/-- Forgetting special data gives the exact basic-atlas family comparison. -/
theorem baseChangeAlongPointEquiv_eq (X : SpecialAtlas K D ι R)
    (f : R →ₐ[𝒪[K]] S) (A : CommAlgCat.{v} S)
    (x : X.Point (restrictCoefficientAlgebra f A)) :
    X.baseChangeAlongPointEquiv f A x = X.atlas.baseChangeAlongPointEquiv f A x :=
  X.order.baseChangeAlongPointEquiv_eq f A x

/-- The entire-family comparison is natural in all further coefficient maps. -/
theorem baseChangeAlongPointEquiv_natural (X : SpecialAtlas K D ι R)
    (f : R →ₐ[𝒪[K]] S) {A B : CommAlgCat.{v} S} (φ : A ⟶ B)
    (x : X.Point (restrictCoefficientAlgebra f A)) :
    (X.baseChangeAlong f).order.mapPoints φ (X.baseChangeAlongPointEquiv f A x) =
      X.baseChangeAlongPointEquiv f B
        (X.order.mapPoints (restrictCoefficientMap f φ) x) :=
  X.order.baseChangeAlongPointEquiv_natural f φ x

/-- Natural comparison of the actual division-order-module point functors. -/
def baseChangeAlongPointFunctorIso (X : SpecialAtlas K D ι R)
    (f : R →ₐ[𝒪[K]] S) :
    restrictCoefficientFunctor f ⋙ X.pointFunctor ≅
      (X.baseChangeAlong f).pointFunctor :=
  X.order.baseChangeAlongPointFunctorIso f

/-- Extend an actual same-cover full-order formal map to the supplied target. -/
def baseChangeAlongHom {X Y : SpecialAtlas K D ι R}
    {h : X.atlas.opens = Y.atlas.opens} (g : X.Hom Y h) (f : R →ₐ[𝒪[K]] S) :
    (X.baseChangeAlong f).Hom (Y.baseChangeAlong f)
      (BasicAtlas.baseOpens_eq (BasicAtlas.coefficientTest f) h) :=
  g.baseChangeAlong f

/-- Extend both formal maps and their two actual inverse equations. -/
def baseChangeAlongIso {X Y : SpecialAtlas K D ι R}
    {h : X.atlas.opens = Y.atlas.opens} (g : X.Iso Y h) (f : R →ₐ[𝒪[K]] S) :
    (X.baseChangeAlong f).Iso (Y.baseChangeAlong f)
      (BasicAtlas.baseOpens_eq (BasicAtlas.coefficientTest f) h) :=
  g.baseChangeAlong f

/-- The actual extended formal map realizes the entire-family square. -/
theorem baseChangeAlongHom_onPoints {X Y : SpecialAtlas K D ι R}
    {h : X.atlas.opens = Y.atlas.opens} (g : X.Hom Y h) (f : R →ₐ[𝒪[K]] S)
    (A : CommAlgCat.{v} S) (x : X.Point (restrictCoefficientAlgebra f A)) :
    (baseChangeAlongHom g f).onPoints A (X.baseChangeAlongPointEquiv f A x) =
      Y.baseChangeAlongPointEquiv f A (g.onPoints (restrictCoefficientAlgebra f A) x) :=
  g.baseChangeAlong_onPoints f A x

/-- Inverse family comparisons realize the reverse square for the same formal map. -/
theorem baseChangeAlongHom_fromPoints {X Y : SpecialAtlas K D ι R}
    {h : X.atlas.opens = Y.atlas.opens} (g : X.Hom Y h) (f : R →ₐ[𝒪[K]] S)
    (A : CommAlgCat.{v} S) (y : (X.baseChangeAlong f).Point A) :
    g.onPoints (restrictCoefficientAlgebra f A)
        ((X.baseChangeAlongPointEquiv f A).symm y) =
      (Y.baseChangeAlongPointEquiv f A).symm ((baseChangeAlongHom g f).onPoints A y) :=
  g.baseChangeAlong_fromPoints f A y

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
