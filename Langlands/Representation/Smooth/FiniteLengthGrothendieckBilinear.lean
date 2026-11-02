import Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Bilinear descent to actual exact Grothendieck groups

An actual bifunctor which preserves finite length and short exact sequences
separately induces a bilinear map, and hence a map from the tensor product of
the two exact Grothendieck groups. No assertion of bijectivity is built in.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.SmoothRep

universe uR uG uH uK uV uW uX uM

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {H : Type uH} [Group H] [TopologicalSpace H]
variable {K : Type uK} [Group K] [TopologicalSpace K]

namespace FiniteLengthGrothendieckGroup

variable {M : Type uM} [AddCommGroup M]

/-- Iterated exact-additive extension in two independent variables. -/
def lift₂ (a : FiniteLengthIsoClass.{uR, uG, uV} R G →
    FiniteLengthIsoClass.{uR, uH, uW} R H → M)
    (hleft : ∀ d, IsExactAdditive R G (fun c => a c d))
    (hright : ∀ c, IsExactAdditive R H (a c)) :
    FiniteLengthGrothendieckGroup.{uR, uG, uV} R G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{uR, uH, uW} R H →ₗ[ℤ] M :=
  lift R G (fun c => lift R H (a c) (hright c)) (by
    intro A B C f g h
    apply hom_ext R H
    intro d
    simp only [LinearMap.add_apply, lift_ofClass]
    exact hleft d A B C f g h)

@[simp]
theorem lift₂_ofClass (a : FiniteLengthIsoClass.{uR, uG, uV} R G →
    FiniteLengthIsoClass.{uR, uH, uW} R H → M)
    (hleft : ∀ d, IsExactAdditive R G (fun c => a c d))
    (hright : ∀ c, IsExactAdditive R H (a c))
    (c : FiniteLengthIsoClass.{uR, uG, uV} R G)
    (d : FiniteLengthIsoClass.{uR, uH, uW} R H) :
    lift₂ a hleft hright (ofClass R G c) (ofClass R H d) = a c d := by
  exact (congrArg (fun l : _ →ₗ[ℤ] M => l (ofClass R H d))
    (lift_ofClass R G (fun c => lift R H (a c) (hright c)) _ c)).trans
      (lift_ofClass R H (a c) (hright c) d)

/-- Bilinear maps are determined by their values on actual object pairs. -/
theorem bilinear_ext
    {f g : FiniteLengthGrothendieckGroup.{uR, uG, uV} R G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{uR, uH, uW} R H →ₗ[ℤ] M}
    (h : ∀ A B, f (ofObject A) (ofObject B) = g (ofObject A) (ofObject B)) :
    f = g := by
  apply hom_ext_object R G
  intro A
  apply hom_ext_object R H
  exact h A

end FiniteLengthGrothendieckGroup

variable (Φ : (SmoothRep.{uR, uG, uV} R G × SmoothRep.{uR, uH, uW} R H) ⥤
  SmoothRep.{uR, uK, uX} R K)

/-- Finite-length preservation for pairs of finite-length objects. -/
def PreservesFiniteLength₂ : Prop :=
  ∀ A B, A.HasFiniteLength → B.HasFiniteLength → (Φ.obj (A, B)).HasFiniteLength

/-- Exactness with a fixed finite-length right factor. -/
def PreservesFiniteLengthShortExactLeft : Prop :=
  ∀ (D : FiniteLengthObject.{uR, uH, uW} R H)
    (A B C : FiniteLengthObject.{uR, uG, uV} R G)
    (f : A.val.representation.IntertwiningMap B.val.representation)
    (g : B.val.representation.IntertwiningMap C.val.representation),
    IsShortExact f g →
      IsShortExact
        (hom (Φ.map (CategoryTheory.Prod.mkHom (ofHom f) (𝟙 D.val))))
        (hom (Φ.map (CategoryTheory.Prod.mkHom (ofHom g) (𝟙 D.val))))

/-- Exactness with a fixed finite-length left factor. -/
def PreservesFiniteLengthShortExactRight : Prop :=
  ∀ (D : FiniteLengthObject.{uR, uG, uV} R G)
    (A B C : FiniteLengthObject.{uR, uH, uW} R H)
    (f : A.val.representation.IntertwiningMap B.val.representation)
    (g : B.val.representation.IntertwiningMap C.val.representation),
    IsShortExact f g →
      IsShortExact
        (hom (Φ.map (CategoryTheory.Prod.mkHom (𝟙 D.val) (ofHom f))))
        (hom (Φ.map (CategoryTheory.Prod.mkHom (𝟙 D.val) (ofHom g))))

namespace FiniteLengthGrothendieckGroup

variable (hl : PreservesFiniteLength₂ Φ)

/-- The output class of the actual bifunctor on a pair of genuine classes. -/
def mapClass₂ (c : FiniteLengthIsoClass.{uR, uG, uV} R G)
    (d : FiniteLengthIsoClass.{uR, uH, uW} R H) :
    FiniteLengthGrothendieckGroup.{uR, uK, uX} R K :=
  Quotient.liftOn₂ c d
    (fun A B => ofRepresentation (Φ.obj (A.val, B.val)) (hl _ _ A.property B.property))
    (by
      intro A B A' B' hA hB
      obtain ⟨e⟩ := hA
      obtain ⟨f⟩ := hB
      exact ofObject_eq_of_iso (Φ.mapIso (Iso.prod e f)))

@[simp]
theorem mapClass₂_objects (A : FiniteLengthObject.{uR, uG, uV} R G)
    (B : FiniteLengthObject.{uR, uH, uW} R H) :
    mapClass₂ Φ hl (finiteLengthIsoClass A) (finiteLengthIsoClass B) =
      ofRepresentation (Φ.obj (A.val, B.val)) (hl _ _ A.property B.property) := rfl

theorem mapClass₂_exact_left (hx : PreservesFiniteLengthShortExactLeft Φ)
    (d : FiniteLengthIsoClass.{uR, uH, uW} R H) :
    IsExactAdditive R G (fun c => mapClass₂ Φ hl c d) := by
  induction d using Quotient.inductionOn with
  | h D =>
    intro A B C f g h
    exact ofRepresentation_shortExact _ _ _ (hx D A B C f g h)

theorem mapClass₂_exact_right (hx : PreservesFiniteLengthShortExactRight Φ)
    (c : FiniteLengthIsoClass.{uR, uG, uV} R G) :
    IsExactAdditive R H (mapClass₂ Φ hl c) := by
  induction c using Quotient.inductionOn with
  | h D =>
    intro A B C f g h
    exact ofRepresentation_shortExact _ _ _ (hx D A B C f g h)

/-- The bilinear map obtained by descending both actual exact relations. -/
def map₂ (hleft : PreservesFiniteLengthShortExactLeft Φ)
    (hright : PreservesFiniteLengthShortExactRight Φ) :
    FiniteLengthGrothendieckGroup.{uR, uG, uV} R G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{uR, uH, uW} R H →ₗ[ℤ]
        FiniteLengthGrothendieckGroup.{uR, uK, uX} R K :=
  lift₂ (mapClass₂ Φ hl) (mapClass₂_exact_left Φ hl hleft)
    (mapClass₂_exact_right Φ hl hright)

@[simp]
theorem map₂_objects (hleft : PreservesFiniteLengthShortExactLeft Φ)
    (hright : PreservesFiniteLengthShortExactRight Φ)
    (A : FiniteLengthObject.{uR, uG, uV} R G)
    (B : FiniteLengthObject.{uR, uH, uW} R H) :
    map₂ Φ hl hleft hright (ofObject A) (ofObject B) =
      ofRepresentation (Φ.obj (A.val, B.val)) (hl _ _ A.property B.property) :=
  lift₂_ofClass _ _ _ _ _

/-- The tensor comparison induced by the actual bifunctor. This is a map into
the exact K0 of the target group, not an asserted isomorphism. -/
def tensorMap (hleft : PreservesFiniteLengthShortExactLeft Φ)
    (hright : PreservesFiniteLengthShortExactRight Φ) :
    (FiniteLengthGrothendieckGroup.{uR, uG, uV} R G ⊗[ℤ]
      FiniteLengthGrothendieckGroup.{uR, uH, uW} R H) →ₗ[ℤ]
        FiniteLengthGrothendieckGroup.{uR, uK, uX} R K :=
  TensorProduct.lift (map₂ Φ hl hleft hright)

@[simp]
theorem tensorMap_objects (hleft : PreservesFiniteLengthShortExactLeft Φ)
    (hright : PreservesFiniteLengthShortExactRight Φ)
    (A : FiniteLengthObject.{uR, uG, uV} R G)
    (B : FiniteLengthObject.{uR, uH, uW} R H) :
    tensorMap Φ hl hleft hright (ofObject A ⊗ₜ[ℤ] ofObject B) =
      ofRepresentation (Φ.obj (A.val, B.val)) (hl _ _ A.property B.property) :=
  map₂_objects Φ hl hleft hright A B

end FiniteLengthGrothendieckGroup
end Langlands.SmoothRep
