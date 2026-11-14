import Langlands.GroupScheme.Rational.CharacterGaloisAction
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.CocharacterTransportNaturality
import Mathlib.RepresentationTheory.Rep.Basic

/-! # The contravariant Galois character functor

The actual characters after base change, with their canonical automorphism action,
form an integral representation contravariantly in the original commutative group scheme.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

section Transport

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)

namespace characterLattice

/-- Transport of actual additive characters is natural in the original group. -/
theorem transport_naturality {H G : CommGroupScheme B} (f : H ⟶ G)
    (χ : characterLattice ((CommGroupScheme.baseChange b).obj G)) :
    transport b a ha H ((CommGroupScheme.baseChange b).map f ≫ χ) =
      (CommGroupScheme.baseChange b).map f ≫ transport b a ha G χ :=
  congrArg Additive.ofMul
    (transportCharacter_naturality b a ha (CommGroupScheme.groupHom f)
      (CommGroupScheme.groupHom χ))

end characterLattice

end Transport

namespace characterLattice

/-- Pullback of actual characters, as an integral linear map. -/
def pullback {S : Scheme.{u}} {H G : CommGroupScheme S} (f : H ⟶ G) :
    characterLattice G →ₗ[ℤ] characterLattice H :=
  (Preadditive.leftComp (Gm S) f).toIntLinearMap

@[simp]
theorem pullback_apply {S : Scheme.{u}} {H G : CommGroupScheme S}
    (f : H ⟶ G) (χ : characterLattice G) : pullback f χ = f ≫ χ := rfl

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]

/-- Actual base-changed characters equipped with the published canonical action. -/
def galoisRep (T : CommGroupScheme (Spec (CommRingCat.of k))) :
    Rep.{u} ℤ (K ≃ₐ[k] K) :=
  Rep.of (galoisRepresentation k K T)

/-- Character pullback along a ground-ring map commutes with the canonical action. -/
theorem galoisRepresentation_naturality
    {H G : CommGroupScheme (Spec (CommRingCat.of k))} (f : H ⟶ G)
    (σ : K ≃ₐ[k] K)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    galoisRepresentation k K H σ
        ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f ≫ χ) =
      (CommGroupScheme.baseChange (algebraBaseMap k K)).map f ≫
        galoisRepresentation k K G σ χ :=
  transport_naturality (algebraBaseMap k K) (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) f χ

/-- Pullback of base-changed characters as a morphism of integral representations. -/
def galoisPullback
    {H G : CommGroupScheme (Spec (CommRingCat.of k))} (f : H ⟶ G) :
    galoisRep k K G ⟶ galoisRep k K H :=
  Rep.ofHom
    ((pullback ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f)).intertwiningMap_of_isIntertwiningMap
        (galoisRepresentation k K G) (galoisRepresentation k K H)
        (fun σ χ => (galoisRepresentation_naturality k K f σ χ).symm))

@[simp]
theorem galoisPullback_apply
    {H G : CommGroupScheme (Spec (CommRingCat.of k))} (f : H ⟶ G)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    (galoisPullback k K f).hom χ =
      (CommGroupScheme.baseChange (algebraBaseMap k K)).map f ≫ χ := rfl

/-- The contravariant functor of actual characters with their canonical automorphism
action. No splitting or finiteness assumption is needed for this construction. -/
def galoisFunctor :
    (CommGroupScheme (Spec (CommRingCat.of k)))ᵒᵖ ⥤ Rep.{u} ℤ (K ≃ₐ[k] K) where
  obj T := galoisRep k K T.unop
  map f := galoisPullback k K f.unop
  map_id T := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro χ
    change (CommGroupScheme.baseChange (algebraBaseMap k K)).map (𝟙 T.unop) ≫ χ = χ
    simp
  map_comp f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro χ
    change (CommGroupScheme.baseChange (algebraBaseMap k K)).map (g.unop ≫ f.unop) ≫ χ =
      (CommGroupScheme.baseChange (algebraBaseMap k K)).map g.unop ≫
        ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f.unop ≫ χ)
    simp only [Functor.map_comp, Category.assoc]

@[simp]
theorem galoisFunctor_map_apply
    {H G : (CommGroupScheme (Spec (CommRingCat.of k)))ᵒᵖ} (f : H ⟶ G)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj H.unop)) :
    ((galoisFunctor k K).map f).hom χ =
      (CommGroupScheme.baseChange (algebraBaseMap k K)).map f.unop ≫ χ := rfl

end characterLattice

end Langlands.GroupScheme
