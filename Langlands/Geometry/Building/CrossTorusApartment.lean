import Langlands.Geometry.Building.CrossTorusApartmentData

/-! # Actual valuation apartments under cross-torus isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {ω : kˣ → ℝ}
  (e : S ≅ S') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
  (D : KPApartmentData i ω)

/-- Reindex the actual valuation point in the entire transported apartment class. -/
def apartmentTransportEquiv : D.Apartment ≃ (D.transport e f h).Apartment where
  toFun x := ⟨RootFunctionFamily.transportEquiv e f x.val, ⟨x.val, x.mem, rfl⟩⟩
  invFun y := ⟨(RootFunctionFamily.transportEquiv e f).symm y.val,
    (mem_transport_iff e f h D y.val).mp y.mem⟩
  left_inv x := Apartment.ext (Equiv.symm_apply_apply _ x.val)
  right_inv y := Apartment.ext (Equiv.apply_symm_apply _ y.val)

/-- The forward point has exactly the transported full valuation family. -/
@[simp] theorem apartmentTransportEquiv_val (x : D.Apartment) :
    (D.apartmentTransportEquiv e f h x).val =
      RootFunctionFamily.transportEquiv e f x.val := rfl

/-- The inverse point uses the inverse of the same full family equivalence. -/
@[simp] theorem apartmentTransportEquiv_symm_val
    (y : (D.transport e f h).Apartment) :
    ((D.apartmentTransportEquiv e f h).symm y).val =
      (RootFunctionFamily.transportEquiv e f).symm y.val := rfl

/-- Every actual point value is unchanged on simultaneous transported inputs. -/
@[simp] theorem apartmentTransportEquiv_value (x : D.Apartment)
    (a : characterLattice S) (g : rationalPoints G) :
    (D.apartmentTransportEquiv e f h x).val (characterLattice.congr e a)
        (rationalPoints.map f.hom g) = x.val a g :=
  RootFunctionFamily.transportEquiv_apply_map e f x.val a g

/-- Point transport intertwines the existing quotient translation actions. -/
theorem apartmentTransportEquiv_vadd (v : TranslationSpace i) (x : D.Apartment) :
    D.apartmentTransportEquiv e f h (v +ᵥ x) =
      translationSpaceTransportEquiv e f h v +ᵥ D.apartmentTransportEquiv e f h x := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  apply Apartment.ext
  change RootFunctionFamily.transportEquiv e f (w +ᵥ x.val) =
    cocharacterRealCongr e w +ᵥ RootFunctionFamily.transportEquiv e f x.val
  exact RootFunctionFamily.transportEquiv_vadd e f x.val w

/-- Point transport intertwines the original actions of the actual normalizer points. -/
theorem apartmentTransportEquiv_smul (n : normalizerPoints i) (x : D.Apartment) :
    D.apartmentTransportEquiv e f h (n • x) =
      normalizerPointsTransportEquiv e f h n • D.apartmentTransportEquiv e f h x := by
  apply Apartment.ext
  exact RootFunctionFamily.transportEquiv_smul e f h n x.val

/-- The actual valuation-point equivalence is affine with the actual quotient derivative. -/
def apartmentTransportAffineEquiv :
    D.Apartment ≃ᵃ[ℝ] (D.transport e f h).Apartment where
  toEquiv := D.apartmentTransportEquiv e f h
  linear := translationSpaceTransportEquiv e f h
  map_vadd' x v := D.apartmentTransportEquiv_vadd e f h v x

/-- The affine constructor retains the original point map. -/
@[simp] theorem apartmentTransportAffineEquiv_toEquiv :
    (D.apartmentTransportAffineEquiv e f h).toEquiv =
      D.apartmentTransportEquiv e f h := rfl

/-- The derivative is exactly the existing map on reduced translations. -/
@[simp] theorem apartmentTransportAffineEquiv_linear :
    (D.apartmentTransportAffineEquiv e f h).linear =
      translationSpaceTransportEquiv e f h := rfl

/-- Displacement of valuation points follows the same actual quotient map. -/
theorem apartmentTransportAffineEquiv_vsub (x y : D.Apartment) :
    translationSpaceTransportEquiv e f h (x -ᵥ y) =
      D.apartmentTransportAffineEquiv e f h x -ᵥ
        D.apartmentTransportAffineEquiv e f h y :=
  (D.apartmentTransportAffineEquiv e f h).toAffineMap.linearMap_vsub x y

/-- The original normalizer affine automorphisms commute with point transport. -/
theorem apartmentTransportAffineEquiv_normalizer (n : normalizerPoints i) :
    (D.normalizerAffineEquiv n).trans (D.apartmentTransportAffineEquiv e f h) =
      (D.apartmentTransportAffineEquiv e f h).trans
        ((D.transport e f h).normalizerAffineEquiv
          (normalizerPointsTransportEquiv e f h n)) := by
  apply AffineEquiv.ext
  intro x
  exact D.apartmentTransportEquiv_smul e f h n x

/-- Membership in the original pointwise filtration is preserved and reflected. -/
theorem mem_filtration_apartmentTransport_iff (x : D.Apartment)
    (a : characterLattice S) (r : ℝ) (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈
        (D.transport e f h).filtration (D.apartmentTransportEquiv e f h x)
          (characterLattice.congr e a) r ↔
      g ∈ D.filtration x a r :=
  rootFiltration_transport_iff e f h x.val a r g

/-- The actual ambient homomorphism maps the entire pointwise filtration subgroup onto it. -/
theorem map_filtration_apartmentTransport (x : D.Apartment)
    (a : characterLattice S) (r : ℝ) :
    (D.filtration x a r).map (rationalPoints.map f.hom) =
      (D.transport e f h).filtration (D.apartmentTransportEquiv e f h x)
        (characterLattice.congr e a) r := by
  apply SetLike.ext'
  change rationalPoints.map f.hom '' rootFiltration i x.val a r =
    rootFiltration j (RootFunctionFamily.transportEquiv e f x.val)
      (characterLattice.congr e a) r
  exact image_rootFiltration_transport e f h x.val a r

end Langlands.Geometry.Building.KPApartmentData
