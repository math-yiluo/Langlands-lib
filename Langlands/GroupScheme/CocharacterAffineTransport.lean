import Langlands.GroupScheme.CocharacterTransport
import Langlands.GroupScheme.AffinePointAutomorphisms

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
universe u

namespace Gm
variable {S : Scheme.{u}}

/-- Affine units are natural for any over-morphism with the specified spectrum map. -/
theorem affinePointsEquiv_naturality_of_left {R R' : CommRingCat.{u}}
    (φ : R ⟶ R') {f : Spec R ⟶ S} {g : Spec R' ⟶ S}
    (h : Over.mk g ⟶ Over.mk f) (hh : h.left = Spec.map φ)
    (x : Over.mk f ⟶ (Gm S).X) :
    affinePointsEquiv g (h ≫ x) = Units.map φ.hom.toMonoidHom (affinePointsEquiv f x) := by
  apply Units.ext
  rw [affinePointsEquiv_val, pointsEquiv_naturality]
  change ((h.left).appTop ≫ (Scheme.ΓSpecIso R').hom) _ =
    φ ((Scheme.ΓSpecIso R).hom _)
  rw [hh, Scheme.ΓSpecIso_naturality]
  rfl

/-- Reinterpreting a unit on another structural map leaves its affine coordinate unchanged. -/
theorem affinePointsEquiv_change_structure {R : CommRingCat.{u}}
    (f g : Spec R ⟶ S) (u : Rˣ) :
    (pointsEquiv S (Over.mk g)).symm
        (pointsEquiv S (Over.mk f) ((affinePointsEquiv f).symm u)) =
      (affinePointsEquiv g).symm u := by
  apply (affinePointsEquiv g).injective
  rw [MulEquiv.apply_symm_apply]
  change (Units.mapEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv)
    ((pointsEquiv S (Over.mk g)) ((pointsEquiv S (Over.mk g)).symm _)) = u
  rw [MulEquiv.apply_symm_apply]
  exact (affinePointsEquiv f).apply_symm_apply u

/-- Precomposition by an affine automorphism cancels its inverse on the unit coordinate. -/
theorem affinePointsEquiv_symm_aut {R : CommRingCat.{u}} (s : R →+* R)
    (t : R →* R) (hst : ∀ x, s (t x) = x)
    {f g : Spec R ⟶ S} (h : Over.mk g ⟶ Over.mk f)
    (hh : h.left = Spec.map (CommRingCat.ofHom s)) (u : Rˣ) :
    h ≫ (affinePointsEquiv f).symm (Units.map t u) =
      (affinePointsEquiv g).symm u := by
  apply (affinePointsEquiv g).injective
  calc
    _ = Units.map s.toMonoidHom
        (affinePointsEquiv f ((affinePointsEquiv f).symm (Units.map t u))) :=
      affinePointsEquiv_naturality_of_left (CommRingCat.ofHom s) h hh _
    _ = affinePointsEquiv g ((affinePointsEquiv g).symm u) := by
      simp only [MulEquiv.apply_symm_apply]
      apply Units.ext
      exact hst _

/-- The base automorphism as a morphism from the test scheme with changed structure. -/
def baseEndMap {R : Type u} [CommRing R] (s : R →+* R) :
    (Over.map (Spec.map (CommRingCat.ofHom s))).obj (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom s)) (by simp)

/-- Inverse coefficient change supplies the point with unchanged global unit. -/
theorem baseEndMap_points {R : Type u} [CommRing R] (s : R →+* R)
    (t : R →* R) (hst : ∀ x, s (t x) = x) (u : Rˣ) :
    baseEndMap s ≫ (affinePointsEquiv (𝟙 (Spec (CommRingCat.of R)))).symm (Units.map t u) =
      (pointsEquiv _ ((Over.map (Spec.map (CommRingCat.ofHom s))).obj
        (Over.mk (𝟙 (Spec (CommRingCat.of R)))))).symm
          (pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of R))))
            ((affinePointsEquiv (𝟙 (Spec (CommRingCat.of R)))).symm u)) := by
  let f := 𝟙 (Spec (CommRingCat.of R))
  let g := f ≫ Spec.map (CommRingCat.ofHom s)
  have h1 := affinePointsEquiv_symm_aut (R := CommRingCat.of R) (f := f) (g := g)
    s t hst (baseEndMap s) rfl u
  exact h1.trans (affinePointsEquiv_change_structure f g u).symm

end Gm

set_option backward.isDefEq.respectTransparency false in
/-- On underlying schemes, the transport formula is the unchanged-unit evaluation followed by projection. -/
theorem transportCocharacter_points_left {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S)
    (ha : a ≫ b = b) (G : GroupScheme B)
    (χ : (Gm S).toGrp ⟶ (Over.pullback b).mapGrp.obj G)
    (T : Over S) (x : T ⟶ (Gm S).X) :
    (x.left ≫ (transportCocharacter b a ha G χ).hom.hom.left) ≫ pullback.fst G.X.hom b =
      (((Gm.pointsEquiv S ((Over.map a).obj T)).symm (Gm.pointsEquiv S T x)).left ≫
        χ.hom.hom.left) ≫ pullback.fst G.X.hom b := by
  have hp := congrArg (fun k => k.left) (transportCocharacter_points b a ha G χ T x)
  change _ = 𝟙 T.left ≫ _ at hp
  simpa only [Category.id_comp, baseChangePointsEquiv_left, Over.comp_left] using hp

set_option backward.isDefEq.respectTransparency false in
/-- The projected base-point formula for a source point obtained by precomposition along a. -/
theorem transportCocharacter_base_points_left {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S)
    (ha : a ≫ b = b) (G : GroupScheme B)
    (χ : (Gm S).toGrp ⟶ (Over.pullback b).mapGrp.obj G)
    (p q : Over.mk (𝟙 S) ⟶ (Gm S).X)
    (h : (Over.map a).obj (Over.mk (𝟙 S)) ⟶ Over.mk (𝟙 S)) (hh : h.left = a)
    (hx : h ≫ q = (Gm.pointsEquiv S ((Over.map a).obj (Over.mk (𝟙 S)))).symm
      (Gm.pointsEquiv S (Over.mk (𝟙 S)) p)) :
    (baseChangeBasePointsEquiv b G (p ≫ (transportCocharacter b a ha G χ).hom.hom)).left =
      a ≫ (baseChangeBasePointsEquiv b G (q ≫ χ.hom.hom)).left := by
  simp only [baseChangeBasePointsEquiv_left, Over.comp_left]
  rw [transportCocharacter_points_left, ← hx]
  simp only [Over.comp_left, hh, Category.assoc]

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (G : GroupScheme (Spec (CommRingCat.of R)))

/-- On underlying schemes the coefficient action is precomposition with Spec(s). -/
theorem affinePointAut_left (s : S ≃ₐ[R] S)
    (x : (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R S)) ⟶ G.X) :
    (G.affinePointAut s x).left = Spec.map (CommRingCat.ofHom s.toRingHom) ≫ x.left := rfl

/-- Evaluate an actual cocharacter in the rational-base affine point model. -/
def affineCocharacterValue
    (χ : (Gm (Spec (CommRingCat.of S))).toGrp ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj G)
    (u : Sˣ) : (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R S)) ⟶ G.X :=
  baseChangeBasePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap R S))) G
    ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of S)))).symm u ≫ χ.hom.hom)

/-- Affine cocharacter evaluation is projection of its value on the base scheme. -/
theorem affineCocharacterValue_left
    (χ : (Gm (Spec (CommRingCat.of S))).toGrp ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj G)
    (u : Sˣ) :
    (G.affineCocharacterValue χ u).left =
      (((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of S)))).symm u).left ≫ χ.hom.hom.left) ≫
        pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  baseChangeBasePointsEquiv_left _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Projected transport along a coefficient endomorphism with a specified right inverse. -/
theorem affineCocharacterValue_transport_left (s : S →+* S)
    (t : S →* S) (hst : ∀ z, s (t z) = z)
    (χ : (Gm (Spec (CommRingCat.of S))).toGrp ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj G)
    (ha : Spec.map (CommRingCat.ofHom s) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
        Spec.map (CommRingCat.ofHom (algebraMap R S))) (u : Sˣ) :
    (G.affineCocharacterValue
        (transportCocharacter _ (Spec.map (CommRingCat.ofHom s)) ha G χ) u).left =
      Spec.map (CommRingCat.ofHom s) ≫
        (G.affineCocharacterValue χ (Units.map t u)).left := by
  rw [affineCocharacterValue_left, affineCocharacterValue_left,
    transportCocharacter_points_left]
  have hx := congrArg (fun k => k.left) (Gm.baseEndMap_points s t hst u)
  change Spec.map (CommRingCat.ofHom s) ≫
    ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of S)))).symm (Units.map t u)).left = _ at hx
  rw [← hx]
  simp only [Category.assoc]


set_option backward.isDefEq.respectTransparency false in
/-- Cocharacter transport evaluates as s applied to the old value at s inverse of the unit. -/
theorem affineCocharacterValue_transport (s : S ≃ₐ[R] S)
    (χ : (Gm (Spec (CommRingCat.of S))).toGrp ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj G)
    (ha : Spec.map (CommRingCat.ofHom s.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
        Spec.map (CommRingCat.ofHom (algebraMap R S))) (u : Sˣ) :
    G.affineCocharacterValue
        (transportCocharacter _ (Spec.map (CommRingCat.ofHom s.toRingHom)) ha G χ) u =
      G.affinePointAut s (G.affineCocharacterValue χ (Units.map s.symm.toMonoidHom u)) := by
  apply Over.OverMorphism.ext
  exact (G.affineCocharacterValue_transport_left s.toRingHom s.symm.toMonoidHom
    (fun z => s.apply_symm_apply z) χ ha u).trans (G.affinePointAut_left s _).symm

end Langlands.GroupScheme
