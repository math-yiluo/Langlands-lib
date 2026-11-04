import Langlands.GroupScheme.Dynamic.UnipotentWeightFiltration
import Langlands.GroupScheme.Rational.CyclicWeightConjugation
import Langlands.GroupScheme.Rational.CyclicWeightFiltrationProof

/-! # Points of an affine group read in its corepresented model -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic.GradedCoordinates

open Corepresented RelativeRoot

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- Points of `G` with coefficients in `A`, read in the corepresented model. -/
def modelPoint (A : CommAlgCat.{u} (CommRingCat.of k)) :
    G.affinePoints A →* (AffineCoordinates.functor G).obj A :=
  (affinePointsEquiv (AffineCoordinates.functor G) (AffineCoordinates.corepresentation G)
    A).toMonoidHom.comp (G.affinePointsTarget (AffineCoordinates.groupSchemeIso G).inv A)

theorem modelPoint_apply (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A) :
    modelPoint G A x = affinePointsEquiv (AffineCoordinates.functor G)
      (AffineCoordinates.corepresentation G) A (x ≫ (AffineCoordinates.groupSchemeIso G).inv.hom.hom) :=
  rfl

theorem modelPoint_naturality {A A' : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ A')
    (x : G.affinePoints A) :
    modelPoint G A' ((algSpec (CommRingCat.of k)).map f.op ≫ x) =
      (AffineCoordinates.functor G).map f (modelPoint G A x) := by
  rw [modelPoint_apply, modelPoint_apply, Category.assoc, affinePointsEquiv_naturality]

theorem modelPoint_injective (A : CommAlgCat.{u} (CommRingCat.of k)) :
    Function.Injective (modelPoint G A) := by
  intro x y h
  rw [modelPoint_apply, modelPoint_apply] at h
  have h' := (affinePointsEquiv _ _ A).injective h
  have := congrArg (· ≫ (AffineCoordinates.groupSchemeIso G).hom.hom.hom) h'
  simpa only [Category.assoc, iso_inv_hom_hom, Category.comp_id] using this

theorem modelPoint_surjective (A : CommAlgCat.{u} (CommRingCat.of k)) :
    Function.Surjective (modelPoint G A) := by
  intro y
  refine ⟨(affinePointsEquiv _ _ A).symm y ≫ (AffineCoordinates.groupSchemeIso G).hom.hom.hom, ?_⟩
  rw [modelPoint_apply, Category.assoc, iso_hom_inv_hom, Category.comp_id,
    MulEquiv.apply_symm_apply]

section Torus

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {I : Type u} [Fintype I] [DecidableEq I]
  (φ : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) (b : AutomorphicAction S.toGrp G)

/-- Membership of an affine point in a weight subgroup functor, read in the model. -/
theorem mem_weightSubgroupFunctor_iff (P : AddSubsemigroup (I → ℤ))
    {A : CommAlgCat.{u} (CommRingCat.of k)} (x : G.affinePoints A) :
    x ∈ (weightSubgroupFunctor (AffineCoordinates.corepresentation G)
        (AffineCoordinates.groupSchemeIso G) φ b P).carrier ((algSpec (CommRingCat.of k)).obj (op A)) ↔
      modelPoint G A x ∈ weightSubgroup (AffineCoordinates.corepresentation G)
        (modelAction (AffineCoordinates.corepresentation G) (AffineCoordinates.groupSchemeIso G) φ b)
        P A := by
  rw [mem_weightSubgroupFunctor, pointsEquiv_eq_affinePointsEquiv, ← modelPoint_apply]
  constructor
  · intro h
    have h' := map_mem_weightSubgroup _ _ P (affineSectionsIso A).hom h
    rwa [← CategoryTheory.comp_apply, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      CategoryTheory.id_apply] at h'
  · intro h
    exact map_mem_weightSubgroup _ _ P (affineSectionsIso A).inv h

omit [DecidableEq I] in
/-- The model torus action on model points is the original action. -/
theorem modelAction_act_modelPoint {A : CommAlgCat.{u} (CommRingCat.of k)} (t : I → Aˣ)
    (x : G.affinePoints A) :
    (modelAction (AffineCoordinates.corepresentation G) (AffineCoordinates.groupSchemeIso G) φ b).act t
        (modelPoint G A x) =
      modelPoint G A (b.act (torusPt I A t ≫ φ.inv.hom.hom) x) := by
  change affinePointsEquiv _ _ A ((b.transport φ.inv (AffineCoordinates.groupSchemeIso G)).act
      (torusPt I A t) ((affinePointsEquiv _ _ A).symm (modelPoint G A x))) = _
  rw [modelPoint_apply, MulEquiv.symm_apply_apply, AutomorphicAction.transport_act, Category.assoc,
    iso_inv_hom_hom, Category.comp_id, modelPoint_apply]

end Torus

section Fixed

/-- The structure map of an affine test scheme to the identity test object. -/
def toBase (A : CommAlgCat.{u} (CommRingCat.of k)) :
    (algSpec (CommRingCat.of k)).obj (op A) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
  Over.homMk ((algSpec (CommRingCat.of k)).obj (op A)).hom (Category.comp_id _)

theorem toBase_naturality {A A' : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ A') :
    (algSpec (CommRingCat.of k)).map f.op ≫ toBase A = toBase A' := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  exact Over.w ((algSpec (CommRingCat.of k)).map f.op)

/-- The constant family of model points of a rational point. -/
def constantFamily (g₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (A : CommAlgCat.{u} (CommRingCat.of k)) : (AffineCoordinates.functor G).obj A :=
  modelPoint G A (toBase A ≫ g₀)

theorem constantFamily_naturality (g₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    {A A' : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ A') :
    (AffineCoordinates.functor G).map f (constantFamily G g₀ A) = constantFamily G g₀ A' := by
  rw [constantFamily, ← modelPoint_naturality, ← Category.assoc, toBase_naturality,
    constantFamily]

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {I : Type u} [Fintype I] (φ : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)

/-- A rational point commuting with the torus is fixed by the model action of conjugation. -/
theorem constantFamily_fixed (i : S.toGrp ⟶ G) {g₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg₀ : g₀ ∈ (torusCentralizer i).carrier _) {A : CommAlgCat.{u} (CommRingCat.of k)}
    (t : I → Aˣ) :
    (modelAction (AffineCoordinates.corepresentation G) (AffineCoordinates.groupSchemeIso G) φ
        (AutomorphicAction.conjugation i)).act t (constantFamily G g₀ A) = constantFamily G g₀ A := by
  rw [constantFamily, modelAction_act_modelPoint, AutomorphicAction.conjugation_act]
  have hc := hg₀ _ (toBase A) (torusPt I A t ≫ φ.inv.hom.hom)
  rw [hc.symm.eq, mul_inv_cancel_right]

end Fixed

section Cocharacter

variable (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

/-- The model torus action of conjugation through a cocharacter. -/
abbrev cocharModelAction : TorusAction (AffineCoordinates.functor G) PUnit :=
  modelAction (AffineCoordinates.corepresentation G) (AffineCoordinates.groupSchemeIso G)
    (splitTorus.gmIso (Spec (CommRingCat.of k))) (AutomorphicAction.conjugation χ)

/-- The exponent vector of the identity character of `𝔾_m`. -/
abbrev idExponent : PUnit.{u + 1} → ℤ :=
  characterExponents (splitTorus.gmIso (Spec (CommRingCat.of k))) (𝟙 (Gm (Spec (CommRingCat.of k))))

theorem idExponent_ne_zero : idExponent (k := k) ≠ 0 := by
  intro h
  have h1 : (𝟙 (Gm (Spec (CommRingCat.of k))) : characterLattice (Gm (Spec (CommRingCat.of k)))) = 0 :=
    (characterExponents (splitTorus.gmIso (Spec (CommRingCat.of k)))).injective
      (h.trans (map_zero _).symm)
  have h2 := congrArg (gmEndEquiv k) h1
  rw [gmEndEquiv_id, map_zero] at h2
  exact one_ne_zero h2

variable [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- Membership in the cyclic weight filtration of conjugation through `χ`, read in the model. -/
theorem mem_weightFiltration_iff_modelPoint (r : ℕ) {A : CommAlgCat.{u} (CommRingCat.of k)}
    (x : G.affinePoints A) :
    x ∈ (weightFiltration (S := Gm (Spec (CommRingCat.of k))) (AutomorphicAction.conjugation χ)
        (𝟙 _) r).carrier ((algSpec (CommRingCat.of k)).obj (op A)) ↔
      modelPoint G A x ∈ weightSubgroup (AffineCoordinates.corepresentation G)
        (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) r) A := by
  have := isAffineHom_affineCoordinates G
  have := AffineCoordinates.formallySmooth_algebra G inferInstance
  have := AffineCoordinates.finiteType_algebra G inferInstance
  have hne : (𝟙 (Gm (Spec (CommRingCat.of k))) : characterLattice (Gm (Spec (CommRingCat.of k)))) ≠
      0 := fun h => idExponent_ne_zero (k := k) (by rw [idExponent, h, map_zero])
  rw [weightFiltration_eq_weightSubgroupFunctor_cyclicTail (AffineCoordinates.corepresentation G)
    (AffineCoordinates.groupSchemeIso G) (splitTorus.gmIso _) _ _ hne r]
  exact mem_weightSubgroupFunctor_iff G (splitTorus.gmIso _) _ _ x

/-- Membership in the dynamic unipotent subgroup, read in the model. -/
theorem mem_unipotent_iff_modelPoint {A : CommAlgCat.{u} (CommRingCat.of k)}
    (x : G.affinePoints A) :
    x ∈ (Dynamic.unipotent χ).carrier ((algSpec (CommRingCat.of k)).obj (op A)) ↔
      modelPoint G A x ∈ weightSubgroup (AffineCoordinates.corepresentation G)
        (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) 1) A := by
  rw [dynamicUnipotent_eq_weightFiltration G χ]
  exact mem_weightFiltration_iff_modelPoint G χ 1 x

end Cocharacter

end Langlands.GroupScheme.Dynamic.GradedCoordinates
