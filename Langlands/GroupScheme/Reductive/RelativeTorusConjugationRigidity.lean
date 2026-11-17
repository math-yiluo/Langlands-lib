import Langlands.GroupScheme.Reductive.IsogenyAdjointTorusDescent
import Langlands.GroupScheme.Reductive.SplitHomomorphismRigidity
import Langlands.GroupScheme.Reductive.LocalSplitRootBaseChange
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Reductive.LocalSplitLocalAlgebraCellIsomorphism

/-! # Torus conjugation from local algebra generator comparisons -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

open LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R]
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  {T : CommGroupScheme (Spec (CommRingCat.of R))}
  {V : Over (Spec (CommRingCat.of R))}

/-- Pull back an ambient homomorphism to an algebra and conjugate it by the
given torus point evaluated at an algebra point of the parameter scheme. -/
def torusConjugateAlgebraHom (A : Type u) [CommRing A] [Algebra R A]
    (j : T.toGrp ⟶ H) (F : G ⟶ H) (t : V ⟶ T.X) (a : fieldPoint R A ⟶ V) :
    (baseChange (algebraBaseMap R A)).obj G ⟶
      (baseChange (algebraBaseMap R A)).obj H :=
  (baseChange (algebraBaseMap R A)).map F ≫
    (((baseChange (algebraBaseMap R A)).obj H).innerIso
      ((baseChangePointsEquiv (algebraBaseMap R A) H (𝟙_ _)).symm
        (a ≫ t ≫ j.hom.hom))).hom

/-- Evaluation of the conjugated algebra homomorphism on every relative test. -/
theorem torusConjugateAlgebraHom_apply (A : Type u) [CommRing A] [Algebra R A]
    (j : T.toGrp ⟶ H) (F : G ⟶ H) (t : V ⟶ T.X) (a : fieldPoint R A ⟶ V)
    (Z : Over (Spec (CommRingCat.of A)))
    (x : Z ⟶ ((baseChange (algebraBaseMap R A)).obj G).X) :
    baseChangePointsEquiv (algebraBaseMap R A) H Z
        (x ≫ (torusConjugateAlgebraHom A j F t a).hom.hom) =
      ((Over.map (algebraBaseMap R A)).map (toUnit Z) ≫ a ≫ t ≫ j.hom.hom) *
        (baseChangePointsEquiv (algebraBaseMap R A) G Z x ≫ F.hom.hom) *
      ((Over.map (algebraBaseMap R A)).map (toUnit Z) ≫ a ≫ t ≫ j.hom.hom)⁻¹ := by
  unfold torusConjugateAlgebraHom
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom,
    map_mul, map_mul, map_inv, baseChangePointsEquiv_comp]
  rw [← toUnit_comp_eq_constantPoint, baseChangePointsEquiv_naturality,
    MulEquiv.apply_symm_apply]

/-- Equality with the conjugated homomorphism over every local algebra gives
conjugation on every scheme test, including nonreduced tests. -/
theorem TorusConjugates.of_localAlgebraHom [IsAffine H.X.left]
    (j : T.toGrp ⟶ H) (f F : G ⟶ H) (t : V ⟶ T.X)
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A]
      (a : fieldPoint R A ⟶ V),
      (baseChange (algebraBaseMap R A)).map f =
        torusConjugateAlgebraHom A j F t a) :
    TorusConjugates j f F t := by
  intro Z d g
  apply Over.OverMorphism.ext
  apply CellGluing.hom_ext_of_localRingPoints
  intro A _ _ q
  let s := q ≫ Z.hom
  let φ := Spec.preimage s
  let : Algebra R A := φ.hom.toAlgebra
  have hs : algebraBaseMap R A = s := by
    change Spec.map (CommRingCat.ofHom φ.hom) = s
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let e : Over.mk s ≅ fieldPoint R A := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ 𝟙 _ ≫ algebraBaseMap R A = s
    rw [Category.id_comp, Category.id_comp, hs])
  let z : fieldPoint R A ⟶ Z := e.inv ≫ Over.homMk q rfl
  let x := (baseChangePointsEquiv (algebraBaseMap R A) G (𝟙_ _)).symm (z ≫ g)
  have hx := torusConjugateAlgebraHom_apply A j F t (z ≫ d) (𝟙_ _) x
  rw [← h A (z ≫ d), baseChangePointsEquiv_comp,
    MulEquiv.apply_symm_apply] at hx
  rw [toUnit_unique (toUnit (𝟙_ _)) (𝟙 _), (Over.map (algebraBaseMap R A)).map_id, Category.id_comp] at hx
  have he : z ≫ (g ≫ f.hom.hom) =
      z ≫ ((d ≫ t ≫ j.hom.hom) * (g ≫ F.hom.hom) * (d ≫ t ≫ j.hom.hom)⁻¹) := by
    simpa only [MulEquiv.apply_symm_apply,
      Category.assoc, MonObj.comp_mul, GrpObj.comp_inv] using hx
  exact congrArg CommaMorphism.left (congrArg (e.hom ≫ ·) he)

section WeylGenerators

variable {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  [IsAffineHom G.X.hom] [IsAffine H.X.left]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {b : P.Base} {roots : J → (Ga R ⟶ G)}

/-- Source Weyl-generator comparisons over every local algebra imply
conjugation of the entire source group on every scheme test. -/
theorem TorusConjugates.of_localWeylGenerators
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (roots a))
    (hw : ∀ a ∈ b.support,
      IsWeylPoint i (rootWeylPoint P roots a) (P.reflection a))
    (j : T.toGrp ⟶ H) (f F : G ⟶ H) (t : V ⟶ T.X)
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A]
      (a : fieldPoint R A ⟶ V),
      AgreeOnWeylGenerators (splitTorus.baseChangeHom (K := A) G I i) P b
        (fun α => baseChangeRoot A (roots α))
        ((baseChange (algebraBaseMap R A)).map f)
        (torusConjugateAlgebraHom A j F t a)) :
    TorusConjugates j f F t := by
  classical
  have : Finite J := hP.finite
  have : P.IsReduced := hP.isReduced
  let W : ∀ α, SimpleWord P b α := fun α => (nonempty_simpleWord P b α).some
  apply TorusConjugates.of_localAlgebraHom j f F t
  intro A _ _ _ a
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom ((baseChange (algebraBaseMap R A)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))
  exact hom_ext_of_weylGenerators (hG.baseChange (algebraBaseMap R A))
    (splitTorus.isFibrewiseMaximalTorus_baseChangeHom I G i hmax)
    (hP.baseChange_implicit (A := A)) W
    (fun α hα => isRootParametrization_baseChangeRoot A i (P.root α) (roots α) (hu α hα))
    (fun α hα => isWeylPoint_baseChange A (hw α hα)) (h A a)

end WeylGenerators

end Langlands.GroupScheme
