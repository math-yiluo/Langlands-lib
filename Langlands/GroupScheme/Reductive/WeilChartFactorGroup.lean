import Langlands.GroupScheme.Reductive.WeilChartFactorDescent
import Langlands.GroupScheme.AffinePointComparison
import Langlands.GroupScheme.EndomorphismFixedSubgroup

/-! # The descended factor group `G'` over the descended coefficient algebra -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option maxRecDepth 4000

namespace Langlands.GroupScheme.WeilChart

variable {A A' C B : Type u} [CommRing A] [CommRing A'] [CommRing C] [CommRing B]
  [Algebra A A'] [Algebra A' C] [Algebra A B]

section BAlg

variable (A) in
/-- A `B`-algebra, regarded as an `A`-algebra. -/
abbrev resB (X : CommAlgCat.{u} (CommRingCat.of B)) : CommAlgCat.{u} (CommRingCat.of A) :=
  letI : Algebra A X := Algebra.compHom X (algebraMap A B)
  CommAlgCat.of (CommRingCat.of A) X

/-- The structure map `B → X` of a `B`-algebra, as a map of `A`-algebras. -/
def structB (X : CommAlgCat.{u} (CommRingCat.of B)) : B →ₐ[A] resB A X :=
  letI : Algebra A X := Algebra.compHom X (algebraMap A B)
  { algebraMap B X with commutes' := fun _ => rfl }

/-- A map of `B`-algebras, as a map of `A`-algebras. -/
def resBHom {X Y : CommAlgCat.{u} (CommRingCat.of B)} (χ : X ⟶ Y) : resB A X ⟶ resB A Y :=
  letI : Algebra A X := Algebra.compHom X (algebraMap A B)
  letI : Algebra A Y := Algebra.compHom Y (algebraMap A B)
  CommAlgCat.ofHom (X := X) (Y := Y)
    { χ.hom.toRingHom with commutes' := fun a => χ.hom.commutes (algebraMap A B a) }

theorem resBHom_comp_structB {X Y : CommAlgCat.{u} (CommRingCat.of B)} (χ : X ⟶ Y) :
    (resBHom (A := A) χ).hom.comp (structB X) = structB Y := by
  apply AlgHom.ext
  intro b
  exact χ.hom.commutes b

variable (G : GroupScheme (Spec (CommRingCat.of A)))

/-- Points of `G_B` over a `B`-algebra are points of `G` over the underlying `A`-algebra. -/
def bPointsEquiv (X : CommAlgCat.{u} (CommRingCat.of B)) :
    ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePoints X ≃*
      G.affinePoints (resB A X) :=
  letI : Algebra A X := Algebra.compHom X (algebraMap A B)
  haveI : IsScalarTower A B X := IsScalarTower.of_algebraMap_eq' rfl
  (affinePointsBaseChangeMulEquiv A B X G).symm

theorem bPointsEquiv_symm_naturality {X Y : CommAlgCat.{u} (CommRingCat.of B)} (χ : X ⟶ Y)
    (p : G.affinePoints (resB A X)) :
    ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePointMap χ
        ((bPointsEquiv G X).symm p) =
      (bPointsEquiv G Y).symm (G.affinePointMap (resBHom χ) p) := by
  letI : Algebra A X := Algebra.compHom X (algebraMap A B)
  haveI : IsScalarTower A B X := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra A Y := Algebra.compHom Y (algebraMap A B)
  haveI : IsScalarTower A B Y := IsScalarTower.of_algebraMap_eq' rfl
  exact affinePointsBaseChangeMulEquiv_naturality (R := A) (S := B) (A := X) (A' := Y) G χ.hom p

end BAlg

section Factor

variable (e : A' ⊗[A] B ≃ₐ[A'] C)
  [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C]
  {G : GroupScheme (Spec (CommRingCat.of A))}
  {H : GroupScheme (Spec (CommRingCat.of C))} [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (P : (GroupScheme.baseChange (Spec.algebraMap A A')).obj G ≅ AffineWeil.groupScheme A' C H)
  (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred : IsReductive H) (hsimple : ∀ s, IsAlmostSimple (geometricFiber H s))
  [Module.FaithfullyFlat A A']
  (hinv : ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : A' →ₐ[A] T) (b : B),
    chartAlgEquiv P hR hred hsimple f₁ f₂ (coeffTmul f₂ 1 (e (1 ⊗ₜ[A] b))) =
      coeffTmul f₁ 1 (e (1 ⊗ₜ[A] b)))

/-- The diagonal factor projection on the points of `G_B` over a `B`-algebra. -/
def factorEndApp (X : CommAlgCat.{u} (CommRingCat.of B)) :
    ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePoints X →*
      ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePoints X :=
  (bPointsEquiv G X).symm.toMonoidHom.comp
    ((descProj e P hR hred hsimple hinv (structB X)).comp (bPointsEquiv G X).toMonoidHom)

theorem factorEndApp_apply (X : CommAlgCat.{u} (CommRingCat.of B))
    (p : ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePoints X) :
    factorEndApp e P hR hred hsimple hinv X p =
      (bPointsEquiv G X).symm (descProj e P hR hred hsimple hinv (structB X) (bPointsEquiv G X p)) :=
  rfl

/-- The diagonal factor projection, as an endomorphism of the point functor of `G_B`. -/
def factorEndNat : ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePointFunctor ⟶
    ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePointFunctor where
  app X := GrpCat.ofHom (factorEndApp e P hR hred hsimple hinv X)
  naturality X Y χ := by
    refine GrpCat.ext fun p => ?_
    change factorEndApp e P hR hred hsimple hinv Y
        (((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePointMap χ p) =
      ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePointMap χ
        (factorEndApp e P hR hred hsimple hinv X p)
    obtain ⟨q, rfl⟩ := (bPointsEquiv G X).symm.surjective p
    rw [factorEndApp_apply, factorEndApp_apply, MulEquiv.apply_symm_apply,
      bPointsEquiv_symm_naturality, MulEquiv.apply_symm_apply, bPointsEquiv_symm_naturality,
      descProj_map, resBHom_comp_structB]

variable [IsAffine G.X.left]

theorem isAffine_baseChange_left :
    IsAffine ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).X.left := by
  change IsAffine (pullback G.X.hom (Spec.algebraMap A B))
  infer_instance

/-- The diagonal factor projection, as an endomorphism of the group scheme `G_B`. -/
def factorEnd : (GroupScheme.baseChange (Spec.algebraMap A B)).obj G ⟶
    (GroupScheme.baseChange (Spec.algebraMap A B)).obj G :=
  haveI := isAffine_baseChange_left (B := B) (G := G)
  AffinePointComparison.map (factorEndNat e P hR hred hsimple hinv)

theorem factorEnd_points (X : CommAlgCat.{u} (CommRingCat.of B))
    (p : ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePoints X) :
    p ≫ (factorEnd e P hR hred hsimple hinv).hom.hom = factorEndApp e P hR hred hsimple hinv X p :=
  haveI := isAffine_baseChange_left (B := B) (G := G)
  AffinePointComparison.map_points (factorEndNat e P hR hred hsimple hinv) X p

theorem exists_factorGroup :
    ∃ (G' : GroupScheme (Spec (CommRingCat.of B)))
      (i : G' ⟶ (GroupScheme.baseChange (Spec.algebraMap A B)).obj G),
      (endomorphismFixedSubgroup (factorEnd e P hR hred hsimple hinv)).IsRepresentedBy i ∧
        IsClosedSubgroup i := by
  haveI := isAffine_baseChange_left (B := B) (G := G)
  exact endomorphismFixedSubgroup_isClosedRepresentable _

/-- **The descended factor group** `G'` over `Spec B`: the closed subgroup of `G_B` fixed by the
diagonal factor projection. -/
def factorGroup : GroupScheme (Spec (CommRingCat.of B)) :=
  Classical.choose (exists_factorGroup e P hR hred hsimple hinv)

/-- The inclusion of the descended factor group into `G_B`. -/
def factorIncl : factorGroup e P hR hred hsimple hinv ⟶
    (GroupScheme.baseChange (Spec.algebraMap A B)).obj G :=
  Classical.choose (Classical.choose_spec (exists_factorGroup e P hR hred hsimple hinv))

theorem factorIncl_spec :
    (endomorphismFixedSubgroup (factorEnd e P hR hred hsimple hinv)).IsRepresentedBy
        (factorIncl e P hR hred hsimple hinv) ∧
      IsClosedSubgroup (factorIncl e P hR hred hsimple hinv) :=
  Classical.choose_spec (Classical.choose_spec (exists_factorGroup e P hR hred hsimple hinv))

theorem factorGroup_isAffine : IsAffine (factorGroup e P hR hred hsimple hinv).X.left := by
  haveI := isAffine_baseChange_left (B := B) (G := G)
  haveI : IsClosedImmersion (factorIncl e P hR hred hsimple hinv).hom.hom.left :=
    (factorIncl_spec e P hR hred hsimple hinv).2
  exact isAffine_of_isAffineHom (factorIncl e P hR hred hsimple hinv).hom.hom.left

theorem factorGroup_locallyOfFiniteType [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (factorGroup e P hR hred hsimple hinv).X.hom := by
  haveI : IsClosedImmersion (factorIncl e P hR hred hsimple hinv).hom.hom.left :=
    (factorIncl_spec e P hR hred hsimple hinv).2
  haveI : LocallyOfFiniteType ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom (Spec.algebraMap A B))
    infer_instance
  rw [← Over.w (factorIncl e P hR hred hsimple hinv).hom.hom]
  infer_instance

theorem factorIncl_injective (X : CommAlgCat.{u} (CommRingCat.of B)) :
    Function.Injective fun y : (factorGroup e P hR hred hsimple hinv).affinePoints X =>
      y ≫ (factorIncl e P hR hred hsimple hinv).hom.hom := by
  haveI := (factorIncl_spec e P hR hred hsimple hinv).1.1
  intro y y' h
  exact (cancel_mono _).1 h

theorem mem_range_factorIncl_iff (X : CommAlgCat.{u} (CommRingCat.of B))
    (g : ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePoints X) :
    (∃ y : (factorGroup e P hR hred hsimple hinv).affinePoints X,
      y ≫ (factorIncl e P hR hred hsimple hinv).hom.hom = g) ↔
        factorEndApp e P hR hred hsimple hinv X g = g := by
  have h := congrArg (fun F : SubgroupFunctor _ => g ∈ F.carrier ((algSpec _).obj (Opposite.op X)))
    (factorIncl_spec e P hR hred hsimple hinv).1.2
  simp only [SubgroupFunctor.mem_range, mem_endomorphismFixedSubgroup] at h
  rw [h, factorEnd_points]

/-- The points of `G_B` fixed by the diagonal factor projection. -/
abbrev fixedPoints (X : CommAlgCat.{u} (CommRingCat.of B)) :
    Subgroup (((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePoints X) :=
  MonoidHom.eqLocus (factorEndApp e P hR hred hsimple hinv X) (MonoidHom.id _)

/-- The points of the descended factor group are the fixed points of the diagonal factor
projection. -/
def factorPointsEquiv (X : CommAlgCat.{u} (CommRingCat.of B)) :
    (factorGroup e P hR hred hsimple hinv).affinePoints X ≃*
      fixedPoints e P hR hred hsimple hinv X :=
  MulEquiv.ofBijective
    (((factorGroup e P hR hred hsimple hinv).affinePointsTarget
        (factorIncl e P hR hred hsimple hinv) X).codRestrict
      (fixedPoints e P hR hred hsimple hinv X)
      fun y => (mem_range_factorIncl_iff e P hR hred hsimple hinv X _).1 ⟨y, rfl⟩)
    ⟨fun y y' h => factorIncl_injective e P hR hred hsimple hinv X (congrArg Subtype.val h),
      fun g => by
        obtain ⟨y, hy⟩ := (mem_range_factorIncl_iff e P hR hred hsimple hinv X g.1).2 g.2
        exact ⟨y, Subtype.ext hy⟩⟩

theorem factorPointsEquiv_apply (X : CommAlgCat.{u} (CommRingCat.of B))
    (y : (factorGroup e P hR hred hsimple hinv).affinePoints X) :
    (factorPointsEquiv e P hR hred hsimple hinv X y : _) =
      y ≫ (factorIncl e P hR hred hsimple hinv).hom.hom :=
  rfl

theorem factorPointsEquiv_naturality {X Y : CommAlgCat.{u} (CommRingCat.of B)} (χ : X ⟶ Y)
    (y : (factorGroup e P hR hred hsimple hinv).affinePoints X) :
    (factorPointsEquiv e P hR hred hsimple hinv Y
        ((factorGroup e P hR hred hsimple hinv).affinePointMap χ y) : _) =
      ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePointMap χ
        (factorPointsEquiv e P hR hred hsimple hinv X y) := by
  rw [factorPointsEquiv_apply, factorPointsEquiv_apply, affinePointMap_apply,
    affinePointMap_apply, Category.assoc]

end Factor

end Langlands.GroupScheme.WeilChart
