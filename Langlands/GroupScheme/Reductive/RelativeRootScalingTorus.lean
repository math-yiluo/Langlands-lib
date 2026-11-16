import Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat
import Langlands.GroupScheme.Rational.CharacterFpqcProof
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.FinitePresentation

/-! # Exponent projections of split tori over arbitrary rings -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme

namespace Diagonalizable

variable (R : CommRingCat.{u}) {I J : Type u} [Fintype I] [Fintype J]

/-- The group algebra of a finite free lattice is finitely presented over the base ring. -/
theorem finitePresentation_groupAlgebra :
    (algebraMap R (AddMonoidAlgebra R (I → ℤ))).FinitePresentation := by
  classical
  have := (isSplitTorus R (AddEquiv.refl (I → ℤ))).smooth
  have h : LocallyOfFinitePresentation (groupScheme R (I → ℤ)).X.hom := inferInstance
  exact (LocallyOfFinitePresentation.SpecMap_iff _).1 h

/-- Every restriction map between finite-rank diagonalizable split tori is locally of
finite presentation, without any noetherian hypothesis on the base. -/
theorem locallyOfFinitePresentation_restrictMap (g : (J → ℤ) →+ (I → ℤ)) :
    LocallyOfFinitePresentation (restrictMap R g).hom.hom.left := by
  rw [restrictMap_left, LocallyOfFinitePresentation.SpecMap_iff]
  apply RingHom.FinitePresentation.of_comp_finiteType
    (algebraMap R (AddMonoidAlgebra R (J → ℤ)))
  · change ((AddMonoidAlgebra.mapDomainRingHom R g).comp
      (algebraMap R (AddMonoidAlgebra R (J → ℤ)))).FinitePresentation
    have heq : (AddMonoidAlgebra.mapDomainRingHom R g).comp
        (algebraMap R (AddMonoidAlgebra R (J → ℤ))) =
        algebraMap R (AddMonoidAlgebra R (I → ℤ)) := by
      apply RingHom.ext
      intro r
      change AddMonoidAlgebra.mapDomain g (AddMonoidAlgebra.single 0 r) =
        AddMonoidAlgebra.single 0 r
      simp [AddMonoidAlgebra.mapDomain_single]
    rw [heq]
    exact finitePresentation_groupAlgebra R
  · exact RingHom.FiniteType.of_finitePresentation (finitePresentation_groupAlgebra R)

omit [Fintype I] [Fintype J] in
/-- The faithful flatness assertion also holds for the zero ring, whose spectrum is empty. -/
theorem flat_and_surjective_restrictMap_all (g : (J → ℤ) →+ (I → ℤ))
    (hg : Function.Injective g) :
    Flat (restrictMap R g).hom.hom.left ∧ Surjective (restrictMap R g).hom.hom.left := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    let := h
    let : IsEmpty (Spec R) := inferInstanceAs (IsEmpty (PrimeSpectrum R))
    let : IsEmpty (groupScheme R (J → ℤ)).X.left :=
      Function.isEmpty (groupScheme R (J → ℤ)).X.hom
    exact ⟨inferInstance, inferInstance⟩
  | inr h =>
    let := h
    exact flat_and_surjective_restrictMap R g hg

/-- The inverse coordinate isomorphism preserves the specified point models. -/
theorem splitIso_inv_points {K : Type u} [AddCommGroup K] [DecidableEq I]
    (b : K ≃+ (I → ℤ)) (V : Over (Spec R)) (x : V ⟶ (splitTorus (Spec R) I).X) :
    splitPointsEquiv R b V (x ≫ (splitIso R b).inv.hom.hom) =
      splitTorus.pointsEquiv I V x := by
  apply isoOfPointModels_inv
  exact fun a y => splitTorus.pointsEquiv_naturality I a y

end Diagonalizable

namespace splitTorus

variable (R : CommRingCat.{u}) {I J : Type u} [Fintype I] [Fintype J]

/-- The lattice map taking the coordinate indexed by `j` to the integer weight `m j`. -/
def exponentLatticeMap (m : J → I → ℤ) : (J → ℤ) →+ (I → ℤ) :=
  (Fintype.linearCombination ℤ m).toAddMonoidHom

/-- The homomorphism of coordinate tori defined by a finite family of integer weights. -/
def exponentTorusProjection (m : J → I → ℤ) :
    splitTorus (Spec R) I ⟶ splitTorus (Spec R) J := by
  classical
  exact (Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))).inv ≫
    Diagonalizable.restrictMap R (exponentLatticeMap m) ≫
    (Diagonalizable.splitIso R (AddEquiv.refl (J → ℤ))).hom

/-- Each output coordinate is the prescribed integer monomial in the input coordinates. -/
theorem exponentTorusProjection_points (m : J → I → ℤ) (V : Over (Spec R))
    (x : V ⟶ (splitTorus (Spec R) I).X) (j : J) :
    pointsEquiv J V (x ≫ (exponentTorusProjection R m).hom.hom) j =
      ∏ i, pointsEquiv I V x i ^ m j i := by
  classical
  change pointsEquiv J V
    ((x ≫ (Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))).inv.hom.hom ≫
      (Diagonalizable.restrictMap R (exponentLatticeMap m)).hom.hom) ≫
      (Diagonalizable.splitIso R (AddEquiv.refl (J → ℤ))).hom.hom.hom) j = _
  rw [RelativeRoot.CharacterFpqc.splitIso_hom_points]
  change DFunLike.coe (F := Multiplicative (J → ℤ) →* ((algΓ R).obj V).unopˣ)
    (Corepresented.pointsEquiv (Diagonalizable.functor R (J → ℤ))
    (Diagonalizable.grpCorepresentation R (J → ℤ)) V
    ((x ≫ (Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))).inv.hom.hom) ≫
      (Diagonalizable.restrictMap R (exponentLatticeMap m)).hom.hom))
    (.ofAdd (Pi.single j 1)) = _
  rw [Diagonalizable.pointsEquiv_restrictMap]
  rw [show exponentLatticeMap m (Pi.single j 1) = m j by
    simp [exponentLatticeMap, Fintype.linearCombination_apply_single]]
  let χ : Multiplicative (I → ℤ) →* ((algΓ R).obj V).unopˣ :=
    Corepresented.pointsEquiv (Diagonalizable.functor R (I → ℤ))
    (Diagonalizable.grpCorepresentation R (I → ℤ)) V
    (x ≫ (Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))).inv.hom.hom)
  have h := Diagonalizable.splitIso_inv_points R (AddEquiv.refl (I → ℤ)) V x
  change Diagonalizable.charEquiv (AddEquiv.refl (I → ℤ)) _ χ = _ at h
  change χ (.ofAdd (m j)) = _
  calc
    χ (.ofAdd (m j)) = ∏ i,
        Diagonalizable.charEquiv (AddEquiv.refl (I → ℤ)) _ χ i ^ m j i :=
      (congrArg (fun f : Multiplicative (I → ℤ) →* (Γ(V.left, ⊤))ˣ => f (.ofAdd (m j)))
        ((Diagonalizable.charEquiv (AddEquiv.refl (I → ℤ)) _).symm_apply_apply χ)).symm
    _ = _ := by rw [h]

/-- Independent integer weights define an fppf projection of split tori over every ring. -/
theorem exponentTorusProjection_fppf (m : J → I → ℤ) (hm : LinearIndependent ℤ m) :
    Flat (exponentTorusProjection R m).hom.hom.left ∧
    Surjective (exponentTorusProjection R m).hom.hom.left ∧
    LocallyOfFinitePresentation (exponentTorusProjection R m).hom.hom.left := by
  classical
  let eI := Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))
  let eJ := Diagonalizable.splitIso R (AddEquiv.refl (J → ℤ))
  let f := Diagonalizable.restrictMap R (exponentLatticeMap m)
  have hf := Diagonalizable.flat_and_surjective_restrictMap_all R (exponentLatticeMap m)
    hm.fintypeLinearCombination_injective
  have : Flat f.hom.hom.left := hf.1
  have : Surjective f.hom.hom.left := hf.2
  have : LocallyOfFinitePresentation f.hom.hom.left :=
    Diagonalizable.locallyOfFinitePresentation_restrictMap R (exponentLatticeMap m)
  have : IsIso eI.inv.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eI)).inv)
  have : IsIso eJ.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eJ)).hom)
  change Flat (eI.inv.hom.hom.left ≫ f.hom.hom.left ≫ eJ.hom.hom.hom.left) ∧
    Surjective (eI.inv.hom.hom.left ≫ f.hom.hom.left ≫ eJ.hom.hom.hom.left) ∧
    LocallyOfFinitePresentation
      (eI.inv.hom.hom.left ≫ f.hom.hom.left ≫ eJ.hom.hom.hom.left)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end splitTorus

end Langlands.GroupScheme
