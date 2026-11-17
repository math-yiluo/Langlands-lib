import Langlands.GroupScheme.Torus.ExponentHomomorphisms
import Langlands.GroupScheme.Rational.SplitTorusIsogenyOfLatticeMapsProof

/-! # Integral-coordinate isogenies over arbitrary affine bases -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace Diagonalizable

/-- Injective lattice maps give faithfully flat group-algebra maps over
every commutative coefficient ring, including the zero ring. -/
theorem faithfullyFlat_mapDomainRingHom_of_injective
    {Λ' Λ : Type*} [AddCommGroup Λ'] [AddCommGroup Λ]
    {g : Λ' →+ Λ} (hg : Function.Injective g)
    (R : Type*) [CommRing R] :
    (AddMonoidAlgebra.mapDomainRingHom R g).FaithfullyFlat := by
  let := mapDomainAlgebra (g := g) R
  have hff : Module.FaithfullyFlat (AddMonoidAlgebra R Λ') (AddMonoidAlgebra R Λ) :=
    Module.FaithfullyFlat.of_linearEquiv _ _
      (LinearEquiv.ofBijective _ (cosetLinearMap_bijective hg R)).symm
  exact (RingHom.faithfullyFlat_algebraMap_iff).2 hff

/-- An injective character-group map with finite cokernel induces an
isogeny of the actual diagonalizable groups over every affine base. -/
theorem isIsogeny_restrictMap
    (R : CommRingCat.{u}) {Λ' Λ : Type u}
    [AddCommGroup Λ'] [AddCommGroup Λ]
    (g : Λ' →+ Λ) (hg : Function.Injective g) [Finite (Λ ⧸ g.range)] :
    IsIsogeny (restrictMap R g) := by
  change isogenyProperty (restrictMap R g).hom.hom.left
  rw [restrictMap_left]
  obtain ⟨hf, hs⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R g))).2
    (faithfullyFlat_mapDomainRingHom_of_injective hg R)
  exact ⟨(IsFinite.SpecMap_iff _).2 (finite_mapDomainRingHom hg), hf, hs⟩

end Diagonalizable

namespace splitTorus

variable (S : Scheme.{u}) (I J : Type u)
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] in
/-- Integral pullback on characters is the prescribed identity on every
test scheme, over an arbitrary base. -/
theorem pointsEquiv_exponentHom
    (f : (J → ℤ) →ₗ[ℤ] (I → ℤ))
    {U : Over S} (x : U ⟶ (splitTorus S I).X) (m : J → ℤ) :
    ∏ j, pointsEquiv J U
        (x ≫ (CommGroupScheme.groupHom (exponentHom S I J f)).hom.hom) j ^ m j =
      ∏ i, pointsEquiv I U x i ^ f m i := by
  rw [← pointsEquiv_exponentCharacter S J m,
    Category.assoc, ← Grp.comp_hom_hom]
  change Gm.pointsEquiv S U
    (x ≫ (CommGroupScheme.groupHom
      (exponentHom S I J f ≫ exponentCharacter S J m)).hom.hom) = _
  rw [exponentHom_comp_exponentCharacter, pointsEquiv_exponentCharacter]

variable (R : CommRingCat.{u})

/-- The fixed integral-coordinate map agrees, over any ring, with
restriction of diagonalizable characters. -/
theorem restrictMap_comp_splitIso
    (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) :
    Diagonalizable.restrictMap R f.toAddMonoidHom ≫
        (Diagonalizable.splitIso R (AddEquiv.refl (J → ℤ))).hom =
      (Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))).hom ≫
        CommGroupScheme.groupHom (exponentHom (Spec R) I J f) := by
  apply hom_ext_points
  intro U x
  apply (pointsEquiv J U).injective
  let eI := Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))
  let eJ := Diagonalizable.splitIso R (AddEquiv.refl (J → ℤ))
  have hI (y : U ⟶ (Diagonalizable.groupScheme R (I → ℤ)).X) :
      pointsEquiv I U (y ≫ eI.hom.hom.hom) =
        Diagonalizable.splitPointsEquiv R (AddEquiv.refl (I → ℤ)) U y :=
    isoOfPointModels_hom _ _ _ _
      (Diagonalizable.splitPointsEquiv_naturality R (AddEquiv.refl (I → ℤ)))
      (fun a z => pointsEquiv_naturality I a z) U y
  have hJ (y : U ⟶ (Diagonalizable.groupScheme R (J → ℤ)).X) :
      pointsEquiv J U (y ≫ eJ.hom.hom.hom) =
        Diagonalizable.splitPointsEquiv R (AddEquiv.refl (J → ℤ)) U y :=
    isoOfPointModels_hom _ _ _ _
      (Diagonalizable.splitPointsEquiv_naturality R (AddEquiv.refl (J → ℤ)))
      (fun a z => pointsEquiv_naturality J a z) U y
  change pointsEquiv J U
    ((x ≫ (Diagonalizable.restrictMap R f.toAddMonoidHom).hom.hom) ≫
      eJ.hom.hom.hom) =
    pointsEquiv J U
      ((x ≫ eI.hom.hom.hom) ≫
        (CommGroupScheme.groupHom (exponentHom (Spec R) I J f)).hom.hom)
  rw [hJ]
  funext j
  let χ : Multiplicative (I → ℤ) →* (Γ(U.left, ⊤))ˣ :=
    Corepresented.pointsEquiv (Diagonalizable.functor R (I → ℤ))
      (Diagonalizable.grpCorepresentation R (I → ℤ)) U x
  change DFunLike.coe (F := Multiplicative (J → ℤ) →* (Γ(U.left, ⊤))ˣ)
    (Corepresented.pointsEquiv (Diagonalizable.functor R (J → ℤ))
      (Diagonalizable.grpCorepresentation R (J → ℤ)) U
      (x ≫ (Diagonalizable.restrictMap R f.toAddMonoidHom).hom.hom))
      (Multiplicative.ofAdd (Pi.single j 1)) = _
  erw [Diagonalizable.pointsEquiv_restrictMap]
  change χ (Multiplicative.ofAdd (f (Pi.single j 1))) = _
  change _ = Gm.pointsEquiv (Spec R) U
    ((x ≫ eI.hom.hom.hom) ≫
      (CommGroupScheme.groupHom
        (exponentHom (Spec R) I J f ≫ proj (Spec R) J j)).hom.hom)
  rw [exponentHom_comp_proj, pointsEquiv_exponentCharacter, hI]
  exact congrArg
    (fun ψ : Multiplicative (I → ℤ) →* (Γ(U.left, ⊤))ˣ =>
      ψ (Multiplicative.ofAdd (f (Pi.single j 1))))
    ((Diagonalizable.charEquiv (AddEquiv.refl (I → ℤ)) _).symm_apply_apply χ).symm

/-- An injective integral-coordinate character map with finite cokernel
gives a finite flat surjective torus map over any commutative ring. -/
theorem isIsogeny_exponentHom
    (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (hf : Function.Injective f)
    [Finite ((I → ℤ) ⧸ LinearMap.range f)] :
    IsIsogeny (CommGroupScheme.groupHom (exponentHom (Spec R) I J f)) := by
  let eI := Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))
  let eJ := Diagonalizable.splitIso R (AddEquiv.refl (J → ℤ))
  have hmap :
      CommGroupScheme.groupHom (exponentHom (Spec R) I J f) =
        eI.inv ≫ Diagonalizable.restrictMap R f.toAddMonoidHom ≫ eJ.hom := by
    rw [restrictMap_comp_splitIso, Iso.inv_hom_id_assoc]
  rw [hmap]
  have : Finite ((I → ℤ) ⧸ f.toAddMonoidHom.range) :=
    ‹Finite ((I → ℤ) ⧸ LinearMap.range f)›
  exact (isCentralIsogeny_of_isIso eI.inv).isIsogeny.comp
    ((Diagonalizable.isIsogeny_restrictMap R f.toAddMonoidHom hf).comp
      (isCentralIsogeny_of_isIso eJ.hom).isIsogeny)

end splitTorus

end Langlands.GroupScheme
