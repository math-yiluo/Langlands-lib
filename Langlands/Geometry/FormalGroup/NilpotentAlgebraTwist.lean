import Langlands.Geometry.FormalGroup.ModuleReduction

/-! # Twisting affine Nilp tests by coefficient automorphisms -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.Nilp

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R] {π : R}
variable (σ : R ≃ₐ[O] R) (hπ : σ π = π)
variable {A B : Nilp.{v, w} R π}

/-- Precompose the structural map of a Nilp algebra with the given coefficient automorphism. -/
def twistObj (A : Nilp.{v, w} R π) : Nilp.{v, w} R π := by
  let j := (algebraMap R A.obj).comp σ.toRingHom
  have h : IsNilpotent (j π) := by
    change IsNilpotent (algebraMap R A.obj (σ π))
    rw [hπ]
    exact A.nilpotent
  letI : Algebra R A.obj := Algebra.compHom A.obj j
  exact Nilp.of R π A.obj h

@[simp]
theorem twistObj_algebraMap (A : Nilp.{v, w} R π) (r : R) :
    algebraMap R (twistObj σ hπ A).obj r = algebraMap R A.obj (σ r) := rfl

/-- The same ring homomorphism is linear for the two twisted structures. -/
def twistHom (f : A ⟶ B) : twistObj σ hπ A ⟶ twistObj σ hπ B :=
  ObjectProperty.homMk (ConcreteCategory.ofHom (C := CommAlgCat R)
    (X := (twistObj σ hπ A).obj) (Y := (twistObj σ hπ B).obj) {
    __ := f.hom.hom.toRingHom
    commutes' r := f.hom.hom.commutes (σ r) })

/-- The actual coefficient twist of the affine Nilp test category. -/
def twistFunctor : Nilp.{v, w} R π ⥤ Nilp.{v, w} R π where
  obj := twistObj σ hπ
  map := twistHom σ hπ
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    ext a
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    ext a
    rfl

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

/-- The identity on test rings is an equivalence over the fixed scalar ring. -/
def twistScalarEquiv (A : Nilp.{v, w} R π) : A.obj ≃ₐ[O] (twistObj σ hπ A).obj where
  __ := RingEquiv.refl A.obj
  commutes' a := by
    change algebraMap R A.obj (algebraMap O R a) =
      algebraMap R A.obj (σ (algebraMap O R a))
    rw [σ.commutes]

theorem twistScalarEquiv_natural (f : A ⟶ B) :
    (scalarMap O (twistHom σ hπ f)).comp (twistScalarEquiv σ hπ A).toAlgHom =
      (twistScalarEquiv σ hπ B).toAlgHom.comp (scalarMap O f) :=
  AlgHom.ext (fun _ => rfl)

/-- The structural twist gives exactly the same ideal in the underlying test ring. -/
theorem twist_reductionIdeal (A : Nilp.{v, w} R π) :
    reductionIdeal π (twistObj σ hπ A).obj = reductionIdeal π A.obj := by
  change Ideal.span {algebraMap R A.obj (σ π)} = Ideal.span {algebraMap R A.obj π}
  rw [hπ]

/-- The identity on representatives compares the two actual quotient rings over the fixed scalars. -/
def twistReducedEquiv (A : Nilp.{v, w} R π) :
    ((reductionFunctor R π).obj A).obj ≃ₐ[O]
      ((reductionFunctor R π).obj (twistObj σ hπ A)).obj := by
  let I : Ideal A.obj := reductionIdeal π A.obj
  let J : Ideal A.obj := reductionIdeal π (twistObj σ hπ A).obj
  have h : I = J := (twist_reductionIdeal σ hπ A).symm
  refine { __ := Ideal.quotEquivOfEq h, commutes' := ?_ }
  intro a
  change Ideal.Quotient.mk J (algebraMap R A.obj (algebraMap O R a)) =
    Ideal.Quotient.mk J (algebraMap R A.obj (σ (algebraMap O R a)))
  rw [σ.commutes]

@[simp]
theorem twistReducedEquiv_quotientO (A : Nilp.{v, w} R π) :
    (twistReducedEquiv σ hπ A).toAlgHom.comp (quotientO O A) =
      (quotientO O (twistObj σ hπ A)).comp (twistScalarEquiv σ hπ A).toAlgHom :=
  AlgHom.ext (fun _ => rfl)

theorem twistReducedEquiv_natural (f : A ⟶ B) :
    (reducedScalarMap O (twistHom σ hπ f)).comp (twistReducedEquiv σ hπ A).toAlgHom =
      (twistReducedEquiv σ hπ B).toAlgHom.comp (reducedScalarMap O f) := by
  apply AlgHom.ext
  intro x
  obtain ⟨x, rfl⟩ := reductionQuotient_surjective π A.obj x
  rfl

/-- The automorphism of the residue coefficient ring induced by the given coefficient twist. -/
def twistResidueEquiv : ResidueRing R π ≃ₐ[O] ResidueRing R π :=
  Ideal.quotientEquivAlg (Ideal.span {π}) (Ideal.span {π}) σ (by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {π} = Ideal.span {σ π}
    rw [hπ])

/-- The residue structural map of a reduced affine test, linear over the fixed scalars. -/
def residueCoefficientMap (A : Nilp.{v, w} R π) :
    ResidueRing R π →ₐ[O] ((reductionFunctor R π).obj A).obj where
  __ := algebraMap (ResidueRing R π) (Reduction π A.obj)
  commutes' _ := rfl

/-- The twisted residue structure is precomposition with the induced residue automorphism,
under the canonical comparison of the two reductions. -/
theorem twistReducedEquiv_residueCoefficientMap (A : Nilp.{v, w} R π) :
    (twistReducedEquiv σ hπ A).toAlgHom.comp
        ((residueCoefficientMap (O := O) A).comp (twistResidueEquiv σ hπ).toAlgHom) =
      residueCoefficientMap (O := O) (twistObj σ hπ A) := by
  apply AlgHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end Langlands.FormalGroup.Nilp
