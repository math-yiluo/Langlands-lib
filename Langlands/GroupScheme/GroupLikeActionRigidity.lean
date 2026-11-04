import Langlands.GroupScheme.GroupLikeActionFamily

/-! # Integral-parameter rigidity for actual actions on Hopf spectra -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AutomorphicAction

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
    {C : CommHopfAlgCat.{u} (CommRingCat.of k)}
    {H : GroupScheme (Spec (CommRingCat.of k))}

attribute [local instance] coefficientAlgebra coefficientTower

/-- The affine parameter point associated to a rational specialization. -/
def specializationSpecMap (ε : R →ₐ[k] k) :
    (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k)) ⟶
      (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k R)) :=
  (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom ε).op

variable (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤)
    (a : AutomorphicAction H ((hopfSpec (CommRingCat.of k)).obj (op C)))
    (s : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k R)) ⟶ H.X)

/-- A coefficient algebra at which the acting point is the identity has identity
convolution action. -/
theorem convolutionFamily_app_eq_self_of_parameter_eq_one
    (A : CommAlgCat.{u} (CommRingCat.of R))
    (hs : parameterSpecMap (k := k) A ≫ s = 1)
    (x : WithConv (R ⊗[k] C →ₐ[R] A)) :
    (convolutionFamily hspan a s).app A x = x := by
  apply (parameterPointsEquiv hspan A).injective
  change parameterPointsEquiv hspan A (convolutionPointAut hspan a s A x) = _
  rw [parameterPointsEquiv_convolutionPointAut, hs, a.act_one_left]

/-- Identity of the specialized acting point gives identity specialization of
the classifying coalgebra map. -/
theorem convolutionFamily_classify_specialize (ε : R →ₐ[k] k)
    (hs : specializationSpecMap ε ≫ s = 1) (c : C) :
    Langlands.GroupLike.specialize ε
      ((convolutionFamily hspan a s).classify (1 ⊗ₜ[k] c)) = c := by
  let e : R →ₐ[k] C := (Algebra.ofId k C).comp ε
  let : Algebra R C := e.toRingHom.toAlgebra
  let : IsScalarTower k R C := IsScalarTower.of_algHom e
  let A : CommAlgCat.{u} (CommRingCat.of R) := CommAlgCat.of R C
  let j : CommAlgCat.of k k ⟶ fieldCoefficients (k := k) A :=
    ConcreteCategory.ofHom (C := CommAlgCat (CommRingCat.of k))
      (@Algebra.ofId k A _ _ (coefficientAlgebra (k := k) A))
  have hp : parameterSpecMap (k := k) A =
      (algSpec (CommRingCat.of k)).map j.op ≫ specializationSpecMap ε := by
    unfold parameterSpecMap specializationSpecMap
    rw [← Functor.map_comp]
    apply congrArg (algSpec (CommRingCat.of k)).map
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    apply DFunLike.ext
    intro r
    change algebraMap k C (ε r) =
      algebraMap k C (ε (algebraMap k R (ε r)))
    simp
  have hp1 : parameterSpecMap (k := k) A ≫ s = 1 := by
    rw [hp, Category.assoc, hs, MonObj.comp_one]
  let ψ : R ⊗[k] C →ₐ[R] C :=
    AlgHom.liftEquiv k R C C (AlgHom.id k C)
  have hψ : ∀ d : R ⊗[k] C, ψ d = Langlands.GroupLike.specialize ε d := by
    intro d
    induction d using TensorProduct.inductionOn with
    | tmul r d =>
      rw [Langlands.GroupLike.specialize_tmul]
      change algebraMap k C (ε r) * d = ε r • d
      exact (Algebra.smul_def (ε r) d).symm
    | add d d' hd hd' => simp only [map_add, hd, hd']
  have hnat := (convolutionFamily hspan a s).app_eq
    (A := A) ψ
  have hfix := convolutionFamily_app_eq_self_of_parameter_eq_one
    hspan a s A hp1 (toConv ψ)
  rw [hfix] at hnat
  have hd := DFunLike.congr_fun hnat (1 ⊗ₜ[k] c)
  change ψ (1 ⊗ₜ[k] c) = ψ ((convolutionFamily hspan a s).classify (1 ⊗ₜ[k] c)) at hd
  rw [← hψ, ← hd]
  change (1 : R) • c = c
  exact one_smul R c

include hspan in
/-- Over integral parameters, one identity specialization forces the actual
action on every coefficient-algebra test to be trivial. -/
theorem act_parameter_eq_self_of_specialization [IsDomain R] (ε : R →ₐ[k] k)
    (hs : specializationSpecMap ε ≫ s = 1)
    (A : CommAlgCat.{u} (CommRingCat.of R))
    (x : (algSpec (CommRingCat.of k)).obj (op (fieldCoefficients (k := k) A)) ⟶
      ((hopfSpec (CommRingCat.of k)).obj (op C)).X) :
    a.act (parameterSpecMap A ≫ s) x = x := by
  let y := (parameterPointsEquiv hspan A).symm x
  have h := (convolutionFamily hspan a s).app_eq_self_of_specialize hspan ε
    (convolutionFamily_classify_specialize hspan a s ε hs) y
  have he := congrArg (parameterPointsEquiv hspan A) h
  change parameterPointsEquiv hspan A (convolutionPointAut hspan a s A y) =
    parameterPointsEquiv hspan A y at he
  rw [parameterPointsEquiv_convolutionPointAut] at he
  simpa only [y, MulEquiv.apply_symm_apply] using he

end Langlands.GroupScheme.AutomorphicAction
