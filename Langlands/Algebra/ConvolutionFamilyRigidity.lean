import Langlands.Algebra.GroupLikeDomainRigidity
import Langlands.TauCeti.Algebra.Coalgebra.Convolution
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Natural convolution endomorphisms and coalgebra rigidity -/

noncomputable section

universe u

open CategoryTheory TensorProduct WithConv
open scoped TensorProduct

namespace Langlands.ConvolutionFamily

variable (R D : Type u) [CommRing R] [CommRing D] [Bialgebra R D]

/-- A natural family of endomorphisms of convolution monoids of algebra points. -/
structure EndFamily where
  app (A : CommAlgCat.{u} (CommRingCat.of R)) :
    WithConv (D →ₐ[R] A) →* WithConv (D →ₐ[R] A)
  naturality {A B : CommAlgCat.{u} (CommRingCat.of R)} (f : A →ₐ[R] B)
    (x : WithConv (D →ₐ[R] A)) :
    (app B (toConv (f.comp x.ofConv))).ofConv = f.comp (app A x).ofConv

variable {R D}

/-- The image of the universal algebra point. -/
def EndFamily.classify (F : EndFamily R D) : D →ₐ[R] D :=
  (F.app (CommAlgCat.of R D) (toConv (AlgHom.id R D))).ofConv

/-- Naturality determines every value from the universal algebra point. -/
theorem EndFamily.app_eq (F : EndFamily R D) {A : CommAlgCat.{u} (CommRingCat.of R)}
    (f : D →ₐ[R] A) :
    (F.app A (toConv f)).ofConv = f.comp F.classify := by
  simpa only [EndFamily.classify, AlgHom.comp_id] using
    F.naturality (A := CommAlgCat.of R D) f (toConv (AlgHom.id R D))

/-- The classifying algebra map preserves the counit. -/
theorem EndFamily.classify_counit (F : EndFamily R D) :
    (Bialgebra.counitAlgHom R D).comp F.classify = Bialgebra.counitAlgHom R D := by
  have h := F.app_eq (A := CommAlgCat.of R R) (Bialgebra.counitAlgHom R D)
  have he : toConv (Bialgebra.counitAlgHom R D) =
      (1 : WithConv (D →ₐ[R] R)) := by rfl
  rw [he, map_one] at h
  exact h.symm

/-- The classifying algebra map preserves comultiplication. -/
theorem EndFamily.classify_comul (F : EndFamily R D) :
    (Bialgebra.comulAlgHom R D).comp F.classify =
      (Algebra.TensorProduct.map F.classify F.classify).comp
        (Bialgebra.comulAlgHom R D) := by
  have h := congrArg (fun x => (F.app (CommAlgCat.of R (D ⊗[R] D)) x).ofConv)
    (TauCeti.Bialgebra.comulPoint_eq_include_mul (R := R) (H := D)).symm
  rw [map_mul, F.app_eq] at h
  have hlift : Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : D →ₐ[R] D ⊗[R] D).comp F.classify)
      ((Algebra.TensorProduct.includeRight : D →ₐ[R] D ⊗[R] D).comp F.classify)
      (fun _ _ => .all _ _) = Algebra.TensorProduct.map F.classify F.classify := by
    ext <;> simp
  apply AlgHom.ext
  intro d
  have hd := DFunLike.congr_fun h d
  change ((F.app (CommAlgCat.of R (D ⊗[R] D)))
      (toConv (Algebra.TensorProduct.includeLeft : D →ₐ[R] D ⊗[R] D)) *
    (F.app (CommAlgCat.of R (D ⊗[R] D)))
      (toConv (Algebra.TensorProduct.includeRight : D →ₐ[R] D ⊗[R] D))) d = _ at hd
  rw [AlgHom.convMul_apply, F.app_eq, F.app_eq, hlift] at hd
  exact hd.symm

/-- A natural convolution-monoid endomorphism induces a genuine coalgebra map. -/
def EndFamily.coalgHom (F : EndFamily R D) : D →ₗc[R] D where
  toLinearMap := F.classify.toLinearMap
  counit_comp := by
    apply LinearMap.ext
    intro d
    exact DFunLike.congr_fun F.classify_counit d
  map_comp_comul := by
    apply LinearMap.ext
    intro d
    exact (DFunLike.congr_fun F.classify_comul d).symm

section IntegralParameters

variable {k R C : Type u} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    [CommRing C] [Bialgebra k C]

/-- A natural convolution family over integral parameters is the identity if its
classifying map specializes to the identity on the original coalgebra. -/
theorem EndFamily.app_eq_self_of_specialize (F : EndFamily R (R ⊗[k] C))
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤)
    (ε : R →ₐ[k] k)
    (hF : ∀ c : C, GroupLike.specialize ε (F.classify (1 ⊗ₜ[k] c)) = c)
    {A : CommAlgCat.{u} (CommRingCat.of R)} (x : WithConv (R ⊗[k] C →ₐ[R] A)) :
    F.app A x = x := by
  have hc : F.coalgHom = CoalgHom.id R (R ⊗[k] C) :=
    GroupLike.endomorphism_eq_id_of_specialize hspan ε F.coalgHom hF
  have ha : F.classify = AlgHom.id R (R ⊗[k] C) := by
    apply AlgHom.ext
    intro d
    exact DFunLike.congr_fun hc d
  apply WithConv.ofConv_injective
  simpa only [ha, AlgHom.comp_id] using F.app_eq x.ofConv

end IntegralParameters

end Langlands.ConvolutionFamily
