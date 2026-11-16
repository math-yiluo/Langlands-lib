import Langlands.GroupScheme.Torus.CentralExtensionHopfSpec
import Langlands.GroupScheme.Reductive.ArtinianCentrality

/-! # Centrality of spectra of Hopf algebra maps -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HopfSpecCentrality

open HopfSpecPoints

variable {R : CommRingCat.{u}} {A C : CommHopfAlgCat.{u} R}

set_option backward.isDefEq.respectTransparency false in
theorem isCentral_of_specPoint_commute (π : A ⟶ C)
    (h : ∀ (Y : CommAlgCat.{u} R) (f : C →ₐ[R] Y) (g : A →ₐ[R] Y),
      Commute (specPoint f ≫ ((hopfSpec R).map π.op).hom.hom) (specPoint g)) :
    IsCentral ((hopfSpec R).map π.op) := by
  let H := (hopfSpec R).obj (op C)
  let G := (hopfSpec R).obj (op A)
  apply ArtinianCentrality.isCentral_of_universal_commute
  change Commute (fst H.X G.X ≫ ((hopfSpec R).map π.op).hom.hom) (snd H.X G.X)
  have : IsAffine H.X.left := by
    change IsAffine (Spec _)
    infer_instance
  have : IsAffine G.X.left := by
    change IsAffine (Spec _)
    infer_instance
  have haf : IsAffine (H.X ⊗ G.X).left := by
    change IsAffine (Limits.pullback H.X.hom G.X.hom)
    infer_instance
  have he := (essImage_algSpec (R := R)).mpr haf
  let e := he.getIso
  obtain ⟨f, hf⟩ := exists_specPoint (e.hom ≫ fst H.X G.X)
  obtain ⟨g, hg⟩ := exists_specPoint (e.hom ≫ snd H.X G.X)
  apply (cancel_epi e.hom).mp
  simpa only [MonObj.comp_mul, ← Category.assoc, ← hf, ← hg] using (h _ f g).eq

theorem isCentral_of_rTensor_comul_eq (π : A ⟶ C)
    (h : ∀ a : A, (π.hom : A →ₗ[R] C).rTensor A (comul a) =
      TensorProduct.comm R A C ((π.hom : A →ₗ[R] C).lTensor A (comul a))) :
    IsCentral ((hopfSpec R).map π.op) := by
  apply isCentral_of_specPoint_commute
  intro Y f g
  change _ * _ = _ * _
  rw [specPoint_comp_map, specPoint_mul, specPoint_mul]
  congr 1
  ext a
  have he := congrArg (Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)) (h a)
  have hleft : ∀ t : A ⊗[R] A,
      Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)
        ((π.hom : A →ₗ[R] C).rTensor A t) =
      Algebra.TensorProduct.lift (f.comp π.hom.toAlgHom) g
        (fun _ _ => .all _ _) t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hright : ∀ t : A ⊗[R] A,
      Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)
        (TensorProduct.comm R A C ((π.hom : A →ₗ[R] C).lTensor A t)) =
      Algebra.TensorProduct.lift g (f.comp π.hom.toAlgHom)
        (fun _ _ => .all _ _) t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  simpa only [hleft, hright, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] using he

theorem isCentral_iff_rTensor_comul_eq (π : A ⟶ C) :
    IsCentral ((hopfSpec R).map π.op) ↔
      ∀ a : A, (π.hom : A →ₗ[R] C).rTensor A (comul a) =
        TensorProduct.comm R A C ((π.hom : A →ₗ[R] C).lTensor A (comul a)) :=
  ⟨CentralExtensionHopfSpec.rTensor_comul_eq_of_isCentral π,
    isCentral_of_rTensor_comul_eq π⟩

/-- Bundle the unchanged monomorphic Hopf spectrum as commutative using its tensor coactions. -/
def commGroupSchemeOfTensorCoactions (π : A ⟶ C)
    [Mono ((hopfSpec R).map π.op).hom.hom]
    (h : ∀ a : A, (π.hom : A →ₗ[R] C).rTensor A (comul a) =
      TensorProduct.comm R A C ((π.hom : A →ₗ[R] C).lTensor A (comul a))) :
    CommGroupScheme (Spec R) :=
  (isCentral_of_rTensor_comul_eq π h).commGroupScheme

@[simp]
theorem commGroupSchemeOfTensorCoactions_toGrp (π : A ⟶ C)
    [Mono ((hopfSpec R).map π.op).hom.hom]
    (h : ∀ a : A, (π.hom : A →ₗ[R] C).rTensor A (comul a) =
      TensorProduct.comm R A C ((π.hom : A →ₗ[R] C).lTensor A (comul a))) :
    (commGroupSchemeOfTensorCoactions π h).toGrp = (hopfSpec R).obj (op C) := rfl

end Langlands.GroupScheme.HopfSpecCentrality
