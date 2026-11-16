import Langlands.Algebra.GroupAlgebraCoactionCentrality
import Langlands.GroupScheme.HopfSpecCentrality
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Langlands.AbelianScheme.KernelBaseChange
import Mathlib.RingTheory.Ideal.Maps

/-! # Centrality of a diagonalizable homomorphism through a nilpotent reduction -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.DiagonalizableInfinitesimalCentrality

open HopfSpecPoints

variable {R : CommRingCat.{u}} {A C : CommHopfAlgCat.{u} R}

set_option backward.isDefEq.respectTransparency false in
theorem specPoint_commute_of_quotient_central (π : A ⟶ C) (I : Ideal R)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map
      ((hopfSpec R).map π.op)))
    (Y : CommAlgCat.{u} R) (hY : ∀ r : R, r ∈ I → algebraMap R Y r = 0)
    (f : C →ₐ[R] Y) (g : A →ₐ[R] Y) :
    Commute (specPoint f ≫ ((hopfSpec R).map π.op).hom.hom) (specPoint g) := by
  let b := Spec.algebraMap R (R ⧸ I)
  let t : Spec (CommRingCat.of Y) ⟶ Spec (CommRingCat.of (R ⧸ I)) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I (algebraMap R Y) hY))
  let T : Over (Spec (CommRingCat.of (R ⧸ I))) := Over.mk t
  let e : (Over.map b).obj T ≅ (algSpec R).obj (op Y) :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R Y)) = t ≫ b
      rw [Category.id_comp]
      change _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I (algebraMap R Y) hY)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
      rw [← Spec.map_comp]
      rfl)
  let H := (hopfSpec R).obj (op C)
  let G := (hopfSpec R).obj (op A)
  let x := (baseChangePointsEquiv b H T).symm (e.hom ≫ specPoint f)
  let y := (baseChangePointsEquiv b G T).symm (e.hom ≫ specPoint g)
  have hxy : Commute
      (x ≫ ((Over.pullback b).mapGrp.map ((hopfSpec R).map π.op)).hom.hom) y :=
    commute_of_mem_center (hc T x) y
  have he := congrArg (baseChangePointsEquiv b G T) hxy.eq
  apply (cancel_epi e.hom).mp
  simpa only [map_mul, baseChangePointsEquiv_comp, x, y,
    MulEquiv.apply_symm_apply, MonObj.comp_mul, Category.assoc] using he

open Langlands.GroupAlgebraCoaction

variable {N : Type u} [AddCommGroup N]

theorem coeff_eq_of_test_commute (π : A ⟶ Diagonalizable.hopfAlgebra R N)
    (B : CommAlgCat.{u} R) (q : A →ₐ[R] B)
    (h : Commute
      (specPoint (Y := CommAlgCat.of R (AddMonoidAlgebra B N))
        (AddMonoidAlgebra.mapAlgHom N (Algebra.ofId R B)) ≫
        ((hopfSpec R).map π.op).hom.hom)
      (specPoint (Y := CommAlgCat.of R (AddMonoidAlgebra B N))
        ((AddMonoidAlgebra.singleZeroAlgHom : B →ₐ[R] AddMonoidAlgebra B N).comp q)))
    (n : N) (a : A) :
    q (lact (coeffForm π.hom n) a) = q (proj π.hom n a) := by
  have he := h.eq
  rw [specPoint_comp_map, specPoint_mul, specPoint_mul] at he
  have ha := AlgHom.congr_fun (specPoint_injective he) a
  have hcoeff := congrArg (fun z : AddMonoidAlgebra B N => z.coeff n) ha
  let 𝓡 := Repr.arbitrary R a
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, ← 𝓡.eq, map_sum,
    Algebra.TensorProduct.lift_tmul, AddMonoidAlgebra.singleZeroAlgHom_apply,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_mul_single_zero,
    AddMonoidAlgebra.coeff_single_zero_mul, AddMonoidAlgebra.coeff_mapAlgHom,
    Algebra.ofId_apply] at hcoeff
  rw [lact_apply 𝓡, proj, ract_apply 𝓡, map_sum, map_sum]
  simpa [coeffForm_apply, Algebra.smul_def, mul_comm] using hcoeff

theorem coeff_sub_mem_of_quotient_central (π : A ⟶ Diagonalizable.hopfAlgebra R N)
    (I : Ideal R)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map
      ((hopfSpec R).map π.op))) (n : N) (a : A) :
    lact (coeffForm π.hom n) a - proj π.hom n a ∈ I • (⊤ : Submodule R A) := by
  let J := I.map (algebraMap R A)
  let B := CommAlgCat.of R (A ⧸ J)
  let q : A →ₐ[R] B := Ideal.Quotient.mkₐ R J
  let Y := CommAlgCat.of R (AddMonoidAlgebra B N)
  have hY : ∀ r : R, r ∈ I → algebraMap R Y r = 0 := by
    intro r hr
    change AddMonoidAlgebra.single 0 (Ideal.Quotient.mk J (algebraMap R A r)) = 0
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr
      (Ideal.mem_map_of_mem (algebraMap R A) hr)]
    exact AddMonoidAlgebra.single_zero _
  have h := specPoint_commute_of_quotient_central π I hc Y hY
    (AddMonoidAlgebra.mapAlgHom N (Algebra.ofId R B))
    ((AddMonoidAlgebra.singleZeroAlgHom : B →ₐ[R] AddMonoidAlgebra B N).comp q)
  have he := coeff_eq_of_test_commute π B q h n a
  rw [Ideal.smul_top_eq_map]
  change _ ∈ J
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he

/-- A diagonalizable-source Hopf-spectrum map is central if its nilpotent reduction is. -/
theorem isCentral_of_nilpotent_quotient (π : A ⟶ Diagonalizable.hopfAlgebra R N)
    (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map
      ((hopfSpec R).map π.op))) : IsCentral ((hopfSpec R).map π.op) := by
  apply HopfSpecCentrality.isCentral_of_rTensor_comul_eq
  exact GroupAlgebraCoaction.isCentral_of_coeff_sub_mem π.hom I hI
    (coeff_sub_mem_of_quotient_central π I hc)

/-- Bundle the unchanged monomorphic source using centrality lifted from the quotient. -/
def commGroupSchemeOfNilpotentQuotient (π : A ⟶ Diagonalizable.hopfAlgebra R N)
    [Mono ((hopfSpec R).map π.op).hom.hom]
    (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map
      ((hopfSpec R).map π.op))) : CommGroupScheme (Spec R) :=
  (isCentral_of_nilpotent_quotient π I hI hc).commGroupScheme

@[simp]
theorem commGroupSchemeOfNilpotentQuotient_toGrp (π : A ⟶ Diagonalizable.hopfAlgebra R N)
    [Mono ((hopfSpec R).map π.op).hom.hom]
    (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map
      ((hopfSpec R).map π.op))) :
    (commGroupSchemeOfNilpotentQuotient π I hI hc).toGrp =
      (hopfSpec R).obj (op (Diagonalizable.hopfAlgebra R N)) := rfl

end Langlands.GroupScheme.DiagonalizableInfinitesimalCentrality
