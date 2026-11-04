import Langlands.Algebra.CentralTorusExtensionHopf
import Langlands.GroupScheme.HopfSpecPoints
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Central extensions of spectra of Hopf algebras

For Hopf algebra maps `φ : B → A` and `π : A → C` over a commutative ring, let
`z = Spec π : Spec C → Spec A` and `p = Spec φ : Spec A → Spec B`. If `z` is a central closed
subgroup and `p` is an fppf quotient map with kernel `z`, then `π` is surjective, `φ` is
faithfully flat, `π ∘ φ` is trivial, the coaction of `C` on `A` through `π` is central, and its
invariants come from `B`. For split tori `Spec B` and `Spec C` these are the hypotheses of
`CentralTorusExtensionHopf.IsCentralExtension`. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralExtensionHopfSpec

open HopfSpecPoints RelativeRoot

/-- A ring map whose spectrum map is a closed immersion is surjective. -/
theorem surjective_of_isClosedImmersion {R S : CommRingCat.{u}} (f : R ⟶ S)
    [IsClosedImmersion (Spec.map f)] : Function.Surjective f := by
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map f)).2
  have he : (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop ≫ (Scheme.ΓSpecIso S).hom = f := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hh : Function.Surjective
      ((Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop ≫ (Scheme.ΓSpecIso S).hom) :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom).2.comp
      (hs.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2)
  rwa [he] at hh

variable {R : CommRingCat.{u}} {A B C : CommHopfAlgCat.{u} R}

/-- A Hopf algebra map whose spectrum is a closed subgroup is surjective. -/
theorem surjective_of_isClosedSubgroup (π : A ⟶ C)
    (h : IsClosedSubgroup ((hopfSpec R).map π.op)) : Function.Surjective π.hom := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (π.hom : A →ₐ[R] C).toRingHom)) := h
  exact surjective_of_isClosedImmersion (CommRingCat.ofHom (π.hom : A →ₐ[R] C).toRingHom)

/-- A Hopf algebra map whose spectrum is flat and surjective is faithfully flat. -/
theorem faithfullyFlat_of_isFppfQuotient (φ : B ⟶ A) {N : SubgroupFunctor ((hopfSpec R).obj (op A))}
    (h : IsFppfQuotient N ((hopfSpec R).map φ.op)) :
    (φ.hom : B →ₐ[R] A).toRingHom.FaithfullyFlat :=
  (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (φ.hom : B →ₐ[R] A).toRingHom)).mp
    ⟨h.1, h.2.1⟩

/-- If the kernel of `Spec φ` is the range of `Spec π`, then `π ∘ φ` is trivial. -/
theorem comp_eq_of_range_kernelι (φ : B ⟶ A) (π : A ⟶ C)
    (h : SubgroupFunctor.range (kernelι ((hopfSpec R).map φ.op)) =
      SubgroupFunctor.range ((hopfSpec R).map π.op)) :
    (π.hom : A →ₐ[R] C).comp (φ.hom : B →ₐ[R] A) =
      (Algebra.ofId R C).comp (Bialgebra.counitAlgHom R B) := by
  let x := specPoint (Y := CommAlgCat.of R C) (AlgHom.id R C)
  have hx : x ≫ ((hopfSpec R).map π.op).hom.hom ∈
      (SubgroupFunctor.range (kernelι ((hopfSpec R).map φ.op))).carrier _ := by
    rw [h]
    exact ⟨x, rfl⟩
  rw [mem_range_kernelι_iff, specPoint_comp_map, specPoint_comp_map, specPoint_one] at hx
  simpa using specPoint_injective hx

/-- Centrality of `Spec π` makes the left and right coactions of `C` on `A` through `π` agree. -/
theorem rTensor_comul_eq_of_isCentral (π : A ⟶ C) (hc : IsCentral ((hopfSpec R).map π.op))
    (a : A) :
    (π.hom : A →ₗ[R] C).rTensor A (comul a) =
      TensorProduct.comm R A C ((π.hom : A →ₗ[R] C).lTensor A (comul a)) := by
  let iL : C →ₐ[R] C ⊗[R] A := Algebra.TensorProduct.includeLeft
  let iR : A →ₐ[R] C ⊗[R] A := Algebra.TensorProduct.includeRight
  have hcomm := commute_of_mem_center
    (hc _ (specPoint (Y := CommAlgCat.of R (C ⊗[R] A)) iL))
    (specPoint (Y := CommAlgCat.of R (C ⊗[R] A)) iR)
  have heq := hcomm.eq
  rw [specPoint_comp_map, specPoint_mul, specPoint_mul] at heq
  have key := congrArg (fun f => f a) (specPoint_injective heq)
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] at key
  have e1 : ∀ t : A ⊗[R] A, Algebra.TensorProduct.lift (iL.comp (π.hom : A →ₐ[R] C)) iR
      (fun _ _ => .all _ _) t = (π.hom : A →ₗ[R] C).rTensor A t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [iL, iR]
    | add x y hx hy => simp only [map_add, hx, hy]
  have e2 : ∀ t : A ⊗[R] A, Algebra.TensorProduct.lift iR (iL.comp (π.hom : A →ₐ[R] C))
      (fun _ _ => .all _ _) t =
        TensorProduct.comm R A C ((π.hom : A →ₗ[R] C).lTensor A t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [iL, iR]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [← e1, ← e2]
  exact key

/-- Invariance under the coaction of `C` through `π` descends along the faithfully flat quotient
map: an element of `A` whose coaction is trivial comes from `B`. -/
theorem exists_eq_of_lTensor_comul_eq (φ : B ⟶ A) (π : A ⟶ C)
    (hz : Mono ((hopfSpec R).map π.op).hom.hom)
    (hq : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec R).map π.op)) ((hopfSpec R).map φ.op))
    (a : A) (ha : (π.hom : A →ₗ[R] C).lTensor A (comul a) = a ⊗ₜ 1) :
    ∃ b, φ.hom b = a := by
  let : Algebra B A := (φ.hom : B →ₐ[R] A).toRingHom.toAlgebra
  have : IsScalarTower R B A :=
    IsScalarTower.of_algebraMap_eq fun r => ((φ.hom : B →ₐ[R] A).commutes r).symm
  have : Module.FaithfullyFlat B A := faithfullyFlat_of_isFppfQuotient φ hq
  let iL : A →ₐ[R] A ⊗[B] A := Algebra.TensorProduct.includeLeft
  let iR : A →ₐ[R] A ⊗[B] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[B] A ⊗[B] A).restrictScalars R
  let Y := CommAlgCat.of R (A ⊗[B] A)
  have hxy : specPoint (Y := Y) iL ≫ ((hopfSpec R).map φ.op).hom.hom =
      specPoint (Y := Y) iR ≫ ((hopfSpec R).map φ.op).hom.hom := by
    rw [specPoint_comp_map, specPoint_comp_map]
    congr 1
    ext b
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul (R := B) b
  have hmem := (hq.fibers_iff ⟨hz, rfl⟩ _ _ _).mp hxy
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hmem
  obtain ⟨ω, rfl⟩ := exists_specPoint w
  rw [specPoint_comp_map, eq_inv_mul_iff_mul_eq, specPoint_mul] at hw
  have key := congrArg (fun f => f a) (specPoint_injective hw)
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] at key
  have e : ∀ t : A ⊗[R] A, Algebra.TensorProduct.lift iL (ω.comp (π.hom : A →ₐ[R] C))
      (fun _ _ => .all _ _) t =
        Algebra.TensorProduct.lift iL ω (fun _ _ => .all _ _)
          ((π.hom : A →ₗ[R] C).lTensor A t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [e, ha, Algebra.TensorProduct.lift_tmul, map_one, mul_one] at key
  have hmem' : a ∈ Algebra.TensorProduct.includeLeftRingHom.eqLocus
      (Algebra.TensorProduct.includeRight (R := B) (A := A) (B := A)).toRingHom := key
  rw [← SetLike.mem_coe,
    (Algebra.IsEffective.of_faithfullyFlat B A).eqLocus_includeLeft_includeRight] at hmem'
  obtain ⟨b, hb⟩ := hmem'
  exact ⟨b, hb⟩

/-! ### Split tori -/

section Split

variable {K : Type u} [Field K] {I J : Type u} {A : CommHopfAlgCat.{u} (CommRingCat.of K)}

/-- The Hopf algebra data of a central extension of split tori: if `Spec π` is a central closed
subgroup of `Spec A` and `Spec φ` is an fppf quotient map with kernel `Spec π`, then `φ` and `π`
satisfy `CentralTorusExtensionHopf.IsCentralExtension`. -/
theorem isCentralExtension
    (φ : Diagonalizable.hopfAlgebra (CommRingCat.of K) (I → ℤ) ⟶ A)
    (π : A ⟶ Diagonalizable.hopfAlgebra (CommRingCat.of K) (J → ℤ))
    (hz : IsClosedSubgroup ((hopfSpec (CommRingCat.of K)).map π.op))
    (hc : IsCentral ((hopfSpec (CommRingCat.of K)).map π.op))
    (hq : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec (CommRingCat.of K)).map π.op))
      ((hopfSpec (CommRingCat.of K)).map φ.op)) :
    CentralTorusExtensionHopf.IsCentralExtension (K := K) (A := A) φ.hom π.hom where
  injective := (faithfullyFlat_of_isFppfQuotient φ hq).injective
  surjective := surjective_of_isClosedSubgroup π hz
  comp_eq b := by
    have h := congrArg (fun f => f b) (comp_eq_of_range_kernelι φ π hq.2.2.2)
    simpa using h
  isCentral := rTensor_comul_eq_of_isCentral π hc
  invariants a ha := by
    have : IsClosedImmersion ((hopfSpec (CommRingCat.of K)).map π.op).hom.hom.left := hz
    refine exists_eq_of_lTensor_comul_eq φ π (Over.mono_of_mono_left _) hq a ?_
    rw [GroupAlgebraCoaction.mem_grade_iff, GroupAlgebraCoaction.coaction_apply] at ha
    rw [← (AddMonoidAlgebra.scalarTensorEquiv K A).symm_apply_apply
      ((π.hom : A →ₗ[K] AddMonoidAlgebra K (J → ℤ)).lTensor A (comul a)), ha,
      AddMonoidAlgebra.scalarTensorEquiv_symm_single, ← AddMonoidAlgebra.one_def]

end Split

end Langlands.GroupScheme.CentralExtensionHopfSpec
