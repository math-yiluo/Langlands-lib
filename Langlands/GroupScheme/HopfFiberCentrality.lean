import Langlands.GroupScheme.HopfSpecCentrality
import Langlands.GroupScheme.HopfMorphismBaseChange
import Langlands.GroupScheme.CorepresentedComultiplication
import Langlands.AlgebraicGeometry.FiberMapEqualityDescent

/-! # Fibre centrality in actual Hopf algebra coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Topology

namespace Langlands.GroupScheme.HopfFiberCentrality

open Langlands.Algebra.FiberMapEquality

variable {R : CommRingCat.{u}} {A C : CommHopfAlgCat.{u} R}

/-- The coaction obtained by applying the subgroup map to the first factor. -/
def leftCoaction (π : A ⟶ C) : A →ₐ[R] C ⊗[R] A :=
  (Algebra.TensorProduct.map π.hom.toAlgHom (AlgHom.id R A)).comp
    (Bialgebra.comulAlgHom R A)

/-- The coaction obtained from the second factor, with the factors exchanged. -/
def rightCoaction (π : A ⟶ C) : A →ₐ[R] C ⊗[R] A :=
  (Algebra.TensorProduct.comm R A C).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id R A) π.hom.toAlgHom).comp
      (Bialgebra.comulAlgHom R A))

theorem leftCoaction_apply (π : A ⟶ C) (a : A) :
    leftCoaction π a = (π.hom : A →ₗ[R] C).rTensor A (comul a) := rfl

theorem rightCoaction_apply (π : A ⟶ C) (a : A) :
    rightCoaction π a =
      TensorProduct.comm R A C ((π.hom : A →ₗ[R] C).lTensor A (comul a)) := rfl

/-- Equality of the two actual algebra maps is all-test centrality. -/
theorem isCentral_iff_coaction_eq (π : A ⟶ C) :
    IsCentral ((hopfSpec R).map π.op) ↔ leftCoaction π = rightCoaction π := by
  rw [HopfSpecCentrality.isCentral_iff_rTensor_comul_eq]
  exact ⟨fun h => AlgHom.ext h, fun h a => AlgHom.congr_fun h a⟩

section ScalarExtension

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The actual Hopf map after scalar extension. -/
def scalarExtensionMap (π : A ⟶ C) :
    HopfCoordinates.scalarExtension R S A ⟶ HopfCoordinates.scalarExtension R S C :=
  CommHopfAlgCat.ofHom (Bialgebra.TensorProduct.map (BialgHom.id S S) π.hom)

/-- The tensor comparison for the scalar extension of the coaction target. -/
def coactionTensorIso :
    S ⊗[R] (C ⊗[R] A) ≃ₐ[S] (S ⊗[R] C) ⊗[S] (S ⊗[R] A) :=
  (Algebra.TensorProduct.assoc R R S S C A).symm.trans
    (Algebra.TensorProduct.cancelBaseChange R S S (S ⊗[R] C) A).symm

@[simp]
theorem coactionTensorIso_tmul (s : S) (c : C) (a : A) :
    coactionTensorIso (A := A) (C := C) S (s ⊗ₜ[R] (c ⊗ₜ[R] a)) =
      (s ⊗ₜ[R] c) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] a) := by
  simp [coactionTensorIso]

theorem leftCoaction_scalarExtension (π : A ⟶ C) :
    leftCoaction (R := CommRingCat.of S) (scalarExtensionMap S π) =
      (coactionTensorIso (A := A) (C := C) S).toAlgHom.comp
        (baseChangeMap S (leftCoaction π)) := by
  apply (tensorMap_eq_iff S _ _).mpr
  intro a
  simp only [leftCoaction, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    baseChangeMap_tmul]
  induction comul (R := R) a using TensorProduct.inductionOn with
  | tmul a₁ a₂ => simp [scalarExtensionMap]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

theorem rightCoaction_scalarExtension (π : A ⟶ C) :
    rightCoaction (R := CommRingCat.of S) (scalarExtensionMap S π) =
      (coactionTensorIso (A := A) (C := C) S).toAlgHom.comp
        (baseChangeMap S (rightCoaction π)) := by
  apply (tensorMap_eq_iff S _ _).mpr
  intro a
  simp only [rightCoaction, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    baseChangeMap_tmul]
  induction comul (R := R) a using TensorProduct.inductionOn with
  | tmul a₁ a₂ => simp [scalarExtensionMap]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/-- Centrality of the actual scalar-extension Hopf spectrum is equality of
the scalar extensions of the original two algebra maps. -/
theorem isCentral_scalarExtension_iff (π : A ⟶ C) :
    IsCentral ((hopfSpec (CommRingCat.of S)).map (scalarExtensionMap S π).op) ↔
      baseChangeMap S (leftCoaction π) = baseChangeMap S (rightCoaction π) := by
  rw [isCentral_iff_coaction_eq, leftCoaction_scalarExtension, rightCoaction_scalarExtension]
  constructor
  · intro h
    apply AlgHom.ext
    intro x
    apply (coactionTensorIso (A := A) (C := C) S).injective
    exact AlgHom.congr_fun h x
  · intro h
    rw [h]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the actual group-scheme scalar-extension comparison. -/
theorem baseChange_hopfSpec (π : A ⟶ C) :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        ((hopfSpec R).map π.op) =
      (HopfCoordinates.baseChangeSpecIso R S C).hom ≫
        (hopfSpec (CommRingCat.of S)).map (scalarExtensionMap S π).op ≫
          (HopfCoordinates.baseChangeSpecIso R S A).inv := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact HopfMorphismBaseChange.tensorSpecIso_naturality π.hom.toAlgHom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Centrality of the actual group-scheme pullback is the original pair of
coaction equations after scalar extension. -/
theorem isCentral_baseChange_iff (π : A ⟶ C) :
    IsCentral ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
      ((hopfSpec R).map π.op)) ↔
      baseChangeMap S (leftCoaction π) = baseChangeMap S (rightCoaction π) := by
  rw [← isCentral_scalarExtension_iff, baseChange_hopfSpec]
  constructor
  · intro h
    have h' := (h.comp (HopfCoordinates.baseChangeSpecIso R S C).inv).comp_iso
      (HopfCoordinates.baseChangeSpecIso R S A)
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using h'
  · intro h
    exact (h.comp (HopfCoordinates.baseChangeSpecIso R S C).hom).comp_iso
      (HopfCoordinates.baseChangeSpecIso R S A).symm

end ScalarExtension

section FibreLocus

/-- Primes at which the actual residue-field pullback homomorphism is central. -/
def fiberCentralityLocus (π : A ⟶ C) : Set (PrimeSpectrum R) :=
  {p | IsCentral ((baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)))).map
      ((hopfSpec R).map π.op))}

theorem fiberCentralityLocus_eq (π : A ⟶ C) :
    fiberCentralityLocus π = fiberMapEqualityLocus (leftCoaction π) (rightCoaction π) := by
  ext p
  exact isCentral_baseChange_iff p.asIdeal.ResidueField π

private theorem fiberMapEqualityLocus_postcomp_equiv
    {R₀ X Y Z : Type u} [CommRing R₀] [CommRing X] [CommRing Y] [CommRing Z]
    [Algebra R₀ X] [Algebra R₀ Y] [Algebra R₀ Z]
    (f g : X →ₐ[R₀] Y) (e : Y ≃ₐ[R₀] Z) :
    fiberMapEqualityLocus (e.toAlgHom.comp f) (e.toAlgHom.comp g) =
      fiberMapEqualityLocus f g := by
  ext p
  change baseChangeMap p.asIdeal.ResidueField _ = baseChangeMap p.asIdeal.ResidueField _ ↔
    baseChangeMap p.asIdeal.ResidueField f = baseChangeMap p.asIdeal.ResidueField g
  simp only [baseChangeMap_eq_iff, AlgHom.comp_apply]
  apply forall_congr'
  intro a
  let E := Algebra.TensorProduct.congr
    (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.ResidueField)
      e
  constructor
  · intro h
    apply E.injective
    simpa [E] using h
  · intro h
    simpa [E] using congrArg E h

/-- Centrality of every full residue fibre is preserved and reflected at the
contracted prime under arbitrary scalar extension. -/
theorem fiberCentralityLocus_scalarExtension
    (S : Type u) [CommRing S] [Algebra R S] (π : A ⟶ C) :
    fiberCentralityLocus (R := CommRingCat.of S) (scalarExtensionMap S π) =
      PrimeSpectrum.comap (algebraMap R S) ⁻¹' fiberCentralityLocus π := by
  rw [fiberCentralityLocus_eq, leftCoaction_scalarExtension, rightCoaction_scalarExtension,
    fiberMapEqualityLocus_postcomp_equiv, fiberMapEqualityLocus_baseChange,
    fiberCentralityLocus_eq]

/-- The full residue-fibre centrality locus is constructible over a
noetherian base for finite type Hopf algebras. -/
theorem isConstructible_fiberCentralityLocus
    [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FiniteType R C]
    (π : A ⟶ C) : IsConstructible (fiberCentralityLocus π) := by
  let : Algebra.FiniteType R (C ⊗[R] A) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R C) inferInstance
  rw [fiberCentralityLocus_eq]
  exact isConstructible_fiberMapEqualityLocus _ _

end FibreLocus

section Coefficients

variable (S : Type u) [CommRing S] [Algebra R S]

/-- A finite coefficient algebra retaining actual centrality on every full
residue-field fibre, together with any prescribed finite set of coefficients. -/
structure FiberCentralityCoefficientModel (π : A ⟶ C) (t : Finset S) where
  coefficients : Subalgebra R S
  finiteGeneration : coefficients.FG
  contains : (↑t : Set S) ⊆ coefficients
  centralFibres : fiberCentralityLocus (R := CommRingCat.of coefficients)
    (scalarExtensionMap coefficients π) = Set.univ

theorem exists_fg_subalgebra_fiberCentrality
    [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FiniteType R C]
    (π : A ⟶ C)
    (H : fiberCentralityLocus (R := CommRingCat.of S) (scalarExtensionMap S π) = Set.univ)
    (t : Finset S) :
    ∃ T : Subalgebra R S, T.FG ∧ (↑t : Set S) ⊆ T ∧
      fiberCentralityLocus (R := CommRingCat.of T) (scalarExtensionMap T π) = Set.univ := by
  rw [fiberCentralityLocus_scalarExtension] at H
  obtain ⟨T, hT, ht, hc⟩ :=
    Langlands.AlgebraicGeometry.FiberMapEqualityDescent.exists_fg_subalgebra_preimage_eq_univ
      (fiberCentralityLocus π) (isConstructible_fiberCentralityLocus π) H t
  exact ⟨T, hT, ht, (fiberCentralityLocus_scalarExtension T π).trans hc⟩

/-- Choose the finite coefficient algebra whose existence follows from
constructibility and the actual spectrum limit. -/
def fiberCentralityCoefficientModel
    [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FiniteType R C]
    (π : A ⟶ C)
    (H : fiberCentralityLocus (R := CommRingCat.of S) (scalarExtensionMap S π) = Set.univ)
    (t : Finset S) : FiberCentralityCoefficientModel S π t := by
  let h := exists_fg_subalgebra_fiberCentrality S π H t
  exact ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2.1, (Classical.choose_spec h).2.2⟩

end Coefficients

end Langlands.GroupScheme.HopfFiberCentrality
