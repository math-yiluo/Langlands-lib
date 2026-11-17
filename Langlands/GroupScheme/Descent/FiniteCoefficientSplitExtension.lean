import Langlands.GroupScheme.Descent.FiniteCoefficientFlatAffineQuotient
import Langlands.GroupScheme.Descent.FiniteCoefficientIsomorphism
import Langlands.GroupScheme.KernelSquareTransport
import Langlands.AbelianScheme.KernelBaseChange

/-! # Finite coefficient models of extensions with diagonalizable endpoints -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G H : GroupScheme (Spec (CommRingCat.of A))} {f : G ⟶ H}

/-- The recovery square identifies the model kernel over the original
algebra with the actual kernel of the original homomorphism. -/
def FlatAffineHomModel.kernelRecoveryIso (D : FlatAffineHomModel R A f) :
    (baseChange (Spec.algebraMap D.coefficients A)).obj (kernel D.hom) ≅ kernel f :=
  kernelBaseChangeIso (Spec.algebraMap D.coefficients A) D.hom ≪≫
    (kernelSquareIso f ((baseChange (Spec.algebraMap D.coefficients A)).map D.hom)
      D.sourceIso D.targetIso D.comm).symm

/-- Kernel recovery respects the actual inclusions into the recovered source. -/
@[reassoc]
theorem FlatAffineHomModel.kernelRecoveryIso_hom_ι (D : FlatAffineHomModel R A f) :
    D.kernelRecoveryIso.hom ≫ kernelι f =
      (baseChange (Spec.algebraMap D.coefficients A)).map (kernelι D.hom) ≫
        D.sourceIso.inv := by
  let e := kernelSquareIso f ((baseChange (Spec.algebraMap D.coefficients A)).map D.hom)
    D.sourceIso D.targetIso D.comm
  have he : e.inv ≫ kernelι f =
      kernelι ((baseChange (Spec.algebraMap D.coefficients A)).map D.hom) ≫
        D.sourceIso.inv := by
    apply (cancel_mono D.sourceIso.hom).mp
    rw [Category.assoc, ← kernelSquareIso_hom_ι f _ D.sourceIso D.targetIso D.comm]
    change e.inv ≫ e.hom ≫ _ = _
    rw [Iso.inv_hom_id_assoc, Category.assoc, D.sourceIso.inv_hom_id, Category.comp_id]
  change (kernelBaseChangeIso (Spec.algebraMap D.coefficients A) D.hom).hom ≫
    e.inv ≫ kernelι f = _
  rw [he, ← Category.assoc, kernelBaseChangeIso_hom_ι]

/-- Coefficient enlargement preserves the flat-surjective model map. -/
def FlatAffineQuotientModel.enlarge (D : FlatAffineQuotientModel R A f)
    (T : Subalgebra D.coefficients A) (hT : T.FG) : FlatAffineQuotientModel R A f where
  toFlatAffineHomModel := D.toFlatAffineHomModel.enlarge T hT
  homFlat := MorphismProperty.overPullbackMap (P := @Flat)
    (Spec.algebraMap D.coefficients T) D.hom.hom.hom D.homFlat
  homSurjective := MorphismProperty.overPullbackMap (P := @Surjective)
    (Spec.algebraMap D.coefficients T) D.hom.hom.hom D.homSurjective

/-- Diagonalizability of an affine finitely presented group after base
change descends to a finite coefficient stage. -/
theorem exists_fg_isDiagonalizable_of_baseChange
    {K : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffine K.X.left] [LocallyOfFinitePresentation K.X.hom]
    (hK : RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (Spec.algebraMap R A)).obj K)) (s : Finset A) :
    ∃ (T : Subalgebra R A), T.FG ∧ (s : Set A) ⊆ T ∧
      RelativeMultiplicativeType.IsDiagonalizable
        ((baseChange (Spec.algebraMap R T)).obj K) := by
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ := hK
  let : AddCommGroup Λ := hΛ
  let : AddGroup.FG Λ := hfg
  exact exists_fg_isDiagonalizable R A K Λ
    (e ≪≫ (Diagonalizable.relativeModelIso (CommRingCat.of A) Λ).symm) s

variable (R A)

/-- An exact affine fppf sequence over finite coefficients whose actual
kernel and quotient are both diagonalizable. -/
structure SplitFlatAffineQuotientModel (f : G ⟶ H) extends FlatAffineQuotientModel R A f where
  kernelDiagonalizable : RelativeMultiplicativeType.IsDiagonalizable (kernel hom)
  targetDiagonalizable : RelativeMultiplicativeType.IsDiagonalizable target

variable {R A}

/-- Enlarge a quotient model until both its kernel and quotient are
diagonalizable, whenever those original groups are diagonalizable. -/
theorem FlatAffineQuotientModel.exists_split_enlargement
    (D : FlatAffineQuotientModel R A f)
    (hK : RelativeMultiplicativeType.IsDiagonalizable (kernel f))
    (hH : RelativeMultiplicativeType.IsDiagonalizable H) :
    ∃ E : SplitFlatAffineQuotientModel R A f, D.coefficients ≤ E.coefficients := by
  let := D.kernelAffine
  let := D.kernelFinitePresentation
  have : IsAffine (kernel D.hom).X.left :=
    isAffine_of_isAffineHom (kernel D.hom).X.hom
  have hKA : RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (Spec.algebraMap D.coefficients A)).obj (kernel D.hom)) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso D.toFlatAffineHomModel.kernelRecoveryIso hK
  obtain ⟨T, hT, -, hKT⟩ := exists_fg_isDiagonalizable_of_baseChange hKA ∅
  let D₁ := D.enlarge T hT
  have hK₁ : RelativeMultiplicativeType.IsDiagonalizable (kernel D₁.hom) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (kernelBaseChangeIso (Spec.algebraMap D.coefficients T) D.hom).symm hKT
  let := D₁.targetAffine
  let := D₁.targetFinitePresentation
  have : IsAffine D₁.target.X.left := isAffine_of_isAffineHom D₁.target.X.hom
  have hHA : RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (Spec.algebraMap D₁.coefficients A)).obj D₁.target) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso D₁.targetIso.symm hH
  obtain ⟨U, hU, -, hHU⟩ := exists_fg_isDiagonalizable_of_baseChange hHA ∅
  let D₂ := D₁.enlarge U hU
  have hK₂ : RelativeMultiplicativeType.IsDiagonalizable (kernel D₂.hom) :=
    RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (kernelBaseChangeIso (Spec.algebraMap D₁.coefficients U) D₁.hom).symm
      (hK₁.baseChange (Spec.algebraMap D₁.coefficients U))
  refine ⟨{
    toFlatAffineQuotientModel := D₂
    kernelDiagonalizable := hK₂
    targetDiagonalizable := hHU }, ?_⟩
  intro x hx
  exact U.algebraMap_mem ⟨x, T.algebraMap_mem ⟨x, hx⟩⟩

variable (R A)

/-- Extensions with diagonalizable kernel and quotient admit exact
finite coefficient models with diagonalizable endpoints. -/
theorem exists_splitFlatAffineQuotientModel
    (f : G ⟶ H) [IsAffine G.X.left] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [IsAffine H.X.left] [Flat H.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    [Flat f.hom.hom.left] [Surjective f.hom.hom.left]
    (hK : RelativeMultiplicativeType.IsDiagonalizable (kernel f))
    (hH : RelativeMultiplicativeType.IsDiagonalizable H) (s : Finset A) :
    ∃ D : SplitFlatAffineQuotientModel R A f, (s : Set A) ⊆ D.coefficients := by
  obtain ⟨D, hs⟩ := exists_flatAffineQuotientModel R A f s
  obtain ⟨E, hDE⟩ := D.exists_split_enlargement hK hH
  exact ⟨E, hs.trans hDE⟩

/-- Choose a finite coefficient exact extension model with split endpoints. -/
def splitFlatAffineQuotientModel
    (f : G ⟶ H) [IsAffine G.X.left] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [IsAffine H.X.left] [Flat H.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    [Flat f.hom.hom.left] [Surjective f.hom.hom.left]
    (hK : RelativeMultiplicativeType.IsDiagonalizable (kernel f))
    (hH : RelativeMultiplicativeType.IsDiagonalizable H) :
    SplitFlatAffineQuotientModel R A f :=
  Classical.choose (exists_splitFlatAffineQuotientModel R A f hK hH ∅)

/-- The exact model is defined over a noetherian ring if the initial
ground ring is noetherian. -/
theorem SplitFlatAffineQuotientModel.noetherian [IsNoetherianRing R]
    (D : SplitFlatAffineQuotientModel R A f) : IsNoetherianRing D.coefficients :=
  D.toFlatAffineHomModel.noetherian R A

variable {R A}

/-- Recover any supplied monomorphic representative of the original full
kernel from the actual model kernel. -/
def FlatAffineQuotientModel.kernelRepresentativeRecoveryIso
    (D : FlatAffineQuotientModel R A f) {N : GroupScheme (Spec (CommRingCat.of A))}
    (i : N ⟶ G) [Mono i.hom.hom]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) f) :
    (baseChange (Spec.algebraMap D.coefficients A)).obj (kernel D.hom) ≅ N :=
  D.toFlatAffineHomModel.kernelRecoveryIso ≪≫ KernelRepresentative.iso f i hq.2.2.2

/-- The recovered kernel representative retains its original inclusion. -/
@[reassoc]
theorem FlatAffineQuotientModel.kernelRepresentativeRecoveryIso_hom_comp
    (D : FlatAffineQuotientModel R A f) {N : GroupScheme (Spec (CommRingCat.of A))}
    (i : N ⟶ G) [Mono i.hom.hom]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) f) :
    (D.kernelRepresentativeRecoveryIso i hq).hom ≫ i =
      (baseChange (Spec.algebraMap D.coefficients A)).map (kernelι D.hom) ≫
        D.sourceIso.inv := by
  simp only [kernelRepresentativeRecoveryIso, Iso.trans_hom, Category.assoc,
    KernelRepresentative.iso_hom_comp, FlatAffineHomModel.kernelRecoveryIso_hom_ι]

variable (R A)

/-- The original monic-kernel formulation of an exact extension with
diagonalizable endpoints gives the same finite coefficient model. -/
theorem exists_splitFlatAffineQuotientModel_of_quotient
    {N : GroupScheme (Spec (CommRingCat.of A))}
    (i : N ⟶ G) (f : G ⟶ H) [Mono i.hom.hom]
    [IsAffine G.X.left] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [IsAffine H.X.left] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) f)
    (hN : RelativeMultiplicativeType.IsDiagonalizable N)
    (hH : RelativeMultiplicativeType.IsDiagonalizable H) (s : Finset A) :
    ∃ D : SplitFlatAffineQuotientModel R A f, (s : Set A) ⊆ D.coefficients := by
  let := hq.1
  let := hq.2.1
  exact exists_splitFlatAffineQuotientModel R A f
    (RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (KernelRepresentative.iso f i hq.2.2.2) hN) hH s

end Langlands.GroupScheme.Descent.FiniteCoefficient
