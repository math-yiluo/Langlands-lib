import Langlands.GroupScheme.NormalQuotientStatement
import Langlands.GroupScheme.AffineHomImageStatement
import Langlands.GroupScheme.MatrixRepresentation.CartierNormalKernel
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.Descent.AffineFppfQuotient
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationSourceDescent
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Unrestricted normal quotients from Cartier and affine images -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The unrestricted quotient assertion restricted to algebraically closed
fields. There is no smoothness or reducedness premise on either group. -/
def AlgClosedNormalQuotientExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G N : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G),
    IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom →
    IsClosedSubgroup i → (SubgroupFunctor.range i).IsNormal →
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
        IsAffineHom Q.X.hom ∧ LocallyOfFiniteType Q.X.hom ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q

/-- An fppf quotient of a locally finite-type group over a field has a locally
finite-type target. No smoothness assumption is needed. -/
theorem locallyOfFiniteType_target_of_fppfQuotient
    {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] {H : SubgroupFunctor G} {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient H q) : LocallyOfFiniteType Q.X.hom := by
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have : LocallyOfFinitePresentation (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : LocallyOfFinitePresentation Q.X.hom :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp
      q.hom.hom.left Q.X.hom
  infer_instance

/-- Effective affine descent reduces the exact unrestricted target to its
algebraically closed-field specialization. -/
theorem normalQuotientExistence_of_algClosed_quotients
    (h : AlgClosedNormalQuotientExistenceStatement.{u}) :
    NormalSubgroupQuotientExistenceStatement.{u} := by
  intro k _ G N i ha hl hi hn
  have : IsAffineHom G.X.hom := ha
  have : LocallyOfFiniteType G.X.hom := hl
  let Ω : Type u := AlgebraicClosure k
  let b : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let G' := (GroupScheme.baseChange b).obj G
  let N' := (GroupScheme.baseChange b).obj N
  let i' : N' ⟶ G' := (GroupScheme.baseChange b).map i
  have : IsAffineHom G'.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b))
  have : LocallyOfFiniteType G'.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b))
  have hi' : IsClosedSubgroup i' := hi.baseChange b
  have hn' : (SubgroupFunctor.range i').IsNormal := by
    change (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)).IsNormal
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange b
  obtain ⟨Q, q, hQa, _, hq⟩ := h Ω G' N' i' inferInstance inferInstance hi' hn'
  have : IsAffineHom Q.X.hom := hQa
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : IsAffine G'.X.left := isAffine_of_isAffineHom G'.X.hom
  have : QuasiCompact q.hom.hom.left := inferInstance
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨R, r, hRa, hr, _⟩ := Descent.exists_affine_fppfQuotient b i Q q hq
  have : IsAffine R.X.left := hRa
  exact ⟨R, r, inferInstance, locallyOfFiniteType_target_of_fppfQuotient hr, hr⟩

/-- Cartier and unrestricted affine image factorization produce the quotient
over every algebraically closed field, including nonreduced sources. -/
theorem algClosed_normalQuotientExistence_with_structural_inputs
    (hCartier : AffineCartierSmoothStatement.{u})
    (hImage : AffineHomImageStatement.{u}) :
    AlgClosedNormalQuotientExistenceStatement.{u} := by
  intro k _ _ G N i ha hl hi hn
  have : IsAffineHom G.X.hom := ha
  have : LocallyOfFiniteType G.X.hom := hl
  let D := MatrixRepresentation.normalKernelRepresentationWithCartier hCartier i hi hn
  let H := GeneralLinear.groupScheme (Fin D.dimension) (CommRingCat.of k)
  have : IsAffineHom H.X.hom := GeneralLinear.isAffineHom_groupScheme _ _
  have : Smooth H.X.hom :=
    GeneralLinear.smoothStatement (Fin D.dimension) (CommRingCat.of k)
  obtain ⟨Q, q, _, hQl, hQa, _, _, hq⟩ := hImage k G H D.representation
  rw [D.kernel_range] at hq
  exact ⟨Q, q, hQa, hQl, hq⟩

/-- The exact arbitrary-field quotient proposition follows from two explicitly
retained structural inputs, without adding premises to that proposition. -/
theorem normalQuotientExistence_with_structural_inputs
    (hCartier : AffineCartierSmoothStatement.{u})
    (hImage : AffineHomImageStatement.{u}) :
    NormalSubgroupQuotientExistenceStatement.{u} :=
  normalQuotientExistence_of_algClosed_quotients
    (algClosed_normalQuotientExistence_with_structural_inputs hCartier hImage)

/-- Actual quotient group and projection chosen from the conditional existence
theorem. The two unproved structural propositions remain explicit arguments. -/
def normalQuotientWithStructuralInputs
    (hCartier : AffineCartierSmoothStatement.{u})
    (hImage : AffineHomImageStatement.{u})
    {k : Type u} [Field k]
    {G N : GroupScheme (Spec (CommRingCat.of k))} (i : N ⟶ G)
    (ha : IsAffineHom G.X.hom) (hl : LocallyOfFiniteType G.X.hom)
    (hi : IsClosedSubgroup i) (hn : (SubgroupFunctor.range i).IsNormal) :
    Σ (Q : GroupScheme (Spec (CommRingCat.of k))), {q : G ⟶ Q //
      IsAffineHom Q.X.hom ∧ LocallyOfFiniteType Q.X.hom ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q} := by
  let h := normalQuotientExistence_with_structural_inputs hCartier hImage
    k G N i ha hl hi hn
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choose_spec (Classical.choose_spec h)⟩

end Langlands.GroupScheme
