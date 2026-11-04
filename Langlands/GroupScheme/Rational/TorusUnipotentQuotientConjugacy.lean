import Langlands.GroupScheme.Rational.TorusUnipotentLiftConjugacy
import Langlands.GroupScheme.Rational.QuotientConjugacyLift
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.GroupScheme.FieldSeparatedProof

/-! # Lifting rational torus conjugacy through split unipotent kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace HomogeneousQuotient

variable {k : Type u} [Field k]
    {N G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth N.X.hom]
    (n : N ⟶ G) (hn : IsClosedSubgroup n)
    (hNsplit : RelativeRoot.IsSplitUnipotent N)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)

include hn hNsplit hq

/-- Every affine test point lifts through an fppf quotient of an affine group
by a smooth closed split unipotent subgroup. No affineness of `Q` is needed. -/
theorem fppf_affine_lifts_of_split_unipotent
    (T : Over (Spec (CommRingCat.of k))) [IsAffine T.left] (x : T ⟶ Q.X) :
    ∃ g : T ⟶ G.X, g ≫ q.hom.hom = x := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom N.X.hom := affine_subgroup_of_closed G N n hn
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : IsSeparated Q.X.hom := fieldSeparated k Q
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  exact affine_lifts_of_split_unipotent_torsors G N n q.hom.hom
    (hq.fibers_iff ⟨inferInstance, rfl⟩)
    splitUnipotentAffineTorsorStatement hNsplit T x

/-- A chosen rational lift through a represented split unipotent quotient. -/
def splitUnipotentRationalLift
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q.X) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := by
  let : IsAffine (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  exact Classical.choose (fppf_affine_lifts_of_split_unipotent n hn hNsplit q hq _ x)

/-- The chosen lift projects to the original specified quotient point. -/
theorem splitUnipotentRationalLift_comp
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q.X) :
    splitUnipotentRationalLift n hn hNsplit q hq x ≫ q.hom.hom = x := by
  let : IsAffine (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  exact Classical.choose_spec (fppf_affine_lifts_of_split_unipotent n hn hNsplit q hq _ x)

end HomogeneousQuotient

namespace QuotientConjugacyLift

section SuppliedLift

variable
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hlinear : RelativeRoot.TorusVectorActionLinearizationStatement.{u})
    {k : Type u} [Field k]
    {H H' N G Q : GroupScheme (Spec (CommRingCat.of k))}
    (n : N ⟶ G) (q : G ⟶ Q)
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    [Mono n.hom.hom] [Smooth N.X.hom] [IsAffineHom N.X.hom]
    [ConnectedSpace N.X.left]
    (hN : IsUnipotent N) (hNsplit : RelativeRoot.IsSplitUnipotent N)
    (i : H ⟶ G) (i' : H' ⟶ G) (f : H ≅ H') (hH : IsTorus H)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q.X)
    (hx : (i ≫ q) ≫ (Q.innerIso x).hom = f.hom ≫ (i' ≫ q))
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : g ≫ q.hom.hom = x)

/-- A rational kernel correction for a supplied lift of a quotient conjugator.
The affine torsor input is discharged by its published proof. -/
def splitUnipotentKernelCorrection :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ N.X :=
  QuotientHomCocycle.splitUnipotentTorusConjugator
    hstable hlinear splitUnipotentAffineTorsorStatement n q hn hN hNsplit i
    ((f.hom ≫ i') ≫ (G.innerIso g⁻¹).hom)
    (quotient_eq q i i' f x hx g hg) hH

/-- Correcting the supplied quotient lift gives an actual rational conjugator. -/
def splitUnipotentConjugator :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X :=
  g * (splitUnipotentKernelCorrection hstable hlinear
    n q hn hN hNsplit i i' f hH x hx g hg ≫ n.hom.hom)

/-- The correction preserves the specified image in the quotient. -/
theorem splitUnipotentConjugator_comp :
    splitUnipotentConjugator hstable hlinear
      n q hn hN hNsplit i i' f hH x hx g hg ≫ q.hom.hom = x := by
  have hv := QuotientHomCocycle.splitUnipotentTorusConjugator_mem_kernel
    hstable hlinear splitUnipotentAffineTorsorStatement n q hn hN hNsplit i
    ((f.hom ≫ i') ≫ (G.innerIso g⁻¹).hom)
    (quotient_eq q i i' f x hx g hg) hH
  rw [mem_range_kernelι_iff] at hv
  rw [splitUnipotentConjugator, MonObj.mul_comp,
    splitUnipotentKernelCorrection, hv, mul_one, hg]

/-- Conjugation uses exactly the supplied source isomorphism. -/
theorem splitUnipotentConjugator_conjugates :
    i ≫ (G.innerIso (splitUnipotentConjugator hstable hlinear
      n q hn hN hNsplit i i' f hH x hx g hg)).hom = f.hom ≫ i' := by
  rw [splitUnipotentConjugator, innerIso_mul_hom, ← Category.assoc]
  have hv := QuotientHomCocycle.splitUnipotentTorusConjugator_conjugates
    hstable hlinear splitUnipotentAffineTorsorStatement n q hn hN hNsplit i
    ((f.hom ≫ i') ≫ (G.innerIso g⁻¹).hom)
    (quotient_eq q i i' f x hx g hg) hH
  change (i ≫ (G.innerIso
    (QuotientHomCocycle.splitUnipotentTorusConjugator
      hstable hlinear splitUnipotentAffineTorsorStatement n q hn hN hNsplit i
      ((f.hom ≫ i') ≫ (G.innerIso g⁻¹).hom)
      (quotient_eq q i i' f x hx g hg) hH ≫ n.hom.hom)).hom) ≫
        (G.innerIso g).hom = f.hom ≫ i'
  rw [hv, innerIso_inv_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SuppliedLift

section Fppf

variable
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hlinear : RelativeRoot.TorusVectorActionLinearizationStatement.{u})
    {k : Type u} [Field k]
    {H H' N G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (n : N ⟶ G) (hn : IsClosedSubgroup n)
    (hN : IsUnipotent N) (hNsplit : RelativeRoot.IsSplitUnipotent N)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (i : H ⟶ G) (i' : H' ⟶ G) (f : H ≅ H') (hH : IsTorus H)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q.X)
    (hx : (i ≫ q) ≫ (Q.innerIso x).hom = f.hom ≫ (i' ≫ q))

/-- An actual rational conjugator lifting a specified quotient conjugator
through a represented smooth connected split unipotent kernel. -/
def fppfSplitUnipotentConjugator :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom N.X.hom := HomogeneousQuotient.affine_subgroup_of_closed G N n hn
  exact splitUnipotentConjugator hstable hlinear n q hq.2.2.2.symm hN hNsplit
    i i' f hH x hx
    (HomogeneousQuotient.splitUnipotentRationalLift n hn hNsplit q hq x)
    (HomogeneousQuotient.splitUnipotentRationalLift_comp n hn hNsplit q hq x)

/-- The actual conjugator projects to precisely the specified quotient point. -/
theorem fppfSplitUnipotentConjugator_comp :
    fppfSplitUnipotentConjugator hstable hlinear n hn hN hNsplit q hq
      i i' f hH x hx ≫ q.hom.hom = x := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom N.X.hom := HomogeneousQuotient.affine_subgroup_of_closed G N n hn
  exact splitUnipotentConjugator_comp hstable hlinear n q hq.2.2.2.symm hN hNsplit
    i i' f hH x hx
    (HomogeneousQuotient.splitUnipotentRationalLift n hn hNsplit q hq x)
    (HomogeneousQuotient.splitUnipotentRationalLift_comp n hn hNsplit q hq x)

/-- The lifted conjugator preserves the source isomorphism of the supplied
quotient conjugacy, without any injectivity condition on either torus map. -/
theorem fppfSplitUnipotentConjugator_conjugates :
    i ≫ (G.innerIso (fppfSplitUnipotentConjugator hstable hlinear
      n hn hN hNsplit q hq i i' f hH x hx)).hom = f.hom ≫ i' := by
  let : IsClosedImmersion n.hom.hom.left := hn
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom N.X.hom := HomogeneousQuotient.affine_subgroup_of_closed G N n hn
  exact splitUnipotentConjugator_conjugates hstable hlinear
    n q hq.2.2.2.symm hN hNsplit i i' f hH x hx
    (HomogeneousQuotient.splitUnipotentRationalLift n hn hNsplit q hq x)
    (HomogeneousQuotient.splitUnipotentRationalLift_comp n hn hNsplit q hq x)

end Fppf

end QuotientConjugacyLift

section FppfConjugacy

variable
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hlinear : RelativeRoot.TorusVectorActionLinearizationStatement.{u})
    {k : Type u} [Field k]
    {H H' N G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (n : N ⟶ G) (hn : IsClosedSubgroup n)
    (hN : IsUnipotent N) (hNsplit : RelativeRoot.IsSplitUnipotent N)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (i : H ⟶ G) (i' : H' ⟶ G) (hH : IsTorus H)

include hstable hlinear hn hN hNsplit hq hH

/-- Rational subgroup conjugacy is equivalent to conjugacy in the represented
quotient, conditional only on stable-vector existence and torus linearization. -/
theorem subgroupConjugate_iff_quotient_of_isTorus_fppf_split_unipotent_kernel :
    SubgroupConjugate i i' ↔ SubgroupConjugate (i ≫ q) (i' ≫ q) := by
  constructor
  · exact fun h => h.postcomp q
  · rintro ⟨x, f, hx⟩
    exact ⟨QuotientConjugacyLift.fppfSplitUnipotentConjugator
        hstable hlinear n hn hN hNsplit q hq i i' f hH x hx, f,
      QuotientConjugacyLift.fppfSplitUnipotentConjugator_conjugates
        hstable hlinear n hn hN hNsplit q hq i i' f hH x hx⟩

end FppfConjugacy

end Langlands.GroupScheme
