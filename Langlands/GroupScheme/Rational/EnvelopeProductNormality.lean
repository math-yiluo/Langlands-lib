import Langlands.GroupScheme.Rational.SubgroupProductTransporter
import Langlands.GroupScheme.Rational.TorusSectionEnvelopeNormality
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Absolute.SolvableMaximalTorusSemidirectOfSection

/-! # Normality from an fpqc envelope-kernel and centralizer product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section UniversalLift

variable {S : Scheme.{u}} {G H N V C : GroupScheme S} {T : CommGroupScheme S}
    (h : H ⟶ G) [Mono h.hom.hom]
    (n : N ⟶ G) (j : V ⟶ N) (c : C ⟶ N) (t : T.toGrp ⟶ G)
    [Flat (subgroupMultiplication j c).left]
    [Surjective (subgroupMultiplication j c).left]
    [QuasiCompact (subgroupMultiplication j c).left]
    (hj : SubgroupFunctor.range (j ≫ n) ≤ SubgroupFunctor.range h)
    (ht : SubgroupFunctor.range t ≤ SubgroupFunctor.range h)
    (hc : SubgroupFunctor.range (c ≫ n) ≤ torusCentralizer t)

/-- The unique actual factorization of universal subgroup conjugation
through the represented target subgroup, obtained by fpqc descent. -/
def subgroupProductConjugationLift : N.X ⊗ T.X ⟶ H.X :=
  Classical.choose (SubgroupFunctor.mem_range.mp
    (conj_mem_of_fpqc_subgroupProduct h n j c t hj ht hc (N.X ⊗ T.X)
      (fst N.X T.X) (snd N.X T.X ≫ t.hom.hom)
      (SubgroupFunctor.mem_range.mpr ⟨snd N.X T.X, rfl⟩)))

/-- The factorization recovers the original conjugation morphism exactly. -/
theorem subgroupProductConjugationLift_comp :
    subgroupProductConjugationLift h n j c t hj ht hc ≫ h.hom.hom =
      subgroupConjugation n t :=
  Classical.choose_spec (SubgroupFunctor.mem_range.mp
    (conj_mem_of_fpqc_subgroupProduct h n j c t hj ht hc (N.X ⊗ T.X)
      (fst N.X T.X) (snd N.X T.X ≫ t.hom.hom)
      (SubgroupFunctor.mem_range.mpr ⟨snd N.X T.X, rfl⟩)))

end UniversalLift

namespace TorusGeneratedEnvelope

variable {k : Type u} [Field k]
    {G N V C : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (D : TorusGeneratedEnvelope G)

/-- A sectioned split-unipotent quotient and an fpqc product of an
envelope-contained subgroup with the section's centralizer imply full
envelope normality. Stable-vector existence remains explicit. -/
theorem isNormal_of_fpqc_envelopeKernelProduct
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (n : N ⟶ G) (hn : IsClosedSubgroup n)
    [Smooth N.X.hom] [IsAffineHom N.X.hom] [ConnectedSpace N.X.left]
    (hN : IsUnipotent N) (hNsplit : RelativeRoot.IsSplitUnipotent N)
    (q : G ⟶ T.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (s : T.toGrp ⟶ G) (hs : s ≫ q = 𝟙 T.toGrp) (hT : IsTorus T.toGrp)
    (j : V ⟶ N) (c : C ⟶ N)
    [Flat (subgroupMultiplication j c).left]
    [Surjective (subgroupMultiplication j c).left]
    [QuasiCompact (subgroupMultiplication j c).left]
    (hj : SubgroupFunctor.range (j ≫ n) ≤ SubgroupFunctor.range D.inclusion)
    (hc : SubgroupFunctor.range (c ≫ n) ≤ torusCentralizer s) :
    (SubgroupFunctor.range D.inclusion).IsNormal := by
  let : Mono D.inclusion.hom.hom := D.represents.1
  let : IsClosedImmersion n.hom.hom.left := hn
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  let : IsIso (s ≫ q) := by rw [hs]; infer_instance
  let : IsIso (subgroupMultiplication s n) :=
    isIso_subgroupMultiplication_of_isIso_comp inferInstance hq.2.2.2
  have hsc : IsClosedSubgroup s := IsClosedSubgroup.of_comp_eq_id s q hs
  have hsin : SubgroupFunctor.range s ≤ SubgroupFunctor.range D.inclusion := by
    rw [D.represents.2]
    exact closedTorusEnvelope_containsTori G T s hT hsc
  apply D.isNormal_of_section_conjugates hstable n hn hN hNsplit q hq s hs
  intro R g x hx
  rw [← D.represents.2]
  let a := leviComponent s n g
  let b := radicalComponent s n g
  have ha : a ≫ s.hom.hom ∈ (SubgroupFunctor.range D.inclusion).carrier R :=
    hsin R (SubgroupFunctor.mem_range.mpr ⟨a, rfl⟩)
  have hb : (b ≫ n.hom.hom) * x * (b ≫ n.hom.hom)⁻¹ ∈
      (SubgroupFunctor.range D.inclusion).carrier R :=
    conj_mem_of_fpqc_subgroupProduct D.inclusion n j c s hj hsin hc R b x hx
  have hg : (a ≫ s.hom.hom) * (b ≫ n.hom.hom) = g :=
    leviComponent_mul_radicalComponent s n g
  have heq : g * x * g⁻¹ =
      (a ≫ s.hom.hom) * ((b ≫ n.hom.hom) * x * (b ≫ n.hom.hom)⁻¹) *
        (a ≫ s.hom.hom)⁻¹ := by
    rw [← hg]
    group
  rw [heq]
  exact (SubgroupFunctor.range D.inclusion).carrier R |>.mul_mem
    ((SubgroupFunctor.range D.inclusion).carrier R |>.mul_mem ha hb)
    ((SubgroupFunctor.range D.inclusion).carrier R |>.inv_mem ha)

end TorusGeneratedEnvelope

end Langlands.GroupScheme
