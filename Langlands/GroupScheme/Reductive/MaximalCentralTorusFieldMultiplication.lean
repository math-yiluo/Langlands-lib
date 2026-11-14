import Langlands.GroupScheme.Reductive.MaximalCentralTorus
import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Reductive.CommutingMultiplicationKernelProjection
import Langlands.GroupScheme.Torus.RelativeFieldComparison

/-! # Field multiplication by a maximal central relative torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Enlarging both factors of an actual subgroup product preserves its
surjectivity on underlying scheme points. -/
theorem surjective_subgroupMultiplication_of_factors
    {S : Scheme.{u}} {H K H' K' G : GroupScheme S}
    (j : H ⟶ G) (i : K ⟶ G) (j' : H' ⟶ G) (i' : K' ⟶ G)
    (f : H' ⟶ H) (g : K' ⟶ K) (hf : f ≫ j = j') (hg : g ≫ i = i')
    (hs : Function.Surjective (subgroupMultiplication j' i').left) :
    Surjective (subgroupMultiplication j i).left := by
  let a : H'.X ⊗ K'.X ⟶ H.X ⊗ K.X := f.hom.hom ⊗ₘ g.hom.hom
  have he : a ≫ subgroupMultiplication j i = subgroupMultiplication j' i' := by
    simp only [a, subgroupMultiplication, MonObj.comp_mul, tensorHom_fst_assoc,
      tensorHom_snd_assoc, ← Grp.comp_hom_hom, hf, hg]
  refine ⟨?_⟩
  intro x
  obtain ⟨y, hy⟩ := hs x
  refine ⟨a.left y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, he]
  exact hy

/-- A maximal central relative torus multiplies surjectively with every closed
subgroup containing the derived subgroup of a connected reductive field group. -/
theorem IsMaximalCentralRelativeTorus.surjective_subgroupMultiplication
    {k : Type u} [Field k]
    {G D Z : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hcomm : (SubgroupFunctor.range d).ContainsCommutators)
    {z : Z ⟶ G} (hz : IsMaximalCentralRelativeTorus z) :
    Surjective (subgroupMultiplication z d).left := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨E, e, _, _, he⟩ := derivedSubgroupRepresentability k G
  obtain ⟨Z₀, z₀, _, _, hZ₀, hz₀cl, hz₀c, hs⟩ :=
    reductiveCentralTorusSurjectivity k G E e hG he
  have : IsClosedImmersion z.hom.hom.left := hz.1
  have : IsClosedImmersion d.hom.hom.left := hd
  have hzr : (SubgroupFunctor.range z).IsRepresentedBy z :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hdr : (SubgroupFunctor.range d).IsRepresentedBy d :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hzle := hz.2.2.2 Z₀.toGrp z₀ hz₀cl hz₀c hZ₀.isRelativeTorus
  have hele := he.range_le d hd hcomm
  exact surjective_subgroupMultiplication_of_factors z d z₀ e
    (hzr.factorHom z₀ hzle) (hdr.factorHom e hele)
    (hzr.factorHom_comp _ _) (hdr.factorHom_comp _ _) hs

/-- Finiteness of the full centre of the second factor upgrades this field
multiplication to a central isogeny. -/
theorem IsMaximalCentralRelativeTorus.isCentralIsogeny_commutingMultiplication
    {k : Type u} [Field k]
    {G D Z : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hcomm : (SubgroupFunctor.range d).ContainsCommutators) (hD : HasFiniteCenter D)
    {z : Z ⟶ G} (hz : IsMaximalCentralRelativeTorus z) :
    IsCentralIsogeny (commutingSubgroupMultiplicationHom z d (hz.2.1.commute_values d)) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have : IsClosedImmersion d.hom.hom.left := hd
  have : Mono d.hom.hom := Over.mono_of_mono_left _
  exact isCentralIsogeny_commutingSubgroupMultiplicationHom_of_finite_kernel
    z d hz.1 hd (hz.2.1.commute_values d)
    (hz.surjective_subgroupMultiplication hG d hd hcomm)
    (kernel_commutingSubgroupMultiplicationHom_isFinite_of_right_finiteCenter
      z d (hz.2.1.commute_values d) hz.1 hD)

/-- The two field conclusions, with precisely their respective hypotheses. -/
def MaximalCentralTorusFieldMultiplicationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G D Z : GroupScheme (Spec (CommRingCat.of k)))
    (d : D ⟶ G) (z : Z ⟶ G), IsConnectedReductive G → IsClosedSubgroup d →
    (SubgroupFunctor.range d).ContainsCommutators →
    ∀ hz : IsMaximalCentralRelativeTorus z,
      Surjective (subgroupMultiplication z d).left ∧
        (HasFiniteCenter D → IsCentralIsogeny
          (commutingSubgroupMultiplicationHom z d (hz.2.1.commute_values d)))

/-- The field conclusions follow from the published surjectivity theorem and
one-factor kernel finiteness. -/
theorem maximalCentralTorusFieldMultiplication :
    MaximalCentralTorusFieldMultiplicationStatement.{u} := by
  intro k _ G D Z d z hG hd hcomm hz
  exact ⟨hz.surjective_subgroupMultiplication hG d hd hcomm,
    fun hD => hz.isCentralIsogeny_commutingMultiplication hG d hd hcomm hD⟩

end Langlands.GroupScheme
