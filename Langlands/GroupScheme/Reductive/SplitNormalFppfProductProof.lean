import Langlands.GroupScheme.Reductive.SplitNormalFppfProductStatement
import Langlands.GroupScheme.Reductive.FppfProductUnipotent
import Langlands.GroupScheme.Rational.SplitSemidirectSeries
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.HomImage

/-! # Split unipotence of represented products of split normal closed subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitNormalFppfProduct

/-- The image interface of the splitness induction holds over every field. -/
theorem homImageHypothesis (k : Type u) [Field k] :
    RelativeRoot.SplitSemidirect.HomImageHypothesis k := by
  intro A G φ hA hAc hAa hG hGa
  have : Smooth G.X.hom := hG
  obtain ⟨D, inc, fac, hinc, hfac, hfl, hsu, hqc, -, hDs, hDc, hDa⟩ :=
    smoothConnectedHomImage k A G φ hA hAc hAa inferInstance hGa
  exact ⟨D, inc, fac, hinc, hfac, hfl, hsu, hqc, hDs, hDc, hDa⟩

variable {S : Scheme.{u}} {G P N H : GroupScheme S}

/-- If `p : P ⟶ G` represents the fppf-local product of `range i` and `range j`, with
`i = i' ≫ p`, `j = j' ≫ p` and `range j'` normal in `P`, then the morphism
`(n, h) ↦ j' n * i' h` from `N × H` to `P` is surjective. -/
theorem surjective_mulPoints {i : H ⟶ G} {j : N ⟶ G} {p : P ⟶ G} [Mono p.hom.hom]
    (hp : SubgroupFunctor.IsFppfProduct (SubgroupFunctor.range i)
      (SubgroupFunctor.range j) p)
    (i' : H ⟶ P) (j' : N ⟶ P) (hi' : i' ≫ p = i) (hj' : j' ≫ p = j)
    (hn : (SubgroupFunctor.range j').IsNormal) :
    Surjective (RelativeRoot.SplitSemidirect.mulPoints j' i').left := by
  obtain ⟨V, v, -, hvs, -, a, b, ha, hb, hab⟩ :=
    (hp.mem_range_iff P.X p.hom.hom).1
      (SubgroupFunctor.mem_range.2 ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨a', rfl⟩ := SubgroupFunctor.mem_range.1 ha
  obtain ⟨b', rfl⟩ := SubgroupFunctor.mem_range.1 hb
  have hv : v = (a' ≫ i'.hom.hom) * (b' ≫ j'.hom.hom) := by
    apply (cancel_mono p.hom.hom).1
    rw [hab, MonObj.mul_comp, Category.assoc, Category.assoc, ← Grp.comp_hom_hom,
      ← Grp.comp_hom_hom, hi', hj']
  obtain ⟨c, hc⟩ := SubgroupFunctor.mem_range.1
    (hn V (a' ≫ i'.hom.hom) (b' ≫ j'.hom.hom) (Subgroup.mem_top _)
      (SubgroupFunctor.mem_range.2 ⟨b', rfl⟩))
  have hv' : v = lift c a' ≫ RelativeRoot.SplitSemidirect.mulPoints j' i' := by
    rw [RelativeRoot.SplitSemidirect.mulPoints, MonObj.comp_mul, lift_fst_assoc,
      lift_snd_assoc, hc, inv_mul_cancel_right, hv]
  have : Surjective (lift c a' ≫ RelativeRoot.SplitSemidirect.mulPoints j' i').left := by
    rw [← hv']; exact hvs
  rw [Over.comp_left] at this
  exact Surjective.of_comp (lift c a').left _

/-- `SplitNormalFppfProductStatement`: a smooth connected represented fppf product of two
split smooth connected normal closed subgroups of an affine locally finite-type group over a
field is split unipotent. -/
theorem splitNormalFppfProduct : SplitNormalFppfProductStatement.{u} := by
  intro k _ G hGa _ H N i j hi hHs hHc _ hHsp hj hNs hNc hNn hNsp P p hp hPs _
  have hpc : IsClosedSubgroup p := hp.isClosedSubgroup
  have : IsClosedImmersion p.hom.hom.left := hpc
  have : Mono p.hom.hom := Over.mono_of_mono_left _
  have hrep : (SubgroupFunctor.range p).IsRepresentedBy p := ⟨inferInstance, rfl⟩
  let i' : H ⟶ P := hrep.factorHom i hp.left_le
  let j' : N ⟶ P := hrep.factorHom j hp.right_le
  have hi' : i' ≫ p = i := hrep.factorHom_comp i hp.left_le
  have hj' : j' ≫ p = j := hrep.factorHom_comp j hp.right_le
  have hj'c : IsClosedSubgroup j' := IsClosedSubgroup.of_comp hpc (by rw [hj']; exact hj)
  have hn' : (SubgroupFunctor.range j').IsNormal :=
    SubgroupFunctor.isNormal_range_of_mono_comp j' p (by rw [hj']; exact hNn)
  have : IsAffineHom G.X.hom := hGa
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom P.X.hom := by
    rw [← Over.w p.hom.hom]; infer_instance
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]; infer_instance
  have : Smooth P.X.hom := hPs
  have : Smooth H.X.hom := hHs
  have : Smooth N.X.hom := hNs
  have : ConnectedSpace H.X.left := hHc
  have : ConnectedSpace N.X.left := hNc
  obtain ⟨n, hn⟩ := hHsp
  exact RelativeRoot.SplitSemidirect.isSplitUnipotent_of_surjective (homImageHypothesis k) n
    j' i' hj'c hn' hNsp hn (surjective_mulPoints hp i' j' hi' hj' hn')

end Langlands.GroupScheme.SplitNormalFppfProduct
