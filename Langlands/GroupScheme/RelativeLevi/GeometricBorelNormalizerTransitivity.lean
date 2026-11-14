import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof
import Langlands.GroupScheme.Absolute.BorelNormalizerTorus
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Normalizer conjugacy of geometric Borel subgroups containing a maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G B B' : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Correct a conjugacy of two overgroups containing the same maximal torus to a
conjugacy by a point normalizing that torus. -/
theorem exists_normalizerPoints_conjugatingIso_of_overgroupIso
    (i : B ⟶ G) (i' : B' ⟶ G) (f : T.toGrp ⟶ B) (f' : T.toGrp ⟶ B')
    (hfactor : f ≫ i = f' ≫ i') (hf : IsMaximalTorus f) (hf' : IsMaximalTorus f')
    (hconj : MaximalToriAreConjugate B')
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (e : B ≅ B') (he : i ≫ (G.innerIso g).hom = e.hom ≫ i') :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      n ∈ normalizerPoints (f ≫ i) ∧
        ∃ φ : B ≅ B', i ≫ (G.innerIso n).hom = φ.hom ≫ i' := by
  obtain ⟨p, a, ha⟩ := hconj T T (f ≫ e.hom) f' (hf.comp_iso e) hf'
  let n := (p ≫ i'.hom.hom) * g
  have hn : (f ≫ i) ≫ (G.innerIso n).hom = a.hom ≫ (f ≫ i) := by
    calc
      _ = ((f ≫ e.hom) ≫ (B'.innerIso p).hom) ≫ i' := by
        rw [innerIso_mul_hom]
        simp only [Category.assoc]
        rw [reassoc_of% he, innerIso_hom_comp i' p]
      _ = (a.hom ≫ f') ≫ i' := by rw [ha]
      _ = a.hom ≫ (f ≫ i) := by rw [Category.assoc, ← hfactor]
  let σ : T ≅ T :=
    { hom := Additive.ofMul a.hom
      inv := Additive.ofMul a.inv
      hom_inv_id := congrArg Additive.ofMul a.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul a.inv_hom_id }
  refine ⟨n, ⟨σ, hn⟩, e ≪≫ B'.innerIso p, ?_⟩
  change i ≫ (G.innerIso ((p ≫ i'.hom.hom) * g)).hom =
    (e.hom ≫ (B'.innerIso p).hom) ≫ i'
  rw [innerIso_mul_hom]
  simp only [Category.assoc]
  rw [reassoc_of% he, innerIso_hom_comp i' p]

variable [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom]
  [ConnectedSpace G.X.left]

/-- Any two Borel subgroups over an algebraically closed field containing a fixed
maximal torus are conjugate by a point in the full normalizer subgroup functor. -/
theorem IsBorelSubgroup.exists_normalizer_conjugatingIso
    {i : B ⟶ G} {i' : B' ⟶ G} (hi : IsBorelSubgroup i) (hi' : IsBorelSubgroup i')
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hti' : SubgroupFunctor.range t ≤ SubgroupFunctor.range i') :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      n ∈ (SubgroupFunctor.range t).normalizer.carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ∧
      ∃ φ : B ≅ B', i ≫ (G.innerIso n).hom = φ.hom ≫ i' := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion i'.hom.hom.left := hi'.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  let hiRep : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hi'Rep : (SubgroupFunctor.range i').IsRepresentedBy i' := ⟨inferInstance, rfl⟩
  let f := hiRep.factorHom t hti
  let f' := hi'Rep.factorHom t hti'
  have hfi : f ≫ i = t := hiRep.factorHom_comp t hti
  have hfi' : f' ≫ i' = t := hi'Rep.factorHom_comp t hti'
  have hf : IsMaximalTorus f := IsMaximalTorus.of_comp hi.isClosedSubgroup (by rwa [hfi])
  have hf' : IsMaximalTorus f' := IsMaximalTorus.of_comp hi'.isClosedSubgroup (by rwa [hfi'])
  have := hi'.smooth
  have := hi'.connectedSpace
  have : IsAffineHom B'.X.hom := by
    rw [← Over.w i'.hom.hom]
    infer_instance
  have hconj : MaximalToriAreConjugate B' :=
    solvableMaximalTorusConjugacy k B' hi'.isSolvableGroupScheme
  obtain ⟨g, e, he⟩ := (borelConjugacy k G).2 B B' i i' hi hi'
  obtain ⟨n, hn, φ, hφ⟩ := exists_normalizerPoints_conjugatingIso_of_overgroupIso
    i i' f f' (hfi.trans hfi'.symm) hf hf' hconj g e he
  rw [hfi] at hn
  exact ⟨n, normalizerPoints_le_torusNormalizer t hn, φ, hφ⟩

/-- The same normalizer transitivity expressed as equality of subgroup functors. -/
theorem IsBorelSubgroup.exists_normalizer_range_conjugacy
    {i : B ⟶ G} {i' : B' ⟶ G} (hi : IsBorelSubgroup i) (hi' : IsBorelSubgroup i')
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hti' : SubgroupFunctor.range t ≤ SubgroupFunctor.range i') :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      n ∈ (SubgroupFunctor.range t).normalizer.carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ∧
      SubgroupFunctor.range (i ≫ (G.innerIso n).hom) = SubgroupFunctor.range i' := by
  obtain ⟨n, hn, φ, hφ⟩ := hi.exists_normalizer_conjugatingIso hi' t ht hti hti'
  exact ⟨n, hn, by rw [hφ, SubgroupFunctor.range_iso_comp]⟩

/-- Choose an actual normalizer point conjugating the two geometric Borels,
retaining both the full normalizer condition and the equality of ranges. -/
def IsBorelSubgroup.normalizerConjugacy
    {i : B ⟶ G} {i' : B' ⟶ G} (hi : IsBorelSubgroup i) (hi' : IsBorelSubgroup i')
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hti' : SubgroupFunctor.range t ≤ SubgroupFunctor.range i') :
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X //
      n ∈ (SubgroupFunctor.range t).normalizer.carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ∧
      SubgroupFunctor.range (i ≫ (G.innerIso n).hom) = SubgroupFunctor.range i'} :=
  let h := hi.exists_normalizer_range_conjugacy hi' t ht hti hti'
  ⟨h.choose, h.choose_spec⟩

end Langlands.GroupScheme
