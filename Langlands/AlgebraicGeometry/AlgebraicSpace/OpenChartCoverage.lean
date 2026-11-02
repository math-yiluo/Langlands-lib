import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorImages

/-! # Coverage by open scheme charts -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartCoverage

variable {S : Scheme.{u}} {F : Presheaf S}

private theorem map_universal_section {U T : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (f : T ⟶ U) :
    F.map f.op (uliftYonedaEquiv a) = a.app (op T) (ULift.up f) := by
  exact congrArg
    (fun n : (schemeYoneda S).obj U ⟶ F => n.app (op T) (ULift.up f))
    (uliftYonedaEquiv.symm_apply_apply a)

/-- A sieve covering the universal section of a locally surjective scheme
chart gives local surjectivity on the whole target. -/
theorem isLocallySurjective_of_covering_section
    {G : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (b : G ⟶ F)
    (ha : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) a)
    (hb : CategoryTheory.Presheaf.imageSieve b (uliftYonedaEquiv a) ∈
      fppfTopology S U) :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) b := by
  constructor
  intro T y
  apply (fppfTopology S).transitive (ha.imageSieve_mem y)
  intro R r hr
  obtain ⟨⟨z⟩, hz⟩ := hr
  rw [CategoryTheory.Presheaf.pullback_imageSieve, ← hz]
  have h := (fppfTopology S).pullback_stable z hb
  rw [CategoryTheory.Presheaf.pullback_imageSieve] at h
  rw [map_universal_section] at h
  exact h

/-- Open scheme charts which contain all residue-field values of a scheme
section locally cover that section. -/
theorem covering_section_of_residueField
    {U : Over S} (a : (schemeYoneda S).obj U ⟶ F)
    {I : Type u} {V : I → Over S}
    (b : ∀ i, (schemeYoneda S).obj (V i) ⟶ F)
    (hb : ∀ i, IsOpenImmersion (b i))
    (hcov : ∀ x : U.left, ∃ i,
      F.map (OpenSubfunctorPoints.residueFieldPoint U x).op (uliftYonedaEquiv a) ∈
        (Subfunctor.range (b i)).obj
          (op (OpenSubfunctorPoints.residueFieldTest U x))) :
    CategoryTheory.Presheaf.imageSieve (Sigma.desc b) (uliftYonedaEquiv a) ∈
      fppfTopology S U := by
  let R (i : I) := (hb i).rep.pullback a
  let q (i : I) : R i ⟶ U := (hb i).rep.snd a
  let r (i : I) : (schemeYoneda S).obj (R i) ⟶ (schemeYoneda S).obj (V i) :=
    (hb i).rep.fst a
  let : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (q i).left :=
    fun i => (hb i).property_snd a
  have hpoints : ∀ x : U.left, ∃ i z, (q i).left z = x := by
    intro x
    obtain ⟨i, z, hz⟩ := hcov x
    let f := OpenSubfunctorPoints.residueFieldPoint U x
    have hz' : (b i).app _ z = a.app _ (ULift.up f) := by
      rw [map_universal_section] at hz
      exact hz
    obtain ⟨w, _, hw⟩ := Types.exists_of_isPullback
      (((hb i).rep.isPullback a).app
        (op (OpenSubfunctorPoints.residueFieldTest U x))) z (ULift.up f) hz'
    have hw' : w.down ≫ q i = f := congrArg ULift.down hw
    refine ⟨i, w.down.left (default : Spec (U.left.residueField x)), ?_⟩
    change (w.down ≫ q i).left _ = x
    rw [hw']
    exact U.left.fromSpecResidueField_apply x _
  have hq : Sieve.ofArrows R q ∈ fppfTopology S U := by
    let 𝒰 := Scheme.Cover.mkOfCovers
      (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      I (fun i => (R i).left) (fun i => (q i).left) hpoints
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (Precoverage.toGrothendieck_mono
      Scheme.zariskiPrecoverage_le_fppfPrecoverage) _ 𝒰.mem_grothendieckTopology
  apply (fppfTopology S).superset_covering ?_ hq
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  refine ⟨(Sigma.ι (fun i => (schemeYoneda S).obj (V i)) i).app _
    (uliftYonedaEquiv (r i)), ?_⟩
  have hs := congrArg
    (fun n => n.app (op (R i)) (uliftYonedaEquiv (r i)))
    (Sigma.ι_comp_desc b i)
  refine hs.trans ?_
  rw [← uliftYonedaEquiv_comp, (hb i).rep.isPullback a |>.w]
  exact (uliftYonedaEquiv_naturality a (q i).op).symm

/-- Residue-field coverage on an etale surjective atlas gives the locally
surjective family required for gluing open scheme charts. -/
theorem isLocallySurjective_sigma_of_residueField
    {U : Over S} (a : (schemeYoneda S).obj U ⟶ F)
    (ha : IsEtale a) (hs : IsSurjective a)
    {I : Type u} {V : I → Over S}
    (b : ∀ i, (schemeYoneda S).obj (V i) ⟶ F)
    (hb : ∀ i, IsOpenImmersion (b i))
    (hcov : ∀ x : U.left, ∃ i,
      F.map (OpenSubfunctorPoints.residueFieldPoint U x).op (uliftYonedaEquiv a) ∈
        (Subfunctor.range (b i)).obj
          (op (OpenSubfunctorPoints.residueFieldTest U x))) :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) (Sigma.desc b) :=
  isLocallySurjective_of_covering_section a _
    (isLocallySurjective_of_isEtale_isSurjective a ha hs)
    (covering_section_of_residueField a b hb hcov)

end Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartCoverage
