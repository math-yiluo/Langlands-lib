import Langlands.GroupScheme.HomScheme.SmoothTorusSubgroupRepresentabilityProof
import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf
import Langlands.GroupScheme.Descent.SemilinearDatum
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.CommutativeAlgebra.HenselianSections

/-! # Lifting prescribed residue torus subgroups over Henselian local rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace TorusSubgroupModuli

/-- Evaluating a family over the identity base is the ordinary pullback of
its inclusion into the original ambient group. -/
theorem familyHom_over_identity {S S' : Scheme.{u}} {G : GroupScheme S}
    {K : GroupScheme S}
    (j : K ⟶ (baseChange (𝟙 S)).obj G) (c : S' ⟶ S) :
    familyHom j (show Over.mk c ⟶ Over.mk (𝟙 S) from
      Over.homMk c (Category.comp_id _)) =
      (baseChange c).map (j ≫ (baseChangeIdIso G).hom) := by
  simp only [familyHom, Functor.map_comp]
  congr 1
  exact congrArg (fun e => e.hom) (Descent.baseChangeIdIso_comparison c G).symm

end TorusSubgroupModuli

namespace HenselianTorusLifting

variable {R k : Type u} [CommRing R] [HenselianLocalRing R] [Field k] [Algebra R k]

/-- An actual closed relative torus lifting a supplied residue torus, with
the exact residue inclusion recovered through an actual source isomorphism. -/
structure LiftData (G : GroupScheme (Spec (CommRingCat.of R)))
    {T₀ : GroupScheme (Spec (CommRingCat.of k))}
    (i₀ : T₀ ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj G) where
  torus : GroupScheme (Spec (CommRingCat.of R))
  inclusion : torus ⟶ G
  closed : IsClosedSubgroup inclusion
  relativeTorus : RelativeTorus.IsTorus torus
  residueIso :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj torus ≅ T₀
  residue_comm :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R k)))).map inclusion =
      residueIso.hom ≫ i₀

/-- Smooth moduli of actual torus subgroups and a pointed Henselian section
lift every closed residue relative torus, including nonsplit tori. -/
theorem nonempty_liftData
    (hk : Function.Surjective (algebraMap R k))
    (G : GroupScheme (Spec (CommRingCat.of R)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {T₀ : GroupScheme (Spec (CommRingCat.of k))}
    (i₀ : T₀ ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj G)
    (hi₀ : IsClosedSubgroup i₀) (hT₀ : RelativeTorus.IsTorus T₀) :
    Nonempty (LiftData G i₀) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap R k))
  obtain ⟨M, K, j, hj, hK, hu, hM⟩ :=
    TorusSubgroupModuli.smoothTorusSubgroupRepresentability
      (Spec (CommRingCat.of R)) G
  obtain ⟨a, ha, -⟩ := hu (Over.mk c) (SubgroupFunctor.range i₀)
    (TorusSubgroupModuli.isAdmissible_range i₀ hi₀ hT₀)
  let : Smooth M.hom := hM
  obtain ⟨σ, hσ, hσa⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
      hk M.hom a.left (Over.w a)
  let s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ M := Over.homMk σ hσ
  let b : Over.mk c ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
    Over.homMk c (Category.comp_id _)
  let I : (baseChange σ).obj K ⟶ G :=
    TorusSubgroupModuli.familyHom j s ≫ (baseChangeIdIso G).hom
  have hI : IsClosedSubgroup I :=
    (TorusSubgroupModuli.isClosedSubgroup_familyHom j hj s).comp_iso
      (baseChangeIdIso G)
  have hbs : b ≫ s = a := Over.OverMorphism.ext hσa
  have hres : SubgroupFunctor.range ((baseChange c).map I) =
      SubgroupFunctor.range i₀ := by
    calc
      _ = TorusSubgroupModuli.evaluate
          (TorusSubgroupModuli.familyHom j s) b := by
        rw [TorusSubgroupModuli.evaluate,
          TorusSubgroupModuli.familyHom_over_identity]
      _ = TorusSubgroupModuli.evaluate j (b ≫ s) :=
        TorusSubgroupModuli.evaluate_comp j s b
      _ = SubgroupFunctor.range i₀ := by rw [hbs]; exact ha
  let e := (hI.baseChange c).sourceIsoOfRangeEq hi₀ hres
  exact ⟨⟨(baseChange σ).obj K, I, hI, hK.baseChange σ, e,
    ((hI.baseChange c).sourceIsoOfRangeEq_hom_comp hi₀ hres).symm⟩⟩

/-- Choose a closed lift of a prescribed residue relative torus, retaining
the exact residue inclusion. -/
def liftData
    (hk : Function.Surjective (algebraMap R k))
    (G : GroupScheme (Spec (CommRingCat.of R)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {T₀ : GroupScheme (Spec (CommRingCat.of k))}
    (i₀ : T₀ ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj G)
    (hi₀ : IsClosedSubgroup i₀) (hT₀ : RelativeTorus.IsTorus T₀) :
    LiftData G i₀ :=
  Classical.choice (nonempty_liftData hk G i₀ hi₀ hT₀)

end HenselianTorusLifting

end Langlands.GroupScheme
