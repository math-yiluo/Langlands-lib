import Langlands.GroupScheme.Rational.TorusNormalizerRigidity
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Connected groups normalizing a split torus centralize it -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {G K : GroupScheme S} {T : CommGroupScheme S}

/-- The image of a connected group normalizing a monic split torus centralizes
that torus on every test scheme. -/
theorem range_le_torusCentralizer_of_connected_of_isNormalizedBy
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (hT : IsSplitTorus T.toGrp)
    (j : K ⟶ G) [ConnectedSpace K.X.left]
    (hn : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range j)) :
    SubgroupFunctor.range j ≤ torusCentralizer i := by
  have hj : j.hom.hom ∈ (torusNormalizer i).carrier K.X := by
    intro V a x hx
    have ha : a ≫ j.hom.hom ∈ (SubgroupFunctor.range j).carrier V := ⟨a, rfl⟩
    have hai := ((SubgroupFunctor.range j).carrier V).inv_mem ha
    exact ⟨hn V _ x ha hx, by
      simpa only [inv_inv] using hn V _ x hai hx⟩
  obtain ⟨σ, hσ⟩ := TorusConjugation.exists_isNormalizingAut_of_connected hT hj
  have hfix (V : Over S) (t : V ⟶ T.X) :
      (t ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) ≫ i.hom.hom =
        t ≫ i.hom.hom := by
    have h := hσ V (1 : V ⟶ K.X) t
    rw [MonObj.one_comp] at h
    simpa only [one_mul, inv_one, mul_one] using h.symm
  intro V x hx
  obtain ⟨g, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  intro W a t
  have h := hσ W (a ≫ g) t
  rw [hfix] at h
  rw [Category.assoc] at h
  exact mul_inv_eq_iff_eq_mul.mp h

/-- The actual factor of a connected normalizing group through any
representative of the split torus centralizer. -/
def connectedNormalizerCentralizerFactor
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (hT : IsSplitTorus T.toGrp)
    (j : K ⟶ G) [ConnectedSpace K.X.left]
    (hn : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range j))
    {C : GroupScheme S} {c : C ⟶ G}
    (hc : (torusCentralizer i).IsRepresentedBy c) : K ⟶ C :=
  hc.factorHom j (range_le_torusCentralizer_of_connected_of_isNormalizedBy i hT j hn)

theorem connectedNormalizerCentralizerFactor_comp
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (hT : IsSplitTorus T.toGrp)
    (j : K ⟶ G) [ConnectedSpace K.X.left]
    (hn : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range j))
    {C : GroupScheme S} {c : C ⟶ G}
    (hc : (torusCentralizer i).IsRepresentedBy c) :
    connectedNormalizerCentralizerFactor i hT j hn hc ≫ c = j :=
  hc.factorHom_comp j _

/-- A normal monic split torus in a connected group is central on every test
scheme. The base is arbitrary. -/
theorem isCentral_of_isNormal_of_isSplitTorus
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (hT : IsSplitTorus T.toGrp)
    [ConnectedSpace G.X.left] (hn : (SubgroupFunctor.range i).IsNormal) :
    IsCentral i := by
  have hc : SubgroupFunctor.range (𝟙 G) ≤ torusCentralizer i :=
    range_le_torusCentralizer_of_connected_of_isNormalizedBy i hT (𝟙 G)
      (fun V g x _ hx => hn V g x (Subgroup.mem_top _) hx)
  intro V t W a g
  have hg : g ∈ (SubgroupFunctor.range (𝟙 G)).carrier W := by
    apply SubgroupFunctor.mem_range.mpr
    exact ⟨g, by simp only [Grp.id_hom_hom, Category.comp_id]⟩
  have h := hc W hg W (𝟙 W) (a ≫ t)
  simpa only [Category.id_comp, Category.assoc] using h.symm

end Langlands.GroupScheme
