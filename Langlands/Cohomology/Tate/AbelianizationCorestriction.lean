import Langlands.Cohomology.Tate.LowDegree
import Langlands.Cohomology.Tate.NegativeHomologyComparison

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G J : Type u} [CommRing R] [Group G] [Group J]

instance restricted_isTrivial (f : J →* G) (A : Rep.{u} R G) [A.IsTrivial] :
    (Rep.res f A).IsTrivial where
  out g := Representation.isTrivial_def A.ρ (f g)

/-- Ordinary first-homology pushforward on a single chain with trivial coefficients. -/
lemma groupHomology_map_single {A : Rep.{u} R G} {B : Rep.{u} R J}
    [A.IsTrivial] [B.IsTrivial] (f : G →* J) (φ : A ⟶ Rep.res f B) (g : G) (a : A) :
    groupHomology.map f φ 1
        (groupHomology.H1π A
          ((groupHomology.cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a))) =
      groupHomology.H1π B
        ((groupHomology.cycles₁IsoOfIsTrivial B).inv (Finsupp.single (f g) (φ.hom a))) := by
  have hc : groupHomology.mapCycles₁ f φ
      ((groupHomology.cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a)) =
      (groupHomology.cycles₁IsoOfIsTrivial B).inv (Finsupp.single (f g) (φ.hom a)) := by
    apply Subtype.ext
    change groupHomology.chainsMap₁ f φ (Finsupp.single g a) =
      Finsupp.single (f g) (φ.hom a)
    simp [groupHomology.chainsMap₁]
  exact (ConcreteCategory.congr_hom (groupHomology.H1π_comp_map f φ)
    ((groupHomology.cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a))).trans
      (congrArg (groupHomology.H1π B) hc)

variable [Fintype G]
variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

/-- At degree minus two, corestriction sends the actual single-chain class to its inclusion. -/
theorem corestriction_minusTwoClass (A : Rep.{u} R G) [A.IsTrivial] (h : H) (a : A) :
    corestriction H A (-2) (minusTwoClass (Rep.res H.subtype A) h a) =
      minusTwoClass A (h : G) a := by
  have hh :
      corestriction H A (-2) (minusTwoClass (Rep.res H.subtype A) h a) =
      ((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A).inv
        (groupHomology.map H.subtype (𝟙 (Rep.res H.subtype A)) 1
          (((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app
            (Rep.res H.subtype A)).hom
            (((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app
              (Rep.res H.subtype A)).inv
              (groupHomology.H1π (Rep.res H.subtype A)
                ((groupHomology.cycles₁IsoOfIsTrivial (Rep.res H.subtype A)).inv
                  (Finsupp.single h a)))))) :=
    ConcreteCategory.congr_hom (corestriction_groupHomology H A 1)
      (minusTwoClass (Rep.res H.subtype A) h a)
  rw [Iso.inv_hom_id_apply] at hh
  exact hh.trans (congrArg
    ((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A).inv
    (groupHomology_map_single H.subtype (𝟙 (Rep.res H.subtype A)) h a))

omit [Fintype H] [Fintype (G ⧸ H)] in
/-- A single chain with coefficient one represents every degree-minus-two integral Tate class. -/
lemma integralMinusTwoClass_surjective :
    Function.Surjective (fun g : G => minusTwoClass (integralTrivial G) g (1 : IntegralScalar.{u})) := by
  intro x
  obtain ⟨g, hg⟩ := Quotient.exists_rep (Additive.toMul (integralMinusTwoEquiv G x))
  refine ⟨g, (integralMinusTwoEquiv G).injective ?_⟩
  rw [integralMinusTwoEquiv_class]
  exact congrArg Additive.ofMul hg

/-- Integral Tate corestriction in degree minus two is the actual inclusion on abelianizations. -/
theorem integralMinusTwoEquiv_corestriction
    (x : tateCohomology (integralTrivial H) (-2)) :
    integralMinusTwoEquiv G (corestriction H (integralTrivial G) (-2) x) =
      abelianizationInclusion H (integralMinusTwoEquiv H x) := by
  obtain ⟨h, rfl⟩ := integralMinusTwoClass_surjective x
  exact (congrArg (integralMinusTwoEquiv G)
    (corestriction_minusTwoClass H (integralTrivial G) h 1)).trans
      ((integralMinusTwoEquiv_class (h : G)).trans
        (congrArg (abelianizationInclusion H) (integralMinusTwoEquiv_class h)).symm)

end Langlands.Tate
