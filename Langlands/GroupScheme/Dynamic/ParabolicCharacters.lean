import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Dynamic.NormalizedLimits
import Langlands.GroupScheme.Dynamic.ImproperParabolic

/-! # Characters of a dynamic parabolic and its centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G P Z : GroupScheme S}
  {ν : (Gm S).toGrp ⟶ G} {iP : P ⟶ G} {iZ : Z ⟶ G}

/-- A homomorphism to a separated commutative group has the same value at a
point and every limit under an inner cocharacter action. -/
theorem comp_eq_comp_of_hasLimit_to_commutative
    {H : GroupScheme S} (χ : (Gm S).toGrp ⟶ H)
    (C : CommGroupScheme S) [IsSeparated C.X.hom] (f : H ⟶ C.toGrp)
    {T : Over S} {g l : T ⟶ H.X} (hl : HasLimit χ g l) :
    g ≫ f.hom.hom = l ≫ f.hom.hom := by
  have hz : g ≫ f.hom.hom ∈ (centralizer (χ ≫ f)).carrier T := by
    rw [centralizer_eq_top_of_commutative C]
    trivial
  exact (hasLimit_of_mem_centralizer (χ ≫ f) hz).unique (χ ≫ f)
    (hl.comp_hom χ f)

/-- The cocharacter factors through its dynamic parabolic on every test scheme. -/
def cocharacterToParabolicPoints (hP : (parabolic ν).IsRepresentedBy iP)
    (T : Over S) : (T ⟶ (Gm S).X) →* (T ⟶ P.X) :=
  (hP.pointsEquiv T).symm.toMonoidHom.comp
      { toFun := fun t => ⟨t ≫ ν.hom.hom,
          centralizer_le_parabolic ν T
            (range_le_centralizer ν T (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩))⟩
        map_one' := Subtype.ext (MonObj.one_comp _)
        map_mul' a b := Subtype.ext (MonObj.mul_comp a b _) }

theorem cocharacterToParabolicPoints_naturality (hP : (parabolic ν).IsRepresentedBy iP)
    {T T' : Over S} (a : T' ⟶ T) (t : T ⟶ (Gm S).X) :
    cocharacterToParabolicPoints hP T' (a ≫ t) =
      a ≫ cocharacterToParabolicPoints hP T t := by
  apply hP.1.right_cancellation
  simp only [cocharacterToParabolicPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp, Category.assoc,
    SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp]
  rfl

/-- The cocharacter itself, factored through its represented dynamic parabolic. -/
def cocharacterToParabolic (hP : (parabolic ν).IsRepresentedBy iP) :
    (Gm S).toGrp ⟶ P :=
  homOfPoints (cocharacterToParabolicPoints hP) (cocharacterToParabolicPoints_naturality hP)

/-- Factoring the cocharacter does not change its ambient homomorphism. -/
theorem cocharacterToParabolic_comp (hP : (parabolic ν).IsRepresentedBy iP) :
    cocharacterToParabolic hP ≫ iP = ν := by
  apply hom_ext_points
  intro T t
  rw [Grp.comp_hom_hom, ← Category.assoc]
  unfold cocharacterToParabolic
  rw [comp_homOfPoints _ (cocharacterToParabolicPoints_naturality hP)]
  unfold cocharacterToParabolicPoints
  exact SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp hP _

variable [IsSeparated G.X.hom]

/-- The ambient dynamic limit lifts to the closed represented parabolic. -/
theorem hasLimit_limitGroupHom_toParabolic
    (hP : (parabolic ν).IsRepresentedBy iP) (hc : IsClosedSubgroup iP)
    (hZ : (centralizer ν).IsRepresentedBy iZ)
    {T : Over S} (p : T ⟶ P.X) :
    HasLimit (cocharacterToParabolic hP) p
      ((p ≫ (limitGroupHom hP hZ).hom.hom) ≫
        (centralizerToParabolic hP hZ).hom.hom) := by
  apply (hasLimit_comp_hom_iff (cocharacterToParabolic hP) iP hc).mp
  rw [cocharacterToParabolic_comp, Category.assoc, ← Grp.comp_hom_hom,
    centralizerToParabolic_comp, limitGroupHom_comp]
  exact hasLimit_limit ν (hP.pointsEquiv T p)

/-- Every homomorphism from a closed dynamic parabolic to a separated
commutative group factors through its limit retraction. -/
theorem hom_eq_limitGroupHom_comp
    (hP : (parabolic ν).IsRepresentedBy iP) (hc : IsClosedSubgroup iP)
    (hZ : (centralizer ν).IsRepresentedBy iZ)
    (C : CommGroupScheme S) [IsSeparated C.X.hom] (f : P ⟶ C.toGrp) :
    f = limitGroupHom hP hZ ≫ centralizerToParabolic hP hZ ≫ f := by
  apply hom_ext_points
  intro T p
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    comp_eq_comp_of_hasLimit_to_commutative (cocharacterToParabolic hP) C f
      (hasLimit_limitGroupHom_toParabolic hP hc hZ p)

/-- Restriction to the dynamic centralizer identifies all rational characters
of a closed represented dynamic parabolic with those of its centralizer. -/
def parabolicCharacterEquiv
    (hP : (parabolic ν).IsRepresentedBy iP) (hc : IsClosedSubgroup iP)
    (hZ : (centralizer ν).IsRepresentedBy iZ) :
    rationalCharacters P ≃+ rationalCharacters Z where
  toFun := characterRestrict (centralizerToParabolic hP hZ)
  invFun := characterRestrict (limitGroupHom hP hZ)
  left_inv χ := by
    have : IsSeparated (Gm S).X.hom := by
      have : IsSeparated Gm.overSpecZ.{u}.hom := by
        change IsSeparated (Spec.map _)
        infer_instance
      change IsSeparated (Limits.pullback.snd _ (Gm.toSpecZ S))
      infer_instance
    apply congrArg Additive.ofMul
    exact (hom_eq_limitGroupHom_comp hP hc hZ (Gm S) χ.toMul).symm
  right_inv χ := by
    change Additive.ofMul (centralizerToParabolic hP hZ ≫
      (limitGroupHom hP hZ ≫ χ.toMul)) = χ
    rw [← Category.assoc, centralizerToParabolic_comp_limitGroupHom, Category.id_comp]
    rfl
  map_add' := map_add _

@[simp] theorem parabolicCharacterEquiv_apply
    (hP : (parabolic ν).IsRepresentedBy iP) (hc : IsClosedSubgroup iP)
    (hZ : (centralizer ν).IsRepresentedBy iZ) (χ : rationalCharacters P) :
    parabolicCharacterEquiv hP hc hZ χ =
      characterRestrict (centralizerToParabolic hP hZ) χ :=
  rfl

@[simp] theorem parabolicCharacterEquiv_symm_apply
    (hP : (parabolic ν).IsRepresentedBy iP) (hc : IsClosedSubgroup iP)
    (hZ : (centralizer ν).IsRepresentedBy iZ) (χ : rationalCharacters Z) :
    (parabolicCharacterEquiv hP hc hZ).symm χ =
      characterRestrict (limitGroupHom hP hZ) χ :=
  rfl

/-- Equality of rational characters can be checked on the dynamic centralizer. -/
theorem character_eq_iff_restrict_eq
    (hP : (parabolic ν).IsRepresentedBy iP) (hc : IsClosedSubgroup iP)
    (hZ : (centralizer ν).IsRepresentedBy iZ) (χ ψ : rationalCharacters P) :
    χ = ψ ↔ characterRestrict (centralizerToParabolic hP hZ) χ =
      characterRestrict (centralizerToParabolic hP hZ) ψ :=
  ⟨congrArg _, fun h => (parabolicCharacterEquiv hP hc hZ).injective h⟩

end Langlands.GroupScheme.Dynamic
