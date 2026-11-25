import Langlands.GroupScheme.Reductive.AffineOppositeRootNormalization
import Langlands.GroupScheme.Reductive.LocalSplitRootPairLaws
import Langlands.GroupScheme.Reductive.LocalSplitRankOneNormalStatement

/-! # Rank-one laws over an arbitrary affine base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.LocalSplitCell

open LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
    {G : GroupScheme (Spec (CommRingCat.of R))}

/-- The all-test laws imply the existing simple-root normalization
predicate, with its exact original-base coroot square. -/
theorem RankOneLaws.rankOneNormal
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    {J : Type u} (P : RootDatum J (I → ℤ) (I → ℤ))
    (v : J → (Ga R ⟶ G)) (a : J)
    (h : RankOneLaws i (P.coroot a) (v a) (v (P.reflectionPerm a a))) :
    RankOneNormal i P v a := by
  refine ⟨?_, ?_, ?_⟩
  · intro B _ s x
    exact h.1 (Over.mk s) x
  · intro B _ s x
    exact h.2.1 (Over.mk s) x
  · have hs := h.2.2.1 (𝟙_ (Over (Spec (CommRingCat.of R))))
    change ((𝟙 _ ≫ weylPoint (v a) (v (P.reflectionPerm a a))) *
      (𝟙 _ ≫ weylPoint (v a) (v (P.reflectionPerm a a)))) = _ at hs
    simpa only [Category.id_comp] using hs

/-- The four exact rank-one identities are detected on a family of
affine etale neighborhoods through every base point. -/
theorem RankOneLaws.of_pointwise_etale_baseChange
    (A : Spec (CommRingCat.of R) → CommRingCat.{u})
    (alg : ∀ s, Algebra R (A s))
    (het : ∀ s, letI := alg s; Etale (algebraBaseMap R (A s)))
    (hcover : ∀ s, letI := alg s; s ∈ Set.range (algebraBaseMap R (A s)))
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (nu : I → ℤ) (xp xm : Ga R ⟶ G)
    (h : ∀ s, letI := alg s;
      RankOneLaws (splitTorus.baseChangeHom (K := A s) G I i) nu
        (baseChangeRoot (A s) xp) (baseChangeRoot (A s) xm)) :
    RankOneLaws i nu xp xm := by
  let b (s : Spec (CommRingCat.of R)) : Spec (A s) ⟶ Spec (CommRingCat.of R) :=
    letI := alg s
    algebraBaseMap R (A s)
  let 𝒰 : Scheme.Cover Scheme.fppfPrecoverage (Spec (CommRingCat.of R)) :=
    Scheme.Cover.mkOfCovers _ (fun s => Spec (A s)) b
      (fun s => by obtain ⟨t, ht⟩ := hcover s; exact ⟨s, t, ht⟩)
      (fun s => by
        let : Etale (b s) := het s
        exact ⟨inferInstance, inferInstance⟩)
  let test (s : Spec (CommRingCat.of R)) (Z : Over (Spec (CommRingCat.of R))) :=
    (Over.pullback (b s)).obj Z
  let cover (s : Spec (CommRingCat.of R)) (Z : Over (Spec (CommRingCat.of R))) :
      (Over.map (b s)).obj (test s Z) ⟶ Z :=
    (Over.mapPullbackAdj (b s)).counit.app Z
  have ext {Z : Over (Spec (CommRingCat.of R))} {v w : Z ⟶ G.X}
      (he : ∀ s, cover s Z ≫ v = cover s Z ≫ w) : v = w := by
    apply Over.OverMorphism.ext
    apply CategoryTheory.Precoverage.ZeroHypercover.hom_ext (𝒰.pullback₁ Z.hom)
    intro s
    exact congrArg (fun a => a.left) (he s)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z x
    apply ext
    intro s
    let := alg s
    simp only [MonObj.comp_mul, GrpObj.comp_inv, G.constantPoint_naturality,
      comp_rootPoint, map_neg]
    have e := congrArg (GroupScheme.baseChangePointsEquiv (algebraBaseMap R (A s)) G (test s Z))
      ((h s).1 (test s Z) ((cover s Z).left.appTop x))
    simpa only [map_mul, map_inv, baseChangePointsEquiv_constantWeyl,
      baseChangePointsEquiv_rootPoint] using e
  · intro Z x
    apply ext
    intro s
    let := alg s
    simp only [MonObj.comp_mul, GrpObj.comp_inv, G.constantPoint_naturality,
      comp_rootPoint, map_neg]
    have e := congrArg (GroupScheme.baseChangePointsEquiv (algebraBaseMap R (A s)) G (test s Z))
      ((h s).2.1 (test s Z) ((cover s Z).left.appTop x))
    simpa only [map_mul, map_inv, baseChangePointsEquiv_constantWeyl,
      baseChangePointsEquiv_rootPoint] using e
  · intro Z
    apply ext
    intro s
    let := alg s
    have hminus : Units.map (cover s Z).left.appTop.hom.toMonoidHom
        (-1 : Γ(Z.left, ⊤)ˣ) = -1 := by
      convert Units.map_neg_one (cover s Z).left.appTop.hom using 1
    simp only [MonObj.comp_mul, G.constantPoint_naturality, ← Category.assoc,
      comp_cocharPoint, hminus]
    have e := congrArg (GroupScheme.baseChangePointsEquiv (algebraBaseMap R (A s)) G (test s Z))
      ((h s).2.2.1 (test s Z))
    simpa only [map_mul, baseChangePointsEquiv_constantWeyl,
      baseChangePointsEquiv_torus, baseChangePointsEquiv_cocharPoint] using e
  · intro Z x y d hd
    apply ext
    intro s
    let := alg s
    simp only [MonObj.comp_mul, comp_rootPoint, ← Category.assoc,
      comp_cocharPoint, map_mul]
    let res : Γ(Z.left, ⊤) →+* Γ((test s Z).left, ⊤) :=
      (cover s Z).left.appTop.hom
    let d' := Units.map res.toMonoidHom d
    have hd' : (d' : Γ((test s Z).left, ⊤)) = 1 + res x * res y := by
      change res (d : Γ(Z.left, ⊤)) = _
      rw [hd, map_add, map_one, map_mul]
    have e := congrArg (GroupScheme.baseChangePointsEquiv (algebraBaseMap R (A s)) G (test s Z))
      ((h s).2.2.2 (test s Z) (res x) (res y) d' hd')
    simp only [map_mul, baseChangePointsEquiv_rootPoint,
      baseChangePointsEquiv_torus, baseChangePointsEquiv_cocharPoint,
      d', Units.coe_map_inv] at e
    convert e using 1

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.AffineRootNormalization

open LocalSplitCell LocalSplitRootBaseChange
open splitTorus.RelativeCocharacterCentralizer

variable {R : Type u} [CommRing R]
    {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu : I → ℤ)
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hstd : ∀ m n, P.toLinearMap m n = ∑ j, m j * n j)
    (a : J) (ha : ∑ j, P.root a j * mu j = 0)
    (hmu : ∀ b : J, ∑ j, P.root b j * mu j = 0 →
      P.root b = P.root a ∨ P.root b = -P.root a)
    {xp xm : Ga R ⟶ G}
    (hp : IsRootParametrization i (P.root a) xp)
    (hm : IsRootParametrization i (-P.root a) xm)
    {s : Spec (CommRingCat.of R)}
    {n₀ : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField s) ⟶
      (groupScheme I G i mu).X}
    (E : RingRootCell.AffineEtaleUnitCellData
      (affineCorootCell i mu hG hmax hP hstd a ha hmu hp hm)
      (splitTorus.exponentCommIso (Spec (CommRingCat.of R)) I (P.reflection a)) s n₀)

/-- A supplied normalized pair forces the actual chart beta coordinate
to be one, over an arbitrary original ring. -/
theorem affineEtaleWeylData_beta_eq_one (hi : IsClosedSubgroup i)
    (hn : IsWeylPoint i (weylPoint xp xm) (P.reflection a)) :
    letI := E.coefficientAlgebra
    (affineEtaleWeylData i mu hG hmax hP hstd a ha hmu hp hm E hi).cβ = 1 := by
  let := E.coefficientAlgebra
  let C := groupScheme I G i mu
  let hC := isReductive i mu hG
  let : Smooth C.X.hom := hC.smooth
  let W := affineEtaleWeylData i mu hG hmax hP hstd a ha hmu hp hm E hi
  let b := algebraBaseMap R E.ring
  let : IsAffineHom W.G.X.hom := by
    change IsAffineHom (((GroupScheme.baseChange b).obj C).X.hom)
    exact inferInstanceAs (IsAffineHom (Limits.pullback.snd C.X.hom b))
  let : IsAffine W.G.X.left := isAffine_of_isAffineHom W.G.X.hom
  apply W.cβ_eq_one_of_unscaled_normalizes
  · apply splitTorusCentralizer_eq_range_of_fibrewiseMaximal
      ((isReductive i mu hG).baseChange b) (isSplitTorus_splitTorus I)
    · exact splitTorus.isClosedSubgroup_coordinateBaseChange I C (torusHom I G i mu) b
        (isClosedSubgroup_torusHom I G i mu hi)
    · exact splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange I C (torusHom I G i mu) b
        (isFibrewiseMaximalTorus i mu hmax)
  · rw [W.unscaledWeylPoint_base_eq]
    have h := (isWeylPoint_baseChange E.ring
      (isWeylPoint_rootLift i mu (a := a) ha hp hm hn)).isNormalizingPoint
    have he : RingRootCell.reflectionIso W.α W.h W.hh =
        splitTorus.exponentCommIso (Spec (CommRingCat.of E.ring)) I (P.reflection a) :=
      reflectionIso_eq hstd a E.ring
    rw [he]
    exact h

/-- The actual etale Weyl data retain exactly the supplied root
coordinates, with their normalization forced to beta one. -/
def suppliedAffineEtaleWeylData (hi : IsClosedSubgroup i)
    (hn : IsWeylPoint i (weylPoint xp xm) (P.reflection a)) :
    letI := E.coefficientAlgebra
    {W : RingRootCell.WeylData E.ring // W.cβ = 1} := by
  letI := E.coefficientAlgebra
  exact ⟨affineEtaleWeylData i mu hG hmax hP hstd a ha hmu hp hm E hi,
    affineEtaleWeylData_beta_eq_one i mu hG hmax hP hstd a ha hmu hp hm E hi hn⟩

include hG hmax hP hstd hmu in
/-- The exact four supplied-root laws descend from the actual
pointwise charts of the rank-one centralizer. -/
theorem rankOneLaws_rootLift (hi : IsClosedSubgroup i)
    (hn : IsWeylPoint i (weylPoint xp xm) (P.reflection a)) :
    RankOneLaws (torusHom I G i mu) (P.coroot a)
      (rootLift i mu hp ha)
      (rootLift i mu hm (by
        simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
          congrArg Neg.neg ha)) := by
  let p (s : Spec (CommRingCat.of R)) :=
    pointedEtaleUnitCellReflection i mu hG hmax hP hstd a ha hmu hp hm hi s
  let E (s : Spec (CommRingCat.of R)) := (p s).affineEtaleUnitCell
  apply RankOneLaws.of_pointwise_etale_baseChange
    (fun s => (E s).ring) (fun s => (E s).coefficientAlgebra) ?_ ?_
  · intro s
    let := (E s).coefficientAlgebra
    let C := groupScheme I G i mu
    let W := affineEtaleWeylData i mu hG hmax hP hstd a ha hmu hp hm (E s) hi
    let b := algebraBaseMap R (E s).ring
    let : IsAffineHom W.G.X.hom := by
      change IsAffineHom (((GroupScheme.baseChange b).obj C).X.hom)
      exact inferInstanceAs (IsAffineHom (Limits.pullback.snd C.X.hom b))
    let : IsAffine W.G.X.left := isAffine_of_isAffineHom W.G.X.hom
    have hb : W.cβ = 1 :=
      affineEtaleWeylData_beta_eq_one i mu hG hmax hP hstd a ha hmu hp hm (E s) hi hn
    have h := W.rankOneLaws_of_beta_eq_one (𝟙 _) (P.coroot a)
      (by exact Category.comp_id _) hb
    change RankOneLaws W.i (P.coroot a) W.xp W.xm at h
    exact h
  · intro s
    rw [(E s).coefficientAlgebra_baseMap]
    exact (E s).etale
  · intro s
    rw [(E s).coefficientAlgebra_baseMap]
    refine ⟨(E s).residuePoint (IsLocalRing.closedPoint _), ?_⟩
    change ((E s).residuePoint ≫ (E s).projection) (IsLocalRing.closedPoint _) = s
    rw [(E s).residue_over, Scheme.fromSpecResidueField_apply]

include hG hmax hP hstd ha hmu hp hm in
/-- Including the actual centralizer gives the same supplied-root
laws in the original ambient group over the arbitrary ring. -/
theorem rankOneLaws_of_pairing (hi : IsClosedSubgroup i)
    (hn : IsWeylPoint i (weylPoint xp xm) (P.reflection a)) :
    RankOneLaws i (P.coroot a) xp xm := by
  have h := (rankOneLaws_rootLift i mu hG hmax hP hstd a ha hmu hp hm hi hn).comp
    (inclusion I G i mu)
  simpa only [torusHom_comp, rootLift_comp] using h

end Langlands.GroupScheme.AffineRootNormalization

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R]
    {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
    {xp xm : Ga R ⟶ G}
    (hp : IsRootParametrization i (P.root a) xp)
    (hm : IsRootParametrization i (-P.root a) xm)

include hG hi hmax hP hp hm in
/-- Every supplied Weyl-normalized opposite pair over an arbitrary
commutative ring satisfies the exact existing rank-one laws on every
scheme test. -/
theorem rankOneLaws_of_weylNormalization_affine
    (hn : IsWeylPoint i (weylPoint xp xm) (P.reflection a)) :
    RankOneLaws i (P.coroot a) xp xm := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · let : IsEmpty (Spec (CommRingCat.of R)) :=
      inferInstanceAs (IsEmpty (PrimeSpectrum R))
    have he {Z : Over (Spec (CommRingCat.of R))} (v w : Z ⟶ G.X) : v = w := by
      let : IsEmpty Z.left := Function.isEmpty Z.hom
      apply Over.OverMorphism.ext
      exact isInitialOfIsEmpty.hom_ext _ _
    exact ⟨fun _ _ => he _ _, fun _ _ => he _ _, fun _ => he _ _,
      fun _ _ _ _ _ => he _ _⟩
  · obtain ⟨m, hm'⟩ := Ideal.exists_maximal R
    let := hm'
    let k := R ⧸ m
    let : Field k := Ideal.Quotient.field m
    have hstd : ∀ v w, P.toLinearMap v w = ∑ j, v j * w j := hP.pairing k
    have : Finite J := hP.finite
    have := hP.isReduced
    obtain ⟨mu, ha, hmu⟩ := LocalRootGroup.exists_kernel_exponent P k a
    exact AffineRootNormalization.rankOneLaws_of_pairing
      i mu hG hmax hP hstd a ha hmu hp hm hi hn

end Langlands.GroupScheme.LocalSplitCell
