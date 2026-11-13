import Langlands.Representation.LanglandsClassification.OppositeStandardActualJacquetFamily
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.NoProperPseudoParabolicSplitTorusCentralReduction
import Langlands.GroupScheme.Rational.StandardLeviTorusFactor
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.SplitComponent.AffineTargetBridge
import Langlands.GroupScheme.Rational.ParabolicLeviIntersectionReduction

/-! # Nesting of the chosen opposite standard parabolics

For standard labels `J ⊆ K`, the chosen opposite parabolic of `P_J` lies in the
chosen opposite parabolic of `P_K`, and its intersection with the standard Levi
`M_K` is an actual parabolic of `M_K` with Levi `M_J`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic.OppositeStandardJacquetFamily

open GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

namespace Nesting

omit [IsAffineHom G.X.hom] in
include hG hi in
/-- Containment of dynamic parabolics of lattice cocharacters of a maximal
split torus is inherited by the negated cocharacters. -/
theorem parabolic_neg_le_neg {ζ ξ : cocharacterLattice T}
    (h : Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)) :
    Dynamic.parabolic (CommGroupScheme.groupHom (-ζ) ≫ i) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom (-ξ) ≫ i) := by
  have hsign := (relativeRootSignInclusions k G hG T i hi ζ ξ).1.mp h
  refine (relativeRootSignInclusions k G hG T i hi (-ζ) (-ξ)).1.mpr ?_
  intro α hα hle
  have hneg := relativeRootNegation k G hG T i hi α hα
  have h1 := hsign (-α) hneg
  simp only [map_neg, LinearMap.neg_apply] at hle h1 ⊢
  linarith [h1 (by linarith)]

omit [IsAffineHom G.X.hom] in
/-- Point images inherit inclusions of all-test ranges. -/
theorem pointImage_le_of_range_le {H H' : GroupScheme (Spec (CommRingCat.of k))}
    {j : H ⟶ G} {j' : H' ⟶ G}
    (h : SubgroupFunctor.range j ≤ SubgroupFunctor.range j') :
    pointImage j ≤ pointImage j' :=
  fun _ hx => h (Over.mk (𝟙 _)) hx

variable (J K : StandardJacquetFamily.Index i ν)

/-- The cocharacter chosen by `oppositeLeviParabolic` to realize the standard
parabolic and standard Levi of a label. -/
def realizing : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G :=
  DynamicLeviConjugacy.parabolicLeviRealizingCocharacter
    parabolicDynamic dynamicGeometricUnipotentRadical hG
    (StandardJacquetFamily.datum i ν hG hi hν J).hp
    (StandardJacquetFamily.datum i ν hG hi hν J).hl

theorem standardParabolic_eq_realizing :
    standardParabolic i ν J.val = Dynamic.parabolic (realizing i ν hG hi hν J) :=
  (ParabolicDatum.range_standard_p i ν hG hi hν J.val J.property).symm.trans
    (DynamicLeviConjugacy.parabolicLeviRealizingCocharacter_spec
      parabolicDynamic dynamicGeometricUnipotentRadical hG
      (StandardJacquetFamily.datum i ν hG hi hν J).hp
      (StandardJacquetFamily.datum i ν hG hi hν J).hl).1

theorem standardLevi_eq_realizing :
    standardLevi i ν J.val = Dynamic.centralizer (realizing i ν hG hi hν J) :=
  (ParabolicDatum.range_standard_l_comp_p i ν hG hi hν J.val J.property).symm.trans
    (DynamicLeviConjugacy.parabolicLeviRealizingCocharacter_spec
      parabolicDynamic dynamicGeometricUnipotentRadical hG
      (StandardJacquetFamily.datum i ν hG hi hν J).hp
      (StandardJacquetFamily.datum i ν hG hi hν J).hl).2

/-- The opposite inclusion is the representative of the dynamic parabolic of the
inverse realizing cocharacter. -/
theorem range_opposite_p :
    SubgroupFunctor.range (OppositeStandardJacquetFamily.datum i ν hG hi hν J).p =
      Dynamic.parabolic (Dynamic.oppositeCocharacter (realizing i ν hG hi hν J)) := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact (Dynamic.Affine.isRepresentedBy_parabolicHom _).2

/-- The realizing cocharacter factors through the maximal split torus. -/
theorem exists_lattice : ∃ ζ : cocharacterLattice T,
    CommGroupScheme.groupHom ζ ≫ i = realizing i ν hG hi hν J := by
  obtain ⟨f, hf⟩ := hi.exists_factor_of_commute isSplitTorus_gm (realizing i ν hG hi hν J)
    (fun U x y => by
      have hy : y ≫ i.hom.hom ∈ (Dynamic.centralizer (realizing i ν hG hi hν J)).carrier U := by
        rw [← standardLevi_eq_realizing]
        exact range_le_standardLevi i ν J.val U ⟨y, rfl⟩
      exact NoProperPseudoParabolicSplitTorusCentral.commute_of_mem_centralizer _ hy x)
  exact ⟨Additive.ofMul f, hf⟩

/-- A lattice cocharacter of the maximal split torus lifting the realizing
cocharacter of a label. -/
def lattice : cocharacterLattice T := (exists_lattice i ν hG hi hν J).choose

theorem lattice_comp :
    CommGroupScheme.groupHom (lattice i ν hG hi hν J) ≫ i = realizing i ν hG hi hν J :=
  (exists_lattice i ν hG hi hν J).choose_spec

theorem range_opposite_p_eq :
    SubgroupFunctor.range (OppositeStandardJacquetFamily.datum i ν hG hi hν J).p =
      Dynamic.parabolic (CommGroupScheme.groupHom (-lattice i ν hG hi hν J) ≫ i) := by
  rw [range_opposite_p, groupHom_neg_comp_eq_oppositeCocharacter, lattice_comp]

theorem standardLevi_eq_neg :
    standardLevi i ν J.val =
      Dynamic.centralizer (CommGroupScheme.groupHom (-lattice i ν hG hi hν J) ≫ i) := by
  rw [groupHom_neg_comp_eq_oppositeCocharacter, lattice_comp,
    Dynamic.centralizer_oppositeCocharacter, standardLevi_eq_realizing]

variable {J K}

/-- Nested labels give nested opposite parabolics, on every test scheme. -/
theorem range_opposite_p_le (h : J.val ⊆ K.val) :
    SubgroupFunctor.range (OppositeStandardJacquetFamily.datum i ν hG hi hν J).p ≤
      SubgroupFunctor.range (OppositeStandardJacquetFamily.datum i ν hG hi hν K).p := by
  rw [range_opposite_p_eq, range_opposite_p_eq]
  apply parabolic_neg_le_neg i hG hi
  rw [lattice_comp, lattice_comp, ← standardParabolic_eq_realizing,
    ← standardParabolic_eq_realizing]
  exact ((standardParabolicOrder k G hG T i hi ν hν).1 J.val K.val J.property
    K.property).1.mp h

/-- Nested labels give nested opposite parabolics on rational points. -/
theorem pointImage_opposite_p_le (h : J.val ⊆ K.val) :
    pointImage (OppositeStandardJacquetFamily.datum i ν hG hi hν J).p ≤
      pointImage (OppositeStandardJacquetFamily.datum i ν hG hi hν K).p :=
  pointImage_le_of_range_le (range_opposite_p_le i ν hG hi hν h)

include hG hi hν in
/-- Nested labels give nested standard Levis, on every test scheme. -/
theorem standardLevi_le (h : J.val ⊆ K.val) :
    standardLevi i ν J.val ≤ standardLevi i ν K.val :=
  (((standardParabolicOrder k G hG T i hi ν hν).1 J.val K.val J.property
    K.property).2 h).1

/-- The canonical inclusion of the standard Levi of `J` in the standard Levi of `K`. -/
def leviInclusion (h : J.val ⊆ K.val) :
    Standard.leviScheme i ν J.val ⟶ Standard.leviScheme i ν K.val :=
  (Standard.isRepresentedBy_leviHom i ν K.val).factorHom (Standard.leviHom i ν J.val)
    ((Standard.isRepresentedBy_leviHom i ν J.val).2.le.trans
      (standardLevi_le i ν hG hi hν h))

@[simp] theorem leviInclusion_comp (h : J.val ⊆ K.val) :
    leviInclusion i ν hG hi hν h ≫ Standard.leviHom i ν K.val =
      Standard.leviHom i ν J.val :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

theorem mono_leviInclusion (h : J.val ⊆ K.val) :
    Mono (leviInclusion i ν hG hi hν h).hom.hom := by
  have hJ : Mono (Standard.leviHom i ν J.val).hom.hom :=
    (Standard.isRepresentedBy_leviHom i ν J.val).1
  rw [← leviInclusion_comp i ν hG hi hν h, Grp.comp_hom_hom] at hJ
  exact mono_of_mono _ (Standard.leviHom i ν K.val).hom.hom

variable (J K) in
/-- The inner cocharacter of the standard Levi of `K`: the negated lattice
cocharacter of `J`, factored through the standard Levi of `K`. -/
def innerCocharacter :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Standard.leviScheme i ν K.val :=
  CommGroupScheme.groupHom (-lattice i ν hG hi hν J) ≫
    standardLeviTorusFactor i ν K.val (Standard.isRepresentedBy_leviHom i ν K.val)

theorem innerCocharacter_comp :
    innerCocharacter i ν hG hi hν J K ≫ Standard.leviHom i ν K.val =
      CommGroupScheme.groupHom (-lattice i ν hG hi hν J) ≫ i := by
  rw [innerCocharacter, Category.assoc, standardLeviTorusFactor_comp]

/-- The inclusion of the standard Levi of `J` represents the dynamic
centralizer of the inner cocharacter in the standard Levi of `K`. -/
theorem isRepresentedBy_centralizer_inner (h : J.val ⊆ K.val) :
    (Dynamic.centralizer (innerCocharacter i ν hG hi hν J K)).IsRepresentedBy
      (leviInclusion i ν hG hi hν h) := by
  have hm : Mono (Standard.leviHom i ν K.val).hom.hom :=
    (Standard.isRepresentedBy_leviHom i ν K.val).1
  refine ⟨mono_leviInclusion i ν hG hi hν h, ?_⟩
  rw [Dynamic.centralizer_eq_comap_of_isClosedSubgroup _ _
      (Standard.isClosedSubgroup_leviHom i ν K.val),
    innerCocharacter_comp, ← standardLevi_eq_neg,
    ← (Standard.isRepresentedBy_leviHom i ν J.val).2]
  refine SubgroupFunctor.ext fun U => Subgroup.ext fun x => ?_
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [← leviInclusion_comp i ν hG hi hν h, Grp.comp_hom_hom, Category.assoc]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, (cancel_mono (Standard.leviHom i ν K.val).hom.hom).mp ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, leviInclusion_comp, hy]

include hG hi hν in
variable (J) in
/-- Standard Levis are connected reductive. -/
theorem isConnectedReductive_levi :
    IsConnectedReductive (Standard.leviScheme i ν J.val) :=
  (StandardJacquetFamily.datum i ν hG hi hν J).hl.isConnectedReductive

/-- Nested opposite standard data for labels `J ⊆ K`: an actual parabolic of
the standard Levi of `K` with Levi the standard Levi of `J`, cut out by the
inner cocharacter, together with a morphism of the chosen split components
compatible with the inclusions and with the torus factors. -/
structure NestedData (h : J.val ⊆ K.val) where
  /-- The inner parabolic scheme. -/
  P : GroupScheme (Spec (CommRingCat.of k))
  /-- The unipotent radical scheme of the inner parabolic. -/
  N : GroupScheme (Spec (CommRingCat.of k))
  /-- The inner parabolic inclusion into the standard Levi of `K`. -/
  p : P ⟶ Standard.leviScheme i ν K.val
  /-- The standard Levi of `J` as a Levi of the inner parabolic. -/
  m : Standard.leviScheme i ν J.val ⟶ P
  /-- The unipotent radical inclusion. -/
  n : N ⟶ P
  hp : IsParabolicSubgroup p
  hm : IsRationalLeviSubgroup m
  hn : LeviSubgroup.IsGeometricUnipotentRadical n
  hmul : IsIso (subgroupMultiplication m n)
  levi_eq : m ≫ p = leviInclusion i ν hG hi hν h
  range_eq : SubgroupFunctor.range p =
    Dynamic.parabolic (innerCocharacter i ν hG hi hν J K)
  /-- The morphism of chosen split components. -/
  e : (OppositeStandardJacquetFamily.component i ν hG hi hν K).A ⟶
    (OppositeStandardJacquetFamily.component i ν hG hi hν J).A
  e_comp : CommGroupScheme.groupHom e ≫
      (OppositeStandardJacquetFamily.component i ν hG hi hν J).a ≫
        leviInclusion i ν hG hi hν h =
      (OppositeStandardJacquetFamily.component i ν hG hi hν K).a
  e_g : CommGroupScheme.groupHom e ≫
      (OppositeStandardJacquetFamily.component i ν hG hi hν J).g =
      (OppositeStandardJacquetFamily.component i ν hG hi hν K).g

/-- Choose nested opposite standard data for labels `J ⊆ K`. -/
def nestedData (h : J.val ⊆ K.val) : NestedData i ν hG hi hν h := by
  let H := Standard.leviScheme i ν K.val
  have hH : IsConnectedReductive H := isConnectedReductive_levi i ν hG hi hν K
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : IsSeparated H.X.hom := hH.isSeparated
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let ψ := innerCocharacter i ν hG hi hν J K
  let Q := Dynamic.Affine.parabolicScheme ψ
  let U := Dynamic.Affine.unipotentScheme ψ
  let q : Q ⟶ H := Dynamic.Affine.parabolicHom ψ
  let u : U ⟶ H := Dynamic.Affine.unipotentHom ψ
  have hQ : (Dynamic.parabolic ψ).IsRepresentedBy q :=
    Dynamic.Affine.isRepresentedBy_parabolicHom ψ
  have hU : (Dynamic.unipotent ψ).IsRepresentedBy u :=
    Dynamic.Affine.isRepresentedBy_unipotentHom ψ
  have hZ := isRepresentedBy_centralizer_inner i ν hG hi hν h
  let lQ : Standard.leviScheme i ν J.val ⟶ Q := Dynamic.centralizerToParabolic hQ hZ
  let rQ : U ⟶ Q := Dynamic.unipotentToParabolic hQ hU
  have hlQ : lQ ≫ q = leviInclusion i ν hG hi hν h :=
    Dynamic.centralizerToParabolic_comp hQ hZ
  have hrQ : rQ ≫ q = u := Dynamic.unipotentToParabolic_comp hQ hU
  have hqc : IsClosedSubgroup q := Dynamic.Affine.isClosedSubgroup_parabolicHom ψ
  let : IsClosedImmersion q.hom.hom.left := hqc
  let : IsAffineHom Q.X.hom := by
    rw [← Over.w q.hom.hom]
    infer_instance
  have hrad : IsGeometricUnipotentRadical rQ :=
    dynamicGeometricUnipotentRadical k H hH ψ Q U q rQ hQ (by rw [hrQ]; exact hU)
  have hmul : IsIso (subgroupMultiplication lQ rQ) :=
    Dynamic.isIso_subgroupMultiplication hQ hZ hU lQ rQ hlQ hrQ
  have hlevi : IsRationalLeviSubgroup lQ :=
    Dynamic.isRationalLeviSubgroup_of_geometricUnipotentRadical
      hQ hZ hU lQ rQ hlQ hrQ (isConnectedReductive_levi i ν hG hi hν J) hrad
  let CJ := OppositeStandardJacquetFamily.component i ν hG hi hν J
  let CK := OppositeStandardJacquetFamily.component i ν hG hi hν K
  let φ : CK.A.toGrp ⟶ Standard.leviScheme i ν J.val :=
    CK.g ≫ standardLeviTorusFactor i ν J.val (Standard.isRepresentedBy_leviHom i ν J.val)
  have hφ : φ ≫ leviInclusion i ν hG hi hν h = CK.a := by
    apply (Standard.isRepresentedBy_leviHom i ν K.val).hom_ext
    rw [Category.assoc, leviInclusion_comp, Category.assoc, standardLeviTorusFactor_comp,
      CK.factor]
  have hφc : IsCentral φ :=
    IsCentral.of_comp (mono_leviInclusion i ν hG hi hν h) (by rw [hφ]; exact CK.ha.1.2)
  have : IsAffineHom (Standard.leviScheme i ν J.val).X.hom :=
    (isConnectedReductive_levi i ν hG hi hν J).isAffineHom
  have hex := CJ.ha.exists_factor CK.ha.1.1.1 hφc
  let f := hex.choose
  have hf : f ≫ CJ.a = φ := hex.choose_spec
  have hmi : Mono i.hom.hom := by
    have := hi.isSplitSubtorus.mono
    exact Over.mono_of_mono_left _
  exact {
    P := Q
    N := U
    p := q
    m := lQ
    n := rQ
    hp := isParabolicSubgroup_of_range_eq_dynamicParabolic hH q hqc ψ hQ.2
    hm := hlevi
    hn := hrad.leviSubgroup
    hmul := hmul
    levi_eq := hlQ
    range_eq := hQ.2
    e := Additive.ofMul f
    e_comp := by
      change f ≫ CJ.a ≫ _ = _
      rw [← Category.assoc, hf, hφ]
    e_g := by
      change f ≫ CJ.g = CK.g
      apply SubgroupFunctor.IsRepresentedBy.hom_ext
        (⟨hmi, rfl⟩ : (SubgroupFunctor.range i).IsRepresentedBy i)
      rw [Category.assoc, CJ.factor, ← Category.assoc, hf, Category.assoc,
        standardLeviTorusFactor_comp] }

namespace NestedData

variable {i ν hG hi hν} {h : J.val ⊆ K.val} (D : NestedData i ν hG hi hν h)

/-- The inner Levi followed by the outer ambient Levi map is the fine ambient Levi map. -/
theorem levi_comp :
    D.m ≫ D.p ≫ (OppositeStandardJacquetFamily.datum i ν hG hi hν K).l ≫
        (OppositeStandardJacquetFamily.datum i ν hG hi hν K).p =
      (OppositeStandardJacquetFamily.datum i ν hG hi hν J).l ≫
        (OppositeStandardJacquetFamily.datum i ν hG hi hν J).p := by
  refine (congrArg (D.m ≫ D.p ≫ ·)
    (OppositeStandardJacquetFamily.datum_l_comp_p i ν hG hi hν K)).trans ?_
  rw [OppositeStandardJacquetFamily.datum_l_comp_p, ← Category.assoc, D.levi_eq,
    leviInclusion_comp]

/-- On every test scheme, the inner parabolic is the intersection of the
standard Levi of `K` with the opposite parabolic of `J`. -/
theorem range_comp :
    SubgroupFunctor.range (D.p ≫ Standard.leviHom i ν K.val) =
      SubgroupFunctor.range (Standard.leviHom i ν K.val) ⊓
        SubgroupFunctor.range (OppositeStandardJacquetFamily.datum i ν hG hi hν J).p := by
  rw [RepresentedParabolicLeviIntersection.range_comp_eq_map, D.range_eq,
    ← Dynamic.range_inf_parabolic _ _ (Standard.isClosedSubgroup_leviHom i ν K.val),
    innerCocharacter_comp, range_opposite_p_eq]

/-- The rational points of the inner parabolic are the rational points of the
standard Levi of `K` lying in the opposite parabolic of `J`. -/
theorem inner_eq :
    pointImage (D.p ≫ (OppositeStandardJacquetFamily.datum i ν hG hi hν K).l ≫
        (OppositeStandardJacquetFamily.datum i ν hG hi hν K).p) =
      pointImage ((OppositeStandardJacquetFamily.datum i ν hG hi hν K).l ≫
          (OppositeStandardJacquetFamily.datum i ν hG hi hν K).p) ⊓
        pointImage (OppositeStandardJacquetFamily.datum i ν hG hi hν J).p := by
  rw [show D.p ≫ (OppositeStandardJacquetFamily.datum i ν hG hi hν K).l ≫
      (OppositeStandardJacquetFamily.datum i ν hG hi hν K).p =
      D.p ≫ Standard.leviHom i ν K.val from congrArg (D.p ≫ ·)
        (OppositeStandardJacquetFamily.datum_l_comp_p i ν hG hi hν K),
    OppositeStandardJacquetFamily.datum_l_comp_p]
  exact congrArg
    (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    D.range_comp

/-- The split-component morphism is compatible with the inner Levi and parabolic. -/
theorem e_comp_inner :
    CommGroupScheme.groupHom D.e ≫
        (OppositeStandardJacquetFamily.component i ν hG hi hν J).a ≫ D.m ≫ D.p =
      (OppositeStandardJacquetFamily.component i ν hG hi hν K).a := by
  rw [D.levi_eq, D.e_comp]

end NestedData

end Nesting

end Langlands.Aubert.General.RepresentedParabolic.OppositeStandardJacquetFamily
