import Langlands.GroupScheme.Rational.DynamicSemistandardIntersectionStatement
import Langlands.GroupScheme.Rational.LeviMultiplication
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalStatement
import Langlands.GroupScheme.Dynamic.CommonTorusIntersections
import Langlands.GroupScheme.Absolute.BorelStatement

/-! # Actual models for semistandard intersections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Actual closed subgroup models with an all-test decomposition. Structural
parabolicity, reductivity and geometric radical identification are separate. -/
structure ClosedDecompositionModel (P L U : SubgroupFunctor G) where
  parabolic : GroupScheme S
  levi : GroupScheme S
  unipotent : GroupScheme S
  parabolicHom : parabolic ⟶ G
  leviHom : levi ⟶ parabolic
  unipotentHom : unipotent ⟶ parabolic
  parabolic_rep : P.IsRepresentedBy parabolicHom
  levi_rep : L.IsRepresentedBy (leviHom ≫ parabolicHom)
  unipotent_rep : U.IsRepresentedBy (unipotentHom ≫ parabolicHom)
  parabolic_closed : IsClosedSubgroup parabolicHom
  levi_closed : IsClosedSubgroup leviHom
  unipotent_closed : IsClosedSubgroup unipotentHom
  multiplication_isIso : IsIso (subgroupMultiplication leviHom unipotentHom)
  pointwise : ∀ X : Over S,
    U.carrier X ≤ P.carrier X ∧ L.carrier X ≤ P.carrier X ∧
      ((U.carrier X).subgroupOf (P.carrier X)).Normal ∧
      ((U.carrier X).subgroupOf (P.carrier X)).IsComplement'
        ((L.carrier X).subgroupOf (P.carrier X)) ∧
      (↑(P.carrier X) : Set (X ⟶ G.X)) =
        (↑(L.carrier X) : Set (X ⟶ G.X)) * (↑(U.carrier X) : Set (X ⟶ G.X))

/-- Reindex actual models along three equalities of all-test subgroup functors. -/
def ClosedDecompositionModel.reindex {P L U P' L' U' : SubgroupFunctor G}
    (d : ClosedDecompositionModel P L U) (hP : P = P') (hL : L = L') (hU : U = U') :
    ClosedDecompositionModel P' L' U' := by
  subst P'
  subst L'
  subst U'
  exact d

end SubgroupFunctor

namespace Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} {χ : (Gm S).toGrp ⟶ G}
  {P U : GroupScheme S} {p : P ⟶ G} {r : U ⟶ G}

/-- The actual inclusion of any represented identity-limit subgroup into a
represented dynamic parabolic. -/
def unipotentToParabolic (hP : (parabolic χ).IsRepresentedBy p)
    (hU : (unipotent χ).IsRepresentedBy r) : U ⟶ P :=
  hU.lift hP (fun X => Subgroup.inclusion (unipotent_le_parabolic χ X))
    (fun _ _ => rfl)

theorem unipotentToParabolic_comp (hP : (parabolic χ).IsRepresentedBy p)
    (hU : (unipotent χ).IsRepresentedBy r) :
    unipotentToParabolic hP hU ≫ p = r :=
  hU.lift_comp_eq hP _ (fun _ _ => rfl) (fun _ _ => rfl)

/-- The displayed Levi-first product on every test scheme. -/
theorem parabolic_eq_centralizer_mul_unipotent [IsSeparated G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) (X : Over S) :
    (↑((parabolic χ).carrier X) : Set (X ⟶ G.X)) =
      (↑((centralizer χ).carrier X) : Set (X ⟶ G.X)) *
        (↑((unipotent χ).carrier X) : Set (X ⟶ G.X)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨l, hl⟩ := exists_hasLimit χ hg
    have hz := hl.mem_centralizer χ
    have hu : l⁻¹ * g ∈ (unipotent χ).carrier X := by
      change HasLimit χ (l⁻¹ * g) 1
      simpa only [inv_mul_cancel] using
        ((hasLimit_of_mem_centralizer χ hz).inv χ).mul χ hl
    exact Set.mem_mul.mpr ⟨l, hz, l⁻¹ * g, hu, mul_inv_cancel_left l g⟩
  · rintro ⟨l, hl, u, hu, rfl⟩
    exact mul_mem (centralizer_le_parabolic χ X hl) (unipotent_le_parabolic χ X hu)

section Affine

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
    (χ : (Gm (Spec R)).toGrp ⟶ G)

/-- Chosen actual affine dynamic models, their compatible closed inclusions,
and their decomposition on every test scheme. -/
def affineDecompositionModel :
    SubgroupFunctor.ClosedDecompositionModel
      (parabolic χ) (centralizer χ) (unipotent χ) := by
  letI : IsAffineHom G.X.hom := isAffineHom_of_isAffine _
  let hP := Affine.isRepresentedBy_parabolicHom χ
  let hL := Affine.isRepresentedBy_centralizerHom χ
  let hU := Affine.isRepresentedBy_unipotentHom χ
  let l := centralizerToParabolic hP hL
  let r := unipotentToParabolic hP hU
  have hl : l ≫ Affine.parabolicHom χ = Affine.centralizerHom χ :=
    centralizerToParabolic_comp hP hL
  have hr : r ≫ Affine.parabolicHom χ = Affine.unipotentHom χ :=
    unipotentToParabolic_comp hP hU
  refine
    { parabolic := Affine.parabolicScheme χ
      levi := Affine.centralizerScheme χ
      unipotent := Affine.unipotentScheme χ
      parabolicHom := Affine.parabolicHom χ
      leviHom := l
      unipotentHom := r
      parabolic_rep := hP
      levi_rep := ?_
      unipotent_rep := ?_
      parabolic_closed := Affine.isClosedSubgroup_parabolicHom χ
      levi_closed := ?_
      unipotent_closed := ?_
      multiplication_isIso := isIso_subgroupMultiplication hP hL hU l r hl hr
      pointwise := ?_ }
  · rwa [hl]
  · rwa [hr]
  · apply IsClosedSubgroup.of_comp (Affine.isClosedSubgroup_parabolicHom χ)
    rw [hl]
    exact Affine.isClosedSubgroup_centralizerHom χ
  · apply IsClosedSubgroup.of_comp (Affine.isClosedSubgroup_parabolicHom χ)
    rw [hr]
    exact Affine.isClosedSubgroup_unipotentHom χ
  · intro X
    exact ⟨unipotent_le_parabolic χ X, centralizer_le_parabolic χ X,
      unipotent_subgroupOf_parabolic_normal χ X,
      isComplement'_unipotent_centralizer_of_isSeparated χ X,
      parabolic_eq_centralizer_mul_unipotent χ X⟩

end Affine

section CommonTorus

variable {S : Scheme.{u}} {G M : GroupScheme S} {T : CommGroupScheme S}
    (i : T.toGrp ⟶ G) (α β : (Gm S).toGrp ⟶ T.toGrp) {j : M ⟶ G}
    (hj : (centralizer (α ≫ i)).IsRepresentedBy j)

/-- The second cocharacter lifted through a representative of the first
centralizer, using the original common commutative group. -/
def intersectionCocharacter : (Gm S).toGrp ⟶ M :=
  β ≫ torusFactor i α hj

theorem intersectionCocharacter_comp :
    intersectionCocharacter i α β hj ≫ j = β ≫ i := by
  rw [intersectionCocharacter, Category.assoc, torusFactor_comp]

theorem intersection_dynamic_eq_comap (hjc : IsClosedSubgroup j) :
    parabolic (intersectionCocharacter i α β hj) = (parabolic (β ≫ i)).comap j ∧
    centralizer (intersectionCocharacter i α β hj) = (centralizer (β ≫ i)).comap j ∧
    unipotent (intersectionCocharacter i α β hj) = (unipotent (β ≫ i)).comap j := by
  have hcomp := intersectionCocharacter_comp i α β hj
  exact ⟨by rw [← hcomp]; exact parabolic_eq_comap_of_isClosedSubgroup _ j hjc,
    by rw [← hcomp]; exact centralizer_eq_comap_of_isClosedSubgroup _ j hjc,
    by rw [← hcomp]; exact unipotent_eq_comap_of_isClosedSubgroup _ j hjc⟩

end CommonTorus

/-- Actual closed models of the three intersection functors inside an affine
representative of the first centralizer, with compatible inclusions and the
all-test Levi decomposition. -/
def commonTorusIntersectionModel {R : CommRingCat.{u}}
    {G M : GroupScheme (Spec R)} [IsAffine M.X.left]
    {T : CommGroupScheme (Spec R)} (i : T.toGrp ⟶ G)
    (α β : (Gm (Spec R)).toGrp ⟶ T.toGrp) {j : M ⟶ G}
    (hj : (centralizer (α ≫ i)).IsRepresentedBy j) (hjc : IsClosedSubgroup j) :
    SubgroupFunctor.ClosedDecompositionModel
      ((parabolic (β ≫ i)).comap j)
      ((centralizer (β ≫ i)).comap j)
      ((unipotent (β ≫ i)).comap j) :=
  let h := intersection_dynamic_eq_comap i α β hj hjc
  (affineDecompositionModel (intersectionCocharacter i α β hj)).reindex h.1 h.2.1 h.2.2

end Dynamic

namespace SubgroupFunctor

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {P L U : SubgroupFunctor G}

/-- The exact structural conclusions complete a closed decomposition model. -/
theorem ClosedDecompositionModel.isParabolicWithLeviAndRadical
    (d : ClosedDecompositionModel P L U)
    (hP : IsParabolicSubgroup d.parabolicHom)
    (hL : IsConnectedReductive d.levi)
    (hU : IsGeometricUnipotentRadical d.unipotentHom) :
    IsParabolicWithLeviAndRadical P L U :=
  ⟨d.parabolic, d.levi, d.unipotent, d.parabolicHom, d.leviHom, d.unipotentHom,
    d.parabolic_rep, hP, d.levi_closed, hL, d.levi_rep.2, hU,
    d.unipotent_rep.2, d.pointwise⟩

end SubgroupFunctor

namespace Dynamic

/-- Structural reduction for a single dynamic parabolic. All three structural
inputs remain explicit proof obligations. -/
theorem isParabolicWithLeviAndRadical_of_structural
    (hP : ParabolicDynamicStatement.{u})
    (hL : DynamicCentralizerReductiveStatement.{u})
    (hU : DynamicGeometricUnipotentRadicalStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    SubgroupFunctor.IsParabolicWithLeviAndRadical
      (parabolic χ) (centralizer χ) (unipotent χ) := by
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let d := affineDecompositionModel χ
  exact d.isParabolicWithLeviAndRadical
    ((hP k G hG d.parabolic d.parabolicHom d.parabolic_closed).mpr
      ⟨χ, d.parabolic_rep.2⟩)
    (hL k G hG χ d.levi (d.leviHom ≫ d.parabolicHom)
      (d.levi_closed.comp d.parabolic_closed) d.levi_rep)
    (hU k G hG χ d.parabolic d.unipotent d.parabolicHom d.unipotentHom
      d.parabolic_rep d.unipotent_rep)

end Dynamic

/-- The remaining general semistandard theorem reduces to the three genuine
structural inputs, without additional intersection or nesting premises. -/
theorem dynamicSemistandardIntersection_of_structural
    (hP : ParabolicDynamicStatement.{u})
    (hL : DynamicCentralizerReductiveStatement.{u})
    (hU : DynamicGeometricUnipotentRadicalStatement.{u}) :
    DynamicSemistandardIntersectionStatement.{u} := by
  intro k _ G hG T i hi α β
  dsimp only
  intro M j hj hjc
  have hM := hL k G hG (CommGroupScheme.groupHom α ≫ i) M j hjc hj
  have hcomp := Dynamic.intersection_dynamic_eq_comap i
    (CommGroupScheme.groupHom α) (CommGroupScheme.groupHom β) hj hjc
  have hstructure := Dynamic.isParabolicWithLeviAndRadical_of_structural hP hL hU hM
    (Dynamic.intersectionCocharacter i (CommGroupScheme.groupHom α)
      (CommGroupScheme.groupHom β) hj)
  rw [hcomp.1, hcomp.2.1, hcomp.2.2] at hstructure
  exact ⟨hstructure, Dynamic.semistandardIntersectionProducts hG i α β,
    hi.exists_lift_to_centralizer_parabolic α β hj hjc⟩

end Langlands.GroupScheme
