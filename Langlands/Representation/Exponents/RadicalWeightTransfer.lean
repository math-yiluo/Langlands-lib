import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.GroupScheme.Rational.IntrinsicRootCone
import Langlands.GroupScheme.Rational.ActionWeightTransport
import Langlands.GroupScheme.Rational.SubgroupRelativeRootComparison
import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.Rational.RootKernelIdentityComparison
import Langlands.GroupScheme.Rational.RelativeCentralDirections

/-! # Radical weights of a geometric-lemma intersection datum

For intersection data `D` of a double coset `P z Q`, conjugation by `z⁻¹` carries the
radical `N' = M ∩ zUz⁻¹` of the parabolic `P'` of `M` into the radical `U` of `Q`. Hence a
weight of a torus of `M' = φ(L')` on the tangent space of `N'` restricts to a weight of a
torus of `L` on the tangent space of `U`. For split components this sends intrinsic positive
roots of `P'` to intrinsic positive roots of `Q`, and the cone of `P'` into the cone of `Q`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {K H G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]

/-- Conjugation weights on the image of a subgroup do not change when the ambient group
is embedded by a monomorphism `j`. -/
theorem actionWeightSupport_conjugation_range_comp (i : S.toGrp ⟶ H) (g : K ⟶ H)
    (j : H ⟶ G) [Mono j.hom.hom] :
    actionWeightSupport (AutomorphicAction.conjugation (i ≫ j))
        (SubgroupFunctor.range (g ≫ j)) =
      actionWeightSupport (AutomorphicAction.conjugation i) (SubgroupFunctor.range g) := by
  have h := actionWeightSupport_map j inferInstance (AutomorphicAction.conjugation i)
    (AutomorphicAction.conjugation (i ≫ j)) (conjugation_act_comp i j)
    (SubgroupFunctor.range g)
  rw [← SubgroupFunctor.map_top g, SubgroupFunctor.map_comp] at h
  simpa only [SubgroupFunctor.map_top] using h

/-- Precomposing the acting torus with `τ` precomposes every conjugation weight with `τ`. -/
theorem comp_mem_actionWeightSupport_conjugation (i : S.toGrp ⟶ G) (τ : S' ⟶ S)
    {F : SubgroupFunctor G} {χ : characterLattice S}
    (hχ : χ ∈ actionWeightSupport (AutomorphicAction.conjugation i) F) :
    τ ≫ χ ∈ actionWeightSupport
      (AutomorphicAction.conjugation (CommGroupScheme.groupHom τ ≫ i)) F := by
  obtain ⟨X, hX, hXw, hXF⟩ := hχ
  rw [actionWeightSpace_conjugation] at hXw
  refine ⟨X, hX, ?_, hXF⟩
  rw [actionWeightSpace_conjugation]
  exact mem_weightSpace_precomp_torus_hom i χ τ hXw

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RelativeRoot RealTorusSpace

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
  [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
  {A A' : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ L} {a' : A'.toGrp ⟶ D.L'}

/-- Let `τ : A ⟶ A'` with `τ ≫ a' ≫ (L' → L) = a`. A weight of `A'`, acting on `M`
through `φ`, on the tangent space of `N' = M ∩ zUz⁻¹` restricts along `τ` to a weight
of `A` on the tangent space of `U`. -/
theorem comp_mem_actionWeightSupport_radical (τ : A ⟶ A')
    (hτ : CommGroupScheme.groupHom τ ≫ a' ≫ D.lQ' ≫ D.q' = a)
    {β : characterLattice A'}
    (hβ : β ∈ actionWeightSupport
      (AutomorphicAction.conjugation (a' ≫ D.φ.hom ≫ D.l' ≫ D.p'))
      (SubgroupFunctor.range (D.r' ≫ D.p'))) :
    τ ≫ β ∈ actionWeightSupport (AutomorphicAction.conjugation (a ≫ lQ ≫ q))
      (SubgroupFunctor.range (rQ ≫ q)) := by
  have : Mono (l ≫ p).hom.hom.left :=
    (hl.isClosedSubgroup.comp hp.isClosedSubgroup).mono
  have : Mono (l ≫ p).hom.hom := Over.mono_of_mono_left _
  have : Mono (G.innerIso z).hom.hom.hom.left :=
    (IsClosedSubgroup.of_iso (G.innerIso z)).mono
  have : Mono (G.innerIso z).hom.hom.hom := Over.mono_of_mono_left _
  -- Push the weight from `M` to `G`.
  rw [← actionWeightSupport_conjugation_range_comp _ _ (l ≫ p)] at hβ
  -- Enlarge `N'` to `zUz⁻¹`.
  have hle : SubgroupFunctor.range ((D.r' ≫ D.p') ≫ l ≫ p) ≤
      SubgroupFunctor.range (rQ ≫ q ≫ (G.innerIso z).hom) := by
    have h := D.radical_eq
    simp only [Category.assoc] at h ⊢
    rw [h]
    exact SubgroupFunctor.le_def.mpr fun T => by
      rw [SubgroupFunctor.inf_carrier]
      exact inf_le_right
  have hβ' := actionWeightSupport_mono _ hle hβ
  -- Conjugate by `z⁻¹`.
  have hφ : (a' ≫ D.φ.hom ≫ D.l' ≫ D.p') ≫ l ≫ p =
      (a' ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q) ≫ (G.innerIso z).hom := by
    simp only [Category.assoc]
    rw [D.φ_comp]
  rw [hφ, show rQ ≫ q ≫ (G.innerIso z).hom = (rQ ≫ q) ≫ (G.innerIso z).hom from
    (Category.assoc _ _ _).symm, actionWeightSupport_conjugation_range_comp] at hβ'
  -- Restrict the acting torus along `τ`.
  have h := comp_mem_actionWeightSupport_conjugation _ τ hβ'
  rwa [show CommGroupScheme.groupHom τ ≫ a' ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q = a ≫ lQ ≫ q by
    rw [← hτ]; simp only [Category.assoc]] at h

section Presentations

variable [Smooth G.X.hom] [Smooth M.X.hom]

/-- Intrinsic positive roots of the parabolic `P'` of `M`, for the split component
`a' ≫ φ` of `M'`, restrict along `τ` to intrinsic positive roots of `Q`. -/
theorem comp_mem_intrinsicPositiveRoots (τ : A ⟶ A')
    (hτ : CommGroupScheme.groupHom τ ≫ a' ≫ D.lQ' ≫ D.q' = a)
    (presQ : ParabolicRootPresentation q lQ a)
    (presM : ParabolicRootPresentation D.p' D.l' (a' ≫ D.φ.hom))
    {β : characterLattice A'} (hβ : β ∈ presM.intrinsicPositiveRoots) :
    τ ≫ β ∈ presQ.intrinsicPositiveRoots := by
  rw [presM.intrinsicPositiveRoots_eq_subgroupRelativeRoots D.hr'] at hβ
  have h := D.comp_mem_actionWeightSupport_radical τ hτ (by simpa only [Category.assoc] using hβ.1)
  rw [presQ.range_comp_radical_eq hrQ,
    actionWeightSupport_dynamicUnipotent _ presQ.isCompatible.splitComponent.1.isSplitSubtorus.1]
    at h
  exact h

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType M.X.hom]

/-- Restriction along `τ` maps the cone of the parabolic `P'` of `M` into the cone of `Q`,
when the ambient relative roots of the presentation of `Q` are closed under negation. -/
theorem restrictReal_mem_nonnegCone (τ : A ⟶ A')
    (hτ : CommGroupScheme.groupHom τ ≫ a' ≫ D.lQ' ≫ D.q' = a)
    (presQ : ParabolicRootPresentation q lQ a)
    (presM : ParabolicRootPresentation D.p' D.l' (a' ≫ D.φ.hom))
    (hneg : ∀ α ∈ relativeRoots presQ.data.i, -α ∈ relativeRoots presQ.data.i)
    {x : Vstar A'} (hx : x ∈ presM.nonnegCone) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom τ) x ∈ presQ.nonnegCone := by
  change x ∈ restrictedRootNonnegCone _ _ _ _ _ at hx
  rw [restrictedRootNonnegCone_eq_hull, SetLike.mem_coe] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨β, hβ, rfl⟩ := presM.restrictedRoots_subset_image_intrinsicPositiveRoots hy
    rw [rationalCharacterRestrictReal_tmul]
    exact presQ.one_tmul_mem_nonnegCone_of_mem_intrinsicPositiveRoots hneg
      (D.comp_mem_intrinsicPositiveRoots τ hτ presQ presM hβ)
  | zero =>
    rw [map_zero]
    exact presQ.zero_mem_nonnegCone
  | add y w _ _ hy hw =>
    rw [map_add]
    exact presQ.add_mem_nonnegCone hy hw
  | smul c y _ hy =>
    rw [show c • y = (c : ℝ) • y from rfl, map_smul]
    exact presQ.smul_mem_nonnegCone c.2 hy

end Presentations

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
