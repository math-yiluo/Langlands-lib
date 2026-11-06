import Langlands.GroupScheme.Absolute.SplitTorusDynamicDescent
import Langlands.GroupScheme.Absolute.RegularCocharacterDescent
import Langlands.GroupScheme.Absolute.BorelDynamicConjugacy
import Langlands.GroupScheme.Absolute.BorelContaining
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement
import Langlands.GroupScheme.Reductive.FieldExtensionStatement
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable

/-! # Borel subgroups through a split maximal torus: passage to the algebraic closure

A Borel subgroup `B` through a split maximal torus `j : T ⟶ G` over a field `k` represents
`P(ν ≫ j)` for a regular cocharacter `ν` of `T` (conditional on structure inputs). The proof
passes to the algebraic closure `k̄`, places `B_{k̄}` in a Borel subgroup of `G_{k̄}`, identifies
that Borel subgroup with a dynamic parabolic by conjugacy, and descends the cocharacter. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

-- `ac[k]`: the morphism `Spec k̄ ⟶ Spec k`.
local notation "ac[" k "]" => toAlgebraicClosure k

-- `pt[k]`: the algebraic closure `Spec k̄ ⟶ Spec k` as a test scheme over `Spec k`.
set_option quotPrecheck false in
local notation "pt[" k "]" =>
  (Over.map (toAlgebraicClosure k)).obj (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))

variable {k : Type u} [Field k]

/-- A group scheme over `k` is solvable exactly when its base change to `k̄` is solvable. -/
theorem isSolvableGroupScheme_baseChange_iff (H : GroupScheme (Spec (CommRingCat.of k))) :
    IsSolvableGroupScheme ((GroupScheme.baseChange ac[k]).obj H) ↔
      IsSolvableGroupScheme H :=
  isSolvableGroupScheme_iff_isSolvable_points (k := AlgebraicClosure k) _

/-- The base change to `k̄` of a Borel subgroup is a closed smooth connected solvable subgroup. -/
theorem IsBorelSubgroup.isAdmissible_baseChange {B G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {i : B ⟶ G} (hi : IsBorelSubgroup i) :
    BorelExistence.IsAdmissible ((GroupScheme.baseChange ac[k]).map i) := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have := hi.smooth
  have := hi.connectedSpace
  have : IsAffineHom B.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  exact ⟨hi.isClosedSubgroup.baseChange _, inferInstance,
    B.connectedSpace_baseChange_of_smooth_affine _,
    (isSolvableGroupScheme_baseChange_iff B).2 hi.isSolvableGroupScheme⟩

/-! ### Borel subgroups through a split maximal torus -/

section Glue

variable {G B : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The base change of a composite cocharacter `ν ≫ j`. -/
theorem baseChangeCocharacter_comp {S S' : Scheme.{u}} (b : S' ⟶ S) {H G : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ H) (j : H ⟶ G) :
    Dynamic.baseChangeCocharacter b (χ ≫ j) =
      Dynamic.baseChangeCocharacter b χ ≫ (GroupScheme.baseChange b).map j :=
  Dynamic.baseChangeCocharacter_comp b χ j

/-- **Passage to the algebraic closure (conditional on structure inputs).** Let `G` be connected
reductive over `k`, `j : T ⟶ G` a maximal torus with `T` split and `i : B ⟶ G` a Borel subgroup
through which `j` factors. Assume Borel conjugacy, maximal-torus conjugacy, the base-change
statements for connected reductive groups and maximal tori, and a Borel subgroup of `G_{k̄}`
representing `P(ν₀ ≫ j_{k̄})` for some cocharacter `ν₀` of `T_{k̄}`. Then there is a cocharacter
`ν` of `T` such that every `k̄`-point of `B` lies in `P(ν ≫ j)` and the `k̄`-points of
`P(ν ≫ j)` form a solvable group. -/
theorem exists_cocharacter_algebraicClosurePoints
    (hBC : BorelConjugacyStatement.{u}) (hTC : MaximalTorusConjugacyStatement.{u})
    (hFE : ConnectedReductiveFieldExtensionStatement.{u})
    (hMT : MaximalTorusBaseChangeStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    (hj : IsMaximalTorus j) (i : B ⟶ G) (f : T.toGrp ⟶ B) (hB : IsBorelSubgroup i)
    (hf : f ≫ i = j)
    (ν₀ : cocharacterLattice ((CommGroupScheme.baseChange ac[k]).obj T))
    {P₀ : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k)))}
    (i₀ : P₀ ⟶ (GroupScheme.baseChange ac[k]).obj G) (hP₀ : IsBorelSubgroup i₀)
    (hrep₀ : (Dynamic.parabolic (CommGroupScheme.groupHom ν₀ ≫
      (GroupScheme.baseChange ac[k]).map j)).IsRepresentedBy i₀) :
    ∃ ν : cocharacterLattice T,
      (∀ x : pt[k] ⟶ B.X, x ≫ i.hom.hom ∈
        (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).carrier pt[k]) ∧
      Group.IsSolvable ((Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).carrier pt[k]) := by
  have := hG.isAffineHom
  have := hG.smooth
  have hGK : IsConnectedReductive ((GroupScheme.baseChange ac[k]).obj G) := hFE k _ G hG
  have := hGK.isAffineHom
  have := hGK.smooth
  have := hGK.connectedSpace
  have hjK : IsMaximalTorus (T := (CommGroupScheme.baseChange ac[k]).obj T)
      ((GroupScheme.baseChange ac[k]).map j) :=
    (hMT k _ G T j hT.isTorus hj.2.1).1 hj
  -- `B_{k̄}` lies in a Borel subgroup `i'` of `G_{k̄}`.
  obtain ⟨B', i', g, hB', hg⟩ := BorelExistence.exists_isBorelSubgroup_containing
    ((GroupScheme.baseChange ac[k]).map i) hB.isAdmissible_baseChange
  have hfg : ((GroupScheme.baseChange ac[k]).map f ≫ g) ≫ i' =
      (GroupScheme.baseChange ac[k]).map j := by
    rw [Category.assoc, hg, ← Functor.map_comp, hf]
  -- `i'` is a dynamic parabolic of a cocharacter of `T_{k̄}`.
  obtain ⟨σ, hσ⟩ := exists_isRepresentedBy_parabolic_of_isBorelSubgroup hBC hTC _ hjK ν₀ i₀ hP₀
    hrep₀ i' _ hB' hfg
  -- That cocharacter descends to `T`.
  obtain ⟨ν, hν, -⟩ :=
    hT.existsUnique_baseChangeCocharacter ac[k] T (CommGroupScheme.groupHom (ν₀ ≫ σ.hom))
  have hpar : SubgroupFunctor.range i' =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).baseChange ac[k] := by
    rw [hσ.2, ← Dynamic.parabolic_baseChange, baseChangeCocharacter_comp, hν]
    rfl
  refine ⟨ν, fun x => ?_, ?_⟩
  · -- A `k̄`-point of `B` is a rational point of `B_{k̄}`, hence of `B'`.
    obtain ⟨x', rfl⟩ := (baseChangePointsEquiv ac[k] B _).surjective x
    rw [← baseChangePointsEquiv_comp]
    change x' ≫ ((GroupScheme.baseChange ac[k]).map i).hom.hom ∈
      ((Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).baseChange ac[k]).carrier _
    rw [← hpar, ← hg]
    exact SubgroupFunctor.mem_range.2 ⟨x' ≫ g.hom.hom, by rw [Grp.comp_hom_hom, Category.assoc]⟩
  · -- The rational points of `B'` surject onto those of `P(ν ≫ j)_{k̄}`.
    let U : Over (Spec (CommRingCat.of (AlgebraicClosure k))) := Over.mk (𝟙 _)
    have hsolB' : Group.IsSolvable ((yonedaGrp.obj B').obj (op U)) :=
      (isSolvableGroupScheme_iff_isSolvable_points B').1 hB'.isSolvableGroupScheme
    have hsolR : Group.IsSolvable ((SubgroupFunctor.range i').carrier U) :=
      Group.isSolvable_of_surjective (f := ((yonedaGrp.map i').app (op U)).hom.rangeRestrict)
        (MonoidHom.rangeRestrict_surjective _)
    rw [hpar] at hsolR
    let e := SubgroupFunctor.baseChangeCarrierEquiv ac[k]
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)) U
    exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

/-- **Borel subgroups through a split maximal torus are dynamic parabolics of regular
cocharacters (conditional on structure inputs).** Let `G` be connected reductive over a field
`k`, `j : T ⟶ G` a maximal torus with `T` split and `i : B ⟶ G` a Borel subgroup through which
`j` factors. Assume the listed structure statements and, over every algebraically closed field,
clause 1 of `RegularCocharacterBorelStatement`. Then there is a regular cocharacter `ν` of `T`
such that `i` represents `P(ν ≫ j)`. -/
theorem exists_isRegular_isRepresentedBy_of_isBorelSubgroup (hLie : DynamicLieStatement.{u})
    (hSm : DynamicSmoothStatement.{u}) (hCo : DynamicConnectedStatement.{u})
    (hNeg : RelativeRootNegationStatement.{u}) (hobs : RankOneSolvableObstructionStatement.{u})
    (hBC : BorelConjugacyStatement.{u}) (hTC : MaximalTorusConjugacyStatement.{u})
    (hFE : ConnectedReductiveFieldExtensionStatement.{u})
    (hMT : MaximalTorusBaseChangeStatement.{u})
    (h1 : ∀ (K : Type u) [Field K] [IsAlgClosed K] (G : GroupScheme (Spec (CommRingCat.of K)))
      (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of K)))
      (j : T.toGrp ⟶ G), IsSplitTorus T.toGrp → IsMaximalTorus j →
        haveI := hG.isAffineHom
        ∀ ν : cocharacterLattice T, IsRegularCocharacter j ν →
          ∀ (B : GroupScheme (Spec (CommRingCat.of K))) (i : B ⟶ G), IsClosedSubgroup i →
            (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i →
              IsBorelSubgroup i)
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    (hj : IsMaximalTorus j) (i : B ⟶ G) (f : T.toGrp ⟶ B) (hB : IsBorelSubgroup i)
    (hf : f ≫ i = j) :
    haveI := hG.isAffineHom
    ∃ ν : cocharacterLattice T, IsRegularCocharacter j ν ∧
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i := by
  have := hG.isAffineHom
  have := hG.smooth
  have hGK : IsConnectedReductive ((GroupScheme.baseChange ac[k]).obj G) := hFE k _ G hG
  have := hGK.isAffineHom
  have := hGK.smooth
  have : IsAffine ((GroupScheme.baseChange ac[k]).obj G).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange ac[k]).obj G).X.hom
  have hTK : IsSplitTorus ((CommGroupScheme.baseChange ac[k]).obj T).toGrp := hT.baseChange ac[k]
  have hjK : IsMaximalTorus (T := (CommGroupScheme.baseChange ac[k]).obj T)
      ((GroupScheme.baseChange ac[k]).map j) :=
    (hMT k _ G T j hT.isTorus hj.2.1).1 hj
  -- A regular cocharacter `ν₀` of `T_{k̄}` gives a Borel subgroup `P(ν₀ ≫ j_{k̄})` by clause 1.
  obtain ⟨ν₀, hν₀⟩ := hTK.exists_regularCocharacter ((GroupScheme.baseChange ac[k]).map j)
    ((hTK.finite_weightSupport _).subset fun _ hχ => hχ.2)
  let χ₀ := CommGroupScheme.groupHom ν₀ ≫ (GroupScheme.baseChange ac[k]).map j
  have hP₀ := h1 _ _ hGK _ _ hTK hjK ν₀ hν₀ _ (Dynamic.Affine.parabolicHom χ₀)
    (Dynamic.Affine.isClosedSubgroup_parabolicHom χ₀)
    (Dynamic.Affine.isRepresentedBy_parabolicHom χ₀)
  obtain ⟨ν, hpt, hsol⟩ := exists_cocharacter_algebraicClosurePoints hBC hTC hFE hMT hG hT j hj i f
    hB hf ν₀ _ hP₀ (Dynamic.Affine.isRepresentedBy_parabolicHom χ₀)
  exact ⟨ν, isRegular_isRepresentedBy_of_algebraicClosurePoints hLie hSm hCo hNeg hobs hG hT j hj i
    f hB hf ν hpt hsol⟩

end Glue

end Langlands.GroupScheme
