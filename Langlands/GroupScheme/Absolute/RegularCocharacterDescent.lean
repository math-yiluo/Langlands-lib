import Langlands.GroupScheme.Absolute.RegularCocharacterMaximal
import Langlands.GroupScheme.Absolute.RankOneSolvableStatement
import Langlands.GroupScheme.Absolute.BorelExistenceCoordinates
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

/-! # Borel subgroups through a split maximal torus: descent from `k̄`-points

A Borel subgroup `B` through a split maximal torus `j : T ⟶ G` represents `P(ν ≫ j)` for a
regular `ν` once the `k̄`-points of `B` lie in `P(ν ≫ j)` and the `k̄`-points of `P(ν ≫ j)` form
a solvable group (conditional on structure inputs). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

-- `pt[k]`: the algebraic closure `Spec k̄ ⟶ Spec k` as a test scheme over `Spec k`.
set_option quotPrecheck false in
local notation "pt[" k "]" =>
  (Over.map (toAlgebraicClosure k)).obj (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))

variable {k : Type u} [Field k]

/-! ### Containment of subgroups from `k̄`-points -/

section Descent

variable {B P G : GroupScheme (Spec (CommRingCat.of k))}

/-- If every `k̄`-point of the smooth group `B` maps under `i` into the points of `iP`, then every
global function on `G` vanishing on `P` vanishes on `B`. -/
theorem coordinateKernel_le_of_algebraicClosurePoints [Smooth B.X.hom] (i : B ⟶ G)
    (iP : P ⟶ G)
    (h : ∀ x : pt[k] ⟶ B.X, x ≫ i.hom.hom ∈ (SubgroupFunctor.range iP).carrier pt[k]) :
    BorelExistence.coordinateKernel iP ≤ BorelExistence.coordinateKernel i := by
  intro a ha
  change iP.hom.hom.left.appTop a = 0 at ha
  change i.hom.hom.left.appTop a = 0
  set s := i.hom.hom.left.appTop a with hs
  have : IsReduced B.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k B.X.left
      B.X.hom
  have : IsSeparated (AffineLine.scheme (Spec (CommRingCat.of k))).hom := by
    change IsSeparated (𝔸(PUnit; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
    infer_instance
  let φ : NeronModelInfra.SchemeHomOver B.X.hom (AffineLine.scheme (Spec (CommRingCat.of k))).hom :=
    ⟨((AffineLine.homEquiv B.X).symm s).left, Over.w _⟩
  let ψ : NeronModelInfra.SchemeHomOver B.X.hom (AffineLine.scheme (Spec (CommRingCat.of k))).hom :=
    ⟨((AffineLine.homEquiv B.X).symm 0).left, Over.w _⟩
  have hφψ : φ = ψ := by
    refine SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat (R := k) k
      (AlgebraicClosure k) φ ψ fun x => ?_
    let x' : pt[k] ⟶ B.X := Over.homMk x.1 (by simpa using x.2)
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 (h x')
    have hl : x'.left ≫ i.hom.hom.left = y.left ≫ iP.hom.hom.left :=
      (congrArg (fun m => m.left) hy).symm
    have key : (x'.left ≫ i.hom.hom.left).appTop a = (y.left ≫ iP.hom.hom.left).appTop a := by
      rw [hl]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      CommRingCat.comp_apply, ha, map_zero, ← hs] at key
    have hx : x' ≫ (AffineLine.homEquiv B.X).symm s = x' ≫ (AffineLine.homEquiv B.X).symm 0 := by
      apply AffineLine.hom_ext
      rw [AffineLine.homEquiv_comp, AffineLine.homEquiv_comp, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, map_zero]
      exact key
    exact congrArg (fun m => m.left) hx
  have h' : (AffineLine.homEquiv B.X).symm s = (AffineLine.homEquiv B.X).symm 0 :=
    Over.OverMorphism.ext (congrArg Subtype.val hφψ)
  exact (AffineLine.homEquiv B.X).symm.injective h'

/-- **Containment from `k̄`-points.** Let `G` be affine over a field `k`, `i : B ⟶ G` a
homomorphism from a smooth group and `iP : P ⟶ G` a closed subgroup. If every `k̄`-point of `B`
maps into `P`, then the points of `B` lie in those of `P` on every test scheme. -/
theorem range_le_of_algebraicClosurePoints [IsAffineHom G.X.hom] [Smooth B.X.hom] (i : B ⟶ G)
    (iP : P ⟶ G) (hP : IsClosedSubgroup iP)
    (h : ∀ x : pt[k] ⟶ B.X, x ≫ i.hom.hom ∈ (SubgroupFunctor.range iP).carrier pt[k]) :
    SubgroupFunctor.range i ≤ SubgroupFunctor.range iP := by
  have : IsClosedImmersion iP.hom.hom.left := hP
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hker : iP.hom.hom.left.ker ≤ i.hom.hom.left.ker := by
    rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
    refine Scheme.IdealSheafData.le_of_isAffine ?_
    simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
    exact Ideal.map_mono (coordinateKernel_le_of_algebraicClosurePoints i iP h)
  have hℓ : IsClosedImmersion.lift iP.hom.hom.left i.hom.hom.left hker ≫ iP.hom.hom.left =
      i.hom.hom.left := IsClosedImmersion.lift_fac _ _ _
  intro U x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  refine SubgroupFunctor.mem_range.2
    ⟨Over.homMk (t.left ≫ IsClosedImmersion.lift iP.hom.hom.left i.hom.hom.left hker) ?_, ?_⟩
  · rw [← Over.w iP.hom.hom, Category.assoc, reassoc_of% hℓ, Over.w i.hom.hom, Over.w t]
  · apply Over.OverMorphism.ext
    change (t.left ≫ IsClosedImmersion.lift iP.hom.hom.left i.hom.hom.left hker) ≫
      iP.hom.hom.left = t.left ≫ i.hom.hom.left
    rw [Category.assoc, hℓ]

/-- If `iP : P ⟶ G` represents `F` and the `k̄`-points of `F` form a solvable group, then `P` is
solvable. -/
theorem isSolvableGroupScheme_of_isRepresentedBy {F : SubgroupFunctor G} {iP : P ⟶ G}
    (hrep : F.IsRepresentedBy iP) (hsol : Group.IsSolvable (F.carrier pt[k])) :
    IsSolvableGroupScheme P := by
  have : Mono iP.hom.hom := hrep.1
  let ρ : (pt[k] ⟶ P.X) →* F.carrier pt[k] :=
    MonoidHom.codRestrict ((yonedaGrp.map iP).app (op pt[k])).hom (F.carrier pt[k])
      fun y => by
        rw [← hrep.2]
        exact ⟨y, rfl⟩
  have hρ : Function.Injective ρ := fun y y' hyy' =>
    (cancel_mono iP.hom.hom).1 (congrArg Subtype.val hyy')
  have : Group.IsSolvable (pt[k] ⟶ P.X) := Group.isSolvable_of_isSolvable_injective hρ
  exact Group.isSolvable_of_isSolvable_injective
    (f := (baseChangePointsEquiv (toAlgebraicClosure k) P
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))).toMonoidHom)
    (baseChangePointsEquiv (toAlgebraicClosure k) P _).injective

end Descent

/-! ### Borel subgroups contained in `P(ν)` on `k̄`-points -/

section Assembly

variable {G : GroupScheme (Spec (CommRingCat.of k))} {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {B : GroupScheme (Spec (CommRingCat.of k))}

/-- **Borel subgroups through a split maximal torus, from `k̄`-points (conditional on structure
inputs).** Let `G` be connected reductive over `k`, `j : T ⟶ G` a maximal torus with `T` split,
`i : B ⟶ G` a Borel subgroup with `f ≫ i = j`, and `ν` a cocharacter of `T`. Suppose that every
`k̄`-point of `B` lies in `P(ν ≫ j)` and that the `k̄`-points of `P(ν ≫ j)` form a solvable group.
Then `ν` is regular and `i` represents `P(ν ≫ j)`. -/
theorem isRegular_isRepresentedBy_of_algebraicClosurePoints (hLie : DynamicLieStatement.{u})
    (hSm : DynamicSmoothStatement.{u}) (hCo : DynamicConnectedStatement.{u})
    (hNeg : RelativeRootNegationStatement.{u}) (hobs : RankOneSolvableObstructionStatement.{u})
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    (hj : IsMaximalTorus j) (i : B ⟶ G) (f : T.toGrp ⟶ B) (hB : IsBorelSubgroup i)
    (hf : f ≫ i = j) (ν : cocharacterLattice T)
    (hpt : ∀ x : pt[k] ⟶ B.X, x ≫ i.hom.hom ∈
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).carrier pt[k])
    (hsol : Group.IsSolvable
      ((Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).carrier pt[k])) :
    haveI := hG.isAffineHom
    IsRegularCocharacter j ν ∧
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i := by
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hB.smooth
  have hrepP := Dynamic.Affine.isRepresentedBy_parabolicHom (CommGroupScheme.groupHom ν ≫ j)
  have hclP := Dynamic.Affine.isClosedSubgroup_parabolicHom (CommGroupScheme.groupHom ν ≫ j)
  have hsmP := (hSm k G _ _ _).1 hrepP
  have hcoP := ((hCo k G _ _ _).2 inferInstance).1 hrepP
  have hsolP := isSolvableGroupScheme_of_isRepresentedBy hrepP hsol
  have hle : SubgroupFunctor.range i ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) := by
    rw [← hrepP.2]
    exact range_le_of_algebraicClosurePoints i _ hclP fun x => by
      rw [hrepP.2]
      exact hpt x
  obtain ⟨g, hg⟩ : ∃ g : B ⟶ Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ j),
      g ≫ Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ j) = i :=
    ⟨_, hrepP.liftOfLE_comp i hle⟩
  have : IsIso g := hB.maximal _ _ g hclP hsmP hcoP hsolP hg
  have hginv : (inv g).hom.hom ≫ i.hom.hom =
      (Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ j)).hom.hom := by
    calc (inv g).hom.hom ≫ i.hom.hom = (inv g ≫ i).hom.hom := rfl
      _ = (inv g ≫ g ≫ Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ j)).hom.hom := by
        rw [hg]
      _ = _ := by rw [IsIso.inv_hom_id_assoc]
  have hrep : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i := by
    have : IsClosedImmersion i.hom.hom.left := hB.isClosedSubgroup
    refine ⟨Over.mono_of_mono_left _, le_antisymm hle ?_⟩
    rw [← hrepP.2]
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    refine SubgroupFunctor.mem_range.2 ⟨y ≫ (inv g).hom.hom, ?_⟩
    rw [Category.assoc, hginv]
  refine ⟨fun α hα h0 => ?_, hrep⟩
  have hneg := neg_mem_roots_of_relativeRootNegation hNeg hG hT j hj α hα
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  obtain ⟨X', hX', hX'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hneg.2
  have hmem : ∀ β : characterLattice T, latticePairing T β ν = 0 →
      ∀ Y ∈ weightSpace j β, Y ∈ nonnegativeWeightSpan j ν := fun β hβ Y hY => by
    rw [nonnegativeWeightSpan_def]
    exact (le_iSup₂ (f := fun χ (_ : 0 ≤ latticePairing T χ ν) => weightSpace j χ) β hβ.ge) hY
  have h0' : latticePairing T (-α) ν = 0 := by
    rw [map_neg, LinearMap.neg_apply, h0, neg_zero]
  obtain ⟨Z, hZ⟩ :=
    exists_lieKernel_of_mem_nonnegativeWeightSpan hLie hT j ν i hrep X (hmem α h0 X hX)
  obtain ⟨Z', hZ'⟩ :=
    exists_lieKernel_of_mem_nonnegativeWeightSpan hLie hT j ν i hrep X' (hmem _ h0' X' hX')
  exact hobs k G hG T j hT hj B i f hB.isClosedSubgroup hB.smooth hB.connectedSpace
    hB.isSolvableGroupScheme hf α hα ⟨⟨X, hX, hX0, Z, hZ⟩, ⟨X', hX', hX'0, Z', hZ'⟩⟩

end Assembly

end Langlands.GroupScheme
