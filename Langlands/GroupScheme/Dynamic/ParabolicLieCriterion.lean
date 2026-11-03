import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Dynamic.LieStatement
import Langlands.GroupScheme.Dynamic.SmoothConnectedStatement
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Lie.SubgroupEqualityStatement
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Rational.SplitTorusFiniteRank

/-! # Dynamic parabolics are determined by their Lie algebras (conditional on structure inputs) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Dual-number kernels along homomorphisms -/



/-! ### Factorization through representing subgroups -/

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G H H' : GroupScheme S}

/-- The points of a composite `f ≫ g` are points of `g`. -/
theorem range_comp_le (f : H' ⟶ H) (g : H ⟶ G) : range (f ≫ g) ≤ range g := by
  intro T x hx
  obtain ⟨y, rfl⟩ := mem_range.1 hx
  refine mem_range.2 ⟨y ≫ f.hom.hom, ?_⟩
  rw [Grp.comp_hom_hom, Category.assoc]

variable {F : SubgroupFunctor G} {i : H ⟶ G}

/-- A homomorphism whose points all lie in `F` factors through a group scheme representing `F`. -/
def IsRepresentedBy.liftOfLE (hi : F.IsRepresentedBy i) (f : H' ⟶ G) (hf : range f ≤ F) :
    H' ⟶ H :=
  IsRepresentedBy.lift (top_isRepresentedBy_id H') hi
    (fun T =>
      { toFun := fun x => ⟨(x : T ⟶ H'.X) ≫ f.hom.hom, hf T (mem_range.2 ⟨x.1, rfl⟩)⟩
        map_one' := Subtype.ext (MonObj.one_comp _)
        map_mul' := fun _ _ => Subtype.ext (MonObj.mul_comp _ _ _) })
    (fun _ _ => Category.assoc _ _ _)

theorem IsRepresentedBy.liftOfLE_comp (hi : F.IsRepresentedBy i) (f : H' ⟶ G)
    (hf : range f ≤ F) : hi.liftOfLE f hf ≫ i = f :=
  IsRepresentedBy.lift_comp_eq _ _ _ (fun _ _ => Category.assoc _ _ _) fun _ x => by
    change x ≫ f.hom.hom = (x ≫ 𝟙 H'.X) ≫ f.hom.hom
    rw [Category.comp_id]

end SubgroupFunctor

/-! ### Points of a commutative subgroup centralize its cocharacters -/

section Centralizer

variable {S : Scheme.{u}} {G : GroupScheme S} {T : CommGroupScheme S}

/-- The points of a commutative subgroup `j : T ⟶ G` centralize every cocharacter of `T`. -/
theorem range_le_centralizer_groupHom_comp (j : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    SubgroupFunctor.range j ≤ Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ j) := by
  intro U x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  rw [Dynamic.mem_centralizer, Dynamic.orbit]
  have key : ((CartesianMonoidalCategory.snd U (Gm S).X ≫ (CommGroupScheme.groupHom ν).hom.hom) *
      (CartesianMonoidalCategory.fst U (Gm S).X ≫ t) *
      (CartesianMonoidalCategory.snd U (Gm S).X ≫ (CommGroupScheme.groupHom ν).hom.hom)⁻¹) ≫
        j.hom.hom = (CartesianMonoidalCategory.fst U (Gm S).X ≫ t) ≫ j.hom.hom := by
    rw [mul_inv_cancel_comm]
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp] at key
  simpa only [Category.assoc, Grp.comp_hom_hom] using key

end Centralizer

/-! ### A Lie criterion for containment of dynamic parabolics -/

section LieCriterion

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Let `G` be a smooth connected affine group over a field and `χ, χ'` cocharacters with the
points of `χ'` in `P_G(χ)`. If every element of `Lie(G)` that lies in `P_G(χ)` lies in
`P_G(χ')`, then `P_G(χ) ≤ P_G(χ')`. The proof applies the subgroup-equality criterion to
`P_H(χ') ⊆ H = P_G(χ)`. -/
theorem parabolic_le_parabolic_of_lieKernel (hSm : DynamicSmoothStatement.{u})
    (hCo : DynamicConnectedStatement.{u}) (hEq : LieSubgroupEqualityStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (χ χ' : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ' : SubgroupFunctor.range χ' ≤ Dynamic.parabolic χ)
    (hlie : ∀ X : lieKernel G k, X.val ∈ (Dynamic.parabolic χ).carrier _ →
      X.val ∈ (Dynamic.parabolic χ').carrier _) :
    Dynamic.parabolic χ ≤ Dynamic.parabolic χ' := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨H, iP, hiP, hiPc⟩ : ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (iP : H ⟶ G),
      (Dynamic.parabolic χ).IsRepresentedBy iP ∧ IsClosedSubgroup iP :=
    ⟨_, _, Dynamic.Affine.isRepresentedBy_parabolicHom χ,
      Dynamic.Affine.isClosedSubgroup_parabolicHom χ⟩
  have : IsClosedImmersion iP.hom.hom.left := hiPc
  have : Mono iP.hom.hom := hiP.1
  have : Smooth H.X.hom := (hSm k G χ H iP).1 hiP
  have : ConnectedSpace H.X.left := ((hCo k G χ H iP).2 ‹_›).1 hiP
  have : IsAffineHom H.X.hom := by
    rw [← Over.w iP.hom.hom]
    infer_instance
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨χH, hχH⟩ : ∃ χH : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ H, χH ≫ iP = χ' :=
    ⟨_, hiP.liftOfLE_comp χ' hχ'⟩
  obtain ⟨K, κ, hκ, hκc⟩ : ∃ (K : GroupScheme (Spec (CommRingCat.of k))) (κ : K ⟶ H),
      (Dynamic.parabolic χH).IsRepresentedBy κ ∧ IsClosedSubgroup κ :=
    ⟨_, _, Dynamic.Affine.isRepresentedBy_parabolicHom χH,
      Dynamic.Affine.isClosedSubgroup_parabolicHom χH⟩
  have : Mono κ.hom.hom := hκ.1
  have : Smooth K.X.hom := (hSm k H χH K κ).1 hκ
  have hP : Dynamic.parabolic χH = (Dynamic.parabolic χ').comap iP := by
    rw [← hχH]
    exact Dynamic.parabolic_eq_comap_of_isClosedSubgroup χH iP hiPc
  have htop : SubgroupFunctor.range κ = ⊤ := by
    refine hEq k H K κ hκc fun X => ?_
    have h1 : (Lie.targetMap iP k X).val ∈ (Dynamic.parabolic χ).carrier _ := by
      rw [← hiP.2]
      exact SubgroupFunctor.mem_range.2 ⟨X.val, rfl⟩
    have h1' := hlie (Lie.targetMap iP k X) h1
    have h2 : X.val ∈ (Dynamic.parabolic χH).carrier _ := by
      rw [hP, SubgroupFunctor.mem_comap]
      exact h1'
    rw [← hκ.2] at h2
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 h2
    refine ⟨⟨y, mem_lieKernel_of_comp κ y ?_⟩, hy⟩
    rw [hy]
    exact X.property
  intro U g hg
  rw [← hiP.2] at hg
  obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.1 hg
  have hh : h ∈ (Dynamic.parabolic χH).carrier U := by
    rw [← hκ.2, htop]
    exact Subgroup.mem_top _
  rw [hP, SubgroupFunctor.mem_comap] at hh
  exact hh

end LieCriterion

/-! ### Equality of dynamic parabolics through their Lie algebras -/

section LieEquality

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

/-- Let `G` be a smooth connected affine group over a field and `χ, χ'` cocharacters whose
points lie in each other's dynamic parabolics. Then `P_G(χ) = P_G(χ')` exactly when the sums of
the nonnegative weight spaces of `𝔾_m` on `Lie(G)` through `χ` and through `χ'` agree. -/
theorem parabolic_eq_iff_iSup_weightSpace_eq (hLie : DynamicLieStatement.{u})
    (hSm : DynamicSmoothStatement.{u}) (hCo : DynamicConnectedStatement.{u})
    (hEq : LieSubgroupEqualityStatement.{u}) [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (χ χ' : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ' : SubgroupFunctor.range χ' ≤ Dynamic.parabolic χ)
    (hχ : SubgroupFunctor.range χ ≤ Dynamic.parabolic χ') :
    Dynamic.parabolic χ = Dynamic.parabolic χ' ↔
      (⨆ n : ℕ, weightSpace χ (Gm.powerHom _ n)) = ⨆ n : ℕ, weightSpace χ' (Gm.powerHom _ n) := by
  have hmem : ∀ (c : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (x : Additive (lieKernel G k)),
      x ∈ (⨆ n : ℕ, weightSpace c (Gm.powerHom _ n)) ↔
        x.toMul.val ∈ (Dynamic.parabolic c).carrier _ :=
    fun c x => ((hLie k G c x.toMul).2.1).symm
  constructor
  · intro h
    ext x
    rw [hmem, hmem, h]
  · intro h
    refine le_antisymm
      (parabolic_le_parabolic_of_lieKernel hSm hCo hEq χ χ' hχ' fun X hX => ?_)
      (parabolic_le_parabolic_of_lieKernel hSm hCo hEq χ' χ hχ fun X hX => ?_)
    · have hX' := (hmem χ (Additive.ofMul X)).2 hX
      rw [h] at hX'
      exact (hmem χ' (Additive.ofMul X)).1 hX'
    · have hX' := (hmem χ' (Additive.ofMul X)).2 hX
      rw [← h] at hX'
      exact (hmem χ (Additive.ofMul X)).1 hX'

/-- For two cocharacters `ν, ν'` of a commutative subgroup `j : T ⟶ G` of a smooth connected
affine group over a field, `P_G(ν ≫ j) = P_G(ν' ≫ j)` exactly when the sums of the nonnegative
weight spaces of `𝔾_m` on `Lie(G)` through `ν ≫ j` and through `ν' ≫ j` agree. -/
theorem parabolic_comp_eq_iff_iSup_weightSpace_eq (hLie : DynamicLieStatement.{u})
    (hSm : DynamicSmoothStatement.{u}) (hCo : DynamicConnectedStatement.{u})
    (hEq : LieSubgroupEqualityStatement.{u}) [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G)
    (ν ν' : cocharacterLattice T) :
    Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) =
        Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ j) ↔
      (⨆ n : ℕ, weightSpace (CommGroupScheme.groupHom ν ≫ j) (Gm.powerHom _ n)) =
        ⨆ n : ℕ, weightSpace (CommGroupScheme.groupHom ν' ≫ j) (Gm.powerHom _ n) :=
  parabolic_eq_iff_iSup_weightSpace_eq hLie hSm hCo hEq _ _
    ((SubgroupFunctor.range_comp_le _ j).trans
      ((range_le_centralizer_groupHom_comp j ν).trans (Dynamic.centralizer_le_parabolic _)))
    ((SubgroupFunctor.range_comp_le _ j).trans
      ((range_le_centralizer_groupHom_comp j ν').trans (Dynamic.centralizer_le_parabolic _)))

end LieEquality

end Langlands.GroupScheme
