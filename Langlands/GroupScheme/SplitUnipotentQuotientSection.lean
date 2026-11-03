import Langlands.GroupScheme.SplitUnipotentAffineTorsorStatement
import Langlands.GroupScheme.HomogeneousQuotientFiber
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.FppfQuotientSmooth

/-! # Affine quotient sections from split-unipotent torsor triviality -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotient

section ExactQuotient

variable {k : Type u} [Field k]
variable (G H : GroupScheme (Spec (CommRingCat.of k)))
variable (i : H ⟶ G) [Mono i.hom.hom]
variable {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
variable [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
variable (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier V)

include hfib

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Split-unipotent torsor triviality lifts every point of an exact homogeneous
quotient on every affine test scheme over the original field. -/
theorem affine_lifts_of_split_unipotent_torsors
    (htor : SplitUnipotentAffineTorsorStatement.{u})
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hH : RelativeRoot.IsSplitUnipotent H)
    (T : Over (Spec (CommRingCat.of k))) [IsAffine T.left]
    (p : T ⟶ Q) : ∃ g : T ⟶ G.X, g ≫ q = p := by
  let G' := (GroupScheme.baseChange T.hom).obj G
  let H' := (GroupScheme.baseChange T.hom).obj H
  let i' : H' ⟶ G' := (GroupScheme.baseChange T.hom).map i
  let Q' := (Over.pullback T.hom).obj Q
  let q' : G'.X ⟶ Q' := (Over.pullback T.hom).map q
  let p₀ : (Over.map T.hom).obj (Over.mk (𝟙 T.left)) ⟶ Q :=
    Over.homMk p.left (by
      change p.left ≫ Q.hom = (𝟙 T.left) ≫ T.hom
      simpa only [Category.id_comp] using p.w)
  let p' : Over.mk (𝟙 T.left) ⟶ Q' :=
    (Over.mapPullbackAdj T.hom).homEquiv _ _ p₀
  let : Flat q'.left := MorphismProperty.overPullbackMap (P := @Flat) T.hom q
    inferInstance
  let : Surjective q'.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) T.hom q inferInstance
  let : QuasiCompact q'.left :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) T.hom q inferInstance
  let : Mono i'.hom.hom := by
    change Mono ((Over.pullback T.hom).map i.hom.hom)
    infer_instance
  have hfib' : ∀ (V : Over T.left) (g h : V ⟶ G'.X),
      g ≫ q' = h ≫ q' ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i').carrier V := by
    intro V g h
    rw [← ((Over.mapPullbackAdj T.hom).homEquiv V Q).symm.injective.eq_iff]
    dsimp only [q']
    rw [(Over.mapPullbackAdj T.hom).homEquiv_naturality_right_symm g q,
      (Over.mapPullbackAdj T.hom).homEquiv_naturality_right_symm h q]
    change baseChangePointsEquiv T.hom G V g ≫ q =
      baseChangePointsEquiv T.hom G V h ≫ q ↔ _
    rw [hfib, SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange,
      map_mul, map_inv]
  let X := Dynamic.flagQuotientFiber G' q' p'
  let : ModObj H'.X X := Dynamic.flagQuotientFiberModObj G' q' p' H' i' hfib'
  obtain ⟨s, hs⟩ := htor k H hH T X
    (inferInstance : Flat X.hom) (inferInstance : Surjective X.hom)
    (inferInstance : QuasiCompact X.hom)
    (Dynamic.flagQuotientFiber_leftSMul_isIso G' q' p' H' i' hfib')
  let x : Over.mk (𝟙 T.left) ⟶ X := Over.homMk s hs
  let g' := x ≫ Dynamic.flagQuotientFiberι G' q' p'
  have hg' : g' ≫ q' = p' := by
    change (x ≫ Dynamic.flagQuotientFiberι G' q' p') ≫ q' = _
    rw [Category.assoc, Dynamic.flagQuotientFiberι_comp, ← Category.assoc]
    have hx : x ≫ CategoryTheory.CartesianMonoidalCategory.toUnit X =
        𝟙 (Over.mk (𝟙 T.left)) :=
      CategoryTheory.CartesianMonoidalCategory.toUnit_unique _ _
    rw [hx, Category.id_comp]
  let g₀ := baseChangePointsEquiv T.hom G (Over.mk (𝟙 T.left)) g'
  refine ⟨Over.homMk g₀.left (by
    have hw := g₀.w
    change g₀.left ≫ G.X.hom = (𝟙 T.left) ≫ T.hom at hw
    simpa only [Category.id_comp] using hw), ?_⟩
  apply Over.OverMorphism.ext
  have h := congrArg
    (fun z => ((Over.mapPullbackAdj T.hom).homEquiv (Over.mk (𝟙 T.left)) Q).symm z)
    hg'
  dsimp only [q', p'] at h
  rw [(Over.mapPullbackAdj T.hom).homEquiv_naturality_right_symm g' q,
    Equiv.symm_apply_apply] at h
  exact congrArg (fun z => z.left) h

/-- On an affine quotient, lifting its identity test point gives a scheme section. -/
theorem affine_section_of_split_unipotent_torsors
    (htor : SplitUnipotentAffineTorsorStatement.{u})
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hH : RelativeRoot.IsSplitUnipotent H) [IsAffine Q.left] :
    ∃ s : Q ⟶ G.X, s ≫ q = 𝟙 Q :=
  affine_lifts_of_split_unipotent_torsors G H i q hfib htor hH Q (𝟙 Q)

/-- A chosen actual section of an affine exact homogeneous quotient, conditional
on split-unipotent affine-torsor triviality. -/
def affineQuotientSection
    (htor : SplitUnipotentAffineTorsorStatement.{u})
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hH : RelativeRoot.IsSplitUnipotent H) [IsAffine Q.left] : Q ⟶ G.X :=
  Classical.choose (affine_section_of_split_unipotent_torsors G H i q hfib htor hH)

@[reassoc (attr := simp)]
theorem affineQuotientSection_comp
    (htor : SplitUnipotentAffineTorsorStatement.{u})
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hH : RelativeRoot.IsSplitUnipotent H) [IsAffine Q.left] :
    affineQuotientSection G H i q hfib htor hH ≫ q = 𝟙 Q :=
  Classical.choose_spec (affine_section_of_split_unipotent_torsors G H i q hfib htor hH)

end ExactQuotient

variable {k : Type u} [Field k]
variable (G H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G)

/-- For represented fppf quotients of affine groups by smooth closed split
unipotent subgroups, the broader affine-torsor statement supplies a section
of every affine quotient model. -/
theorem fppf_section_of_split_unipotent_torsors
    (htor : SplitUnipotentAffineTorsorStatement.{u})
    [IsAffineHom G.X.hom] [Smooth H.X.hom]
    (hi : IsClosedSubgroup i) (hH : RelativeRoot.IsSplitUnipotent H)
    (K : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom K.X.hom]
    (π : G ⟶ K) (hπ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) π) :
    ∃ s : K.X ⟶ G.X, s ≫ π.hom.hom = 𝟙 K.X := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom H.X.hom := affine_subgroup_of_closed G H i hi
  let : IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom
  let : Flat π.hom.hom.left := hπ.1
  let : Surjective π.hom.hom.left := hπ.2.1
  have hqc : QuasiCompact (π.hom.hom.left ≫ K.X.hom) := by
    rw [Over.w π.hom.hom]
    infer_instance
  let : QuasiCompact (π.hom.hom.left ≫ K.X.hom) := hqc
  let : QuasiCompact π.hom.hom.left := QuasiCompact.of_comp _ K.X.hom
  exact affine_section_of_split_unipotent_torsors G H i π.hom.hom
    (hπ.fibers_iff ⟨inferInstance, rfl⟩) htor hH

end Langlands.GroupScheme.HomogeneousQuotient
