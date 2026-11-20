import Langlands.AlgebraicGeometry.AffineClosedFactorizationLocus
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Lie.ElementCentralizerTangent
import Langlands.GroupScheme.Rational.MaximalTorusConjugatorCaseCConjugator
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Descent from the centralizer of a regular toral Lie element -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

private theorem range_le_of_affinePoints {k : Type u} [Field k]
    {G H H' : GroupScheme (Spec (CommRingCat.of k))} [IsAffine H.X.left]
    (i : H ⟶ G) (i' : H' ⟶ G)
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A] (p : AffinePoints G A),
      p ∈ (SubgroupFunctor.range i).carrier _ → p ∈ (SubgroupFunctor.range i').carrier _) :
    SubgroupFunctor.range i ≤ SubgroupFunctor.range i' := by
  let R := CommRingCat.of k
  let A := ((algΓ R).obj H.X).unop
  let e := Langlands.AlgebraicGeometry.AffineClosedFactorizationLocus.coordinateIso R H.X
  have hm := h A (e.inv ≫ i.hom.hom) (SubgroupFunctor.mem_range.mpr ⟨e.inv, rfl⟩)
  obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp hm
  intro U p hp
  obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hp
  refine SubgroupFunctor.mem_range.mpr ⟨z ≫ e.hom ≫ a, ?_⟩
  rw [Category.assoc, Category.assoc, ha, Iso.hom_inv_id_assoc]

section BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G C : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local notation "bc" => GroupScheme.baseChange (algebraBaseMap k K)
local notation "G_K" => Functor.obj bc G
local notation "C_K" => Functor.obj bc C

local instance regularTorusDescent_baseChangeAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

local instance regularTorusDescent_baseChangeFiniteType : LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- The closed representative of a Lie-element centralizer base changes to a representative
of the centralizer of the extended Lie element. -/
theorem elementCentralizer_isRepresentedBy_baseChange [IsAffineHom C.X.hom]
    (X : lieKernel G k) (i : C ⟶ G) (hi : (elementCentralizer G X).IsRepresentedBy i) :
    (elementCentralizer G_K (kernelFieldExtension (K := K) G X)).IsRepresentedBy
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i) := by
  let X_K := kernelFieldExtension (K := K) G X
  have hiK := hi.baseChange (algebraBaseMap k K)
  let : IsAffineHom (C_K).X.hom := by
    change IsAffineHom (pullback.snd C.X.hom (algebraBaseMap k K))
    infer_instance
  let : IsAffine (C_K).X.left := isAffine_of_isAffineHom (C_K).X.hom
  obtain ⟨D, j, hj, hcl⟩ := elementCentralizer_isClosedRepresentable G_K X_K
  let : IsClosedImmersion j.hom.hom.left := hcl
  let : IsAffineHom D.X.hom := hcl.isAffineHom
  let : IsAffine D.X.left := isAffine_of_isAffineHom D.X.hom
  have hX : kernelBaseChangeEquiv k K G K X_K = lieKernelMap G (Algebra.ofId k K) X :=
    (kernelBaseChangeEquiv k K G K).apply_symm_apply _
  have htest (A : Type u) [CommRing A] [Algebra K A] (v : AffinePoints G_K A) :
      v ∈ (SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map i)).carrier _ ↔
        v ∈ (SubgroupFunctor.range j).carrier _ := by
    let : Algebra k A := ((algebraMap K A).comp (algebraMap k K)).toAlgebra
    let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    rw [hiK.2, hj.2, SubgroupFunctor.mem_baseChange_affine_iff,
      mem_elementCentralizer_baseChange_affine_iff, mem_elementCentralizer_adjoint_iff, hX]
    change _ ↔ adjoint G A _ (lieKernelMapLinear G (IsScalarTower.toAlgHom k K A)
      (lieKernelMapLinear G (Algebra.ofId k K) (Additive.ofMul X))) =
      lieKernelMapLinear G (IsScalarTower.toAlgHom k K A)
        (lieKernelMapLinear G (Algebra.ofId k K) (Additive.ofMul X))
    have hcomp : (IsScalarTower.toAlgHom k K A).comp (Algebra.ofId k K) = Algebra.ofId k A :=
      Subsingleton.elim _ _
    rw [← lieKernelMapLinear_comp, hcomp]
  refine ⟨hiK.1, ?_⟩
  rw [← hj.2]
  apply le_antisymm
  · apply range_le_of_affinePoints
    intro A _ _ v hv
    exact (htest A v).mp hv
  · apply range_le_of_affinePoints
    intro A _ _ v hv
    exact (htest A v).mpr hv

end BaseChange

section Iso

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- The Lie-element centralizer transports along an isomorphism of the ambient group. -/
theorem elementCentralizer_comap_iso (e : G ≅ H) (X : lieKernel G k) :
    (elementCentralizer H (targetMap e.hom k X)).comap e.hom = elementCentralizer G X := by
  let : IsIso e.hom.hom.hom := inferInstanceAs (IsIso ((Grp.forget _).mapIso e).hom)
  ext U v
  rw [SubgroupFunctor.mem_comap, mem_elementCentralizer, mem_elementCentralizer]
  have htest (A : Type u) [CommRing A] [Algebra k A] (g : AffinePoints G A) :
      Commute (constant H (g ≫ e.hom.hom.hom))
        (lieKernelMap H (Algebra.ofId k A) (targetMap e.hom k X)).val ↔
      Commute (constant G g) (lieKernelMap G (Algebra.ofId k A) X).val := by
    simp only [commute_constant_iff]
    rw [lieKernelMap_target, ← targetMap_conjugation]
    have hinj : Function.Injective (targetMap e.hom A) := by
      intro a b hab
      apply Subtype.ext
      exact (cancel_mono e.hom.hom.hom).mp (congrArg Subtype.val hab)
    exact hinj.eq_iff
  exact ⟨fun h A _ _ a => (htest A (a ≫ v)).mp (h A a),
    fun h A _ _ a => (htest A (a ≫ v)).mpr (h A a)⟩

end Iso

/-- A maximal torus with the full tangent centralizer of a Lie element descends up to
conjugacy when the conjugate of the element is defined over the ground field. -/
def RegularTorusDescentStatement : Prop :=
  ∀ (k K : Type u) [Field k] [CharZero k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [Smooth G.X.hom] [IsAffineHom G.X.hom],
    let G_K := (GroupScheme.baseChange (algebraBaseMap k K)).obj G
    ∀ [IsAffineHom G_K.X.hom] (T : CommGroupScheme (Spec (CommRingCat.of K)))
      [IsAffineHom T.toGrp.X.hom] (j : T.toGrp ⟶ G_K), IsMaximalTorus j →
      ∀ (Y : lieKernel G_K K), SubgroupFunctor.range j ≤ elementCentralizer G_K Y →
        elementCentralizerLie G_K Y = LinearMap.range (targetMapLinear j K) →
        ∀ (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G_K.X) (X : lieKernel G k),
          kernelFieldExtension (K := K) G X = targetMap (G_K.innerIso g).hom K Y →
          ∃ (P : CommGroupScheme (Spec (CommRingCat.of k))) (i : P.toGrp ⟶ G),
            IsMaximalTorus i ∧
              ∃ e : T.toGrp ≅ (GroupScheme.baseChange (algebraBaseMap k K)).obj P.toGrp,
                e.hom ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map i =
                  j ≫ (G_K.innerIso g).hom

set_option maxHeartbeats 600000 in
/-- Construct the descended torus as the identity component of the rational Lie centralizer. -/
theorem regularTorusDescent : RegularTorusDescentStatement.{u} := by
  intro k K _ _ _ _ G _ _ G_K _ T _ j hj Y hjY hLie g X hXY
  let b := algebraBaseMap k K
  let bc := GroupScheme.baseChange b
  let e := G_K.innerIso g
  obtain ⟨C, i, hi, hclosed⟩ := elementCentralizer_isClosedRepresentable G X
  let C_K := bc.obj C
  let : IsClosedImmersion i.hom.hom.left := hclosed
  let : IsAffineHom C.X.hom := hclosed.isAffineHom
  let : LocallyOfFiniteType C.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : Smooth C.X.hom := affineCartierSmooth k C inferInstance inferInstance
  let : Smooth C_K.X.hom := by
    change Smooth (pullback.snd C.X.hom b)
    infer_instance
  let : IsAffineHom C_K.X.hom := by
    change IsAffineHom (pullback.snd C.X.hom b)
    infer_instance
  have hiK := elementCentralizer_isRepresentedBy_baseChange (K := K) X i hi
  let i' : C_K ⟶ G_K := bc.map i ≫ e.inv
  have hi' : (elementCentralizer G_K Y).IsRepresentedBy i' := by
    have h := hiK.comp_iso e.symm
    change SubgroupFunctor.IsRepresentedBy
      ((elementCentralizer G_K (kernelFieldExtension (K := K) G X)).comap e.hom) i' at h
    rw [hXY, elementCentralizer_comap_iso] at h
    exact h
  have hcl' : IsClosedSubgroup i' := (IsClosedSubgroup.baseChange b hclosed).comp_iso e.symm
  let f := hi'.factorHom j hjY
  have hf : f ≫ i' = j := hi'.factorHom_comp j hjY
  let C₀K := identityComponent C_K
  let : ConnectedSpace T.toGrp.X.left := hj.1.connectedSpace
  let : Smooth T.toGrp.X.hom := hj.1.smooth
  let q : T.toGrp ⟶ C₀K := IdentityComponent.factor C_K f
  let i₀' : C₀K ⟶ G_K := identityComponentι C_K ≫ i'
  have hq : q ≫ i₀' = j := by
    dsimp only [i₀', q]
    rw [← Category.assoc, IdentityComponent.factor_identityComponentι, hf]
  have hcl₀ : IsClosedSubgroup i₀' :=
    (IdentityComponent.isClosedSubgroup_identityComponentι C_K).comp hcl'
  have hclq : IsClosedSubgroup q := IsClosedSubgroup.of_comp hcl₀ (hq.symm ▸ hj.2.1)
  have : IsClosedImmersion i₀'.hom.hom.left := hcl₀
  have : Mono i₀'.hom.hom := Over.mono_of_mono_left _
  have hsurj : Function.Surjective (targetMapLinear q K) := by
    intro v
    have hv : targetMapLinear i₀' K v ∈ elementCentralizerLie G_K Y := by
      rw [elementCentralizerLie, SubgroupFunctor.lie_eq_range _ _ i' hi']
      exact ⟨targetMapLinear (identityComponentι C_K) K v, by
        rw [show i₀' = identityComponentι C_K ≫ i' from rfl, targetMapLinear_comp]
        rfl⟩
    rw [hLie] at hv
    obtain ⟨w, hw⟩ := hv
    refine ⟨w, targetMapLinear_injective i₀' K ?_⟩
    have he := congrArg (fun f : T.toGrp ⟶ G_K => targetMapLinear f K w) hq
    rw [targetMapLinear_comp] at he
    exact he.trans hw
  let : IsIso q := isIso_of_surjective_targetMapLinear q hclq hsurj
  let H := identityComponent C
  let I := IdentityComponent.baseChangeIso C (algebraMap k K)
  let E : T.toGrp ≅ bc.obj H := asIso q ≪≫ I.symm
  have htor : IsTorus H := IsTorus.of_baseChange (K := K) (IsTorus.of_iso E.symm hj.1)
  let P : CommGroupScheme (Spec (CommRingCat.of k)) := { H with comm := htor.isCommMonObj }
  let i₀ : P.toGrp ⟶ G := identityComponentι C ≫ i
  have hclQ : IsClosedSubgroup i₀ :=
    (IdentityComponent.isClosedSubgroup_identityComponentι C).comp hclosed
  have heq : E.hom ≫ bc.map i₀ = j ≫ e.hom := by
    have hq' := congrArg (fun a => a ≫ e.hom) hq
    change q ≫ I.inv ≫ bc.map i₀ = j ≫ e.hom
    rw [show i₀ = identityComponentι C ≫ i from rfl, Functor.map_comp,
      IdentityComponent.baseChangeIso_inv_comp_assoc]
    simpa only [i₀', i', Category.assoc, Iso.inv_hom_id, Category.comp_id] using hq'
  refine ⟨P, i₀, ?_, E, heq⟩
  apply (maximalTorusBaseChange k K G P i₀ htor hclQ).mpr
  apply (IsMaximalTorus.iso_comp_iff (T' := T) E _).mp
  rw [heq]
  exact hj.comp_iso e

end Langlands.GroupScheme.Lie
