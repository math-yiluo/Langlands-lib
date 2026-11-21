import Langlands.Automorphic.BlockShapeLeviSlices
import Langlands.Global.AdelicNormalizerConjugation

/-! # Rational invariance of the individual matrix Levi slices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Opposite IsDedekindDomain
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.GeneralLinear Langlands.Global Langlands.GroupScheme
  Langlands.GroupScheme.GeneralLinear

variable {n : ℕ} (B : BlockShape n)

theorem standardBlockWeight_eq_blockShapeWeight :
    standardBlockWeight B.cuts = blockShapeWeight B := by
  funext k
  obtain ⟨i, a, rfl⟩ := exists_eq_index B k
  rw [standardBlockWeight_on_index, blockShapeWeight_index]

private theorem leviEmbedding_map {A C : Type u} [CommRing A] [CommRing C]
    (f : A →+* C) (m : B.Levi A) :
    Matrix.GeneralLinearGroup.map f (B.leviEmbedding A m) =
      B.leviEmbedding C (fun i => Matrix.GeneralLinearGroup.map f (m i)) := by
  apply Units.ext
  ext x y
  obtain ⟨i, a, rfl⟩ := exists_eq_index B x
  obtain ⟨j, b, rfl⟩ := exists_eq_index B y
  change f (B.leviEmbedding A m (B.index i a) (B.index j b)) =
    B.leviEmbedding C (fun k => Matrix.GeneralLinearGroup.map f (m k))
      (B.index i a) (B.index j b)
  by_cases hij : i = j
  · subst j
    rw [B.leviEmbedding_apply_same, B.leviEmbedding_apply_same]
    rfl
  · rw [B.leviEmbedding_apply_ne A m a b hij,
      B.leviEmbedding_apply_ne C _ a b hij, map_zero]

variable (F : Type u) [Field F] [NumberField F]

local notation "RF" => CommRingCat.of F
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) RF
local notation "QF" => CommAlgCat.of F F
local notation "P" => blockShapeParabolic B RF

local instance blockSliceFactorsAffine : IsAffine (GLG).X.left := isAffine_groupScheme (Fin n) RF
local instance blockSliceFactorsSmooth : Smooth (GLG).X.hom := smoothStatement (Fin n) RF
local instance blockSliceFactorsRationalAddCommGroup {d : ℕ} : AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance blockSliceFactorsContinuousAddCommGroup {d : ℕ} : AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance blockSliceFactorsFiniteSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

/-- The original matrix constant term is left invariant under principal
points of the block parabolic. -/
theorem blockShapeConstantTerm_parabolic_rational_mul (f : FiniteSmoothRationalFunctions F n)
    (p : B.parabolic F) (g : AdelicGL F n) :
    blockShapeConstantTerm B F f (AdelicGL.rational F n p.val * g) =
      blockShapeConstantTerm B F f g := by
  let x := (GeneralLinearGroupPoints.rationalEquiv F n).symm p.val
  have hx : x ∈ (P).carrier ((algSpec RF).obj (op QF)) := by
    exact (mem_ofMatrixSubgroups_affinePoints_iff (H := fun A => B.parabolic A)
      (hH := fun a _ ha => by
        rw [← blockParabolicSubgroup_blockShapeWeight B] at ha ⊢
        exact map_mem_blockParabolicSubgroup _ a.hom ha) RF QF x).mpr
      ((congrArg (fun y : RationalGL F n => y ∈ B.parabolic F)
        ((GeneralLinearGroupPoints.rationalEquiv F n).apply_symm_apply p.val)).mpr p.property)
  let q := (AdelicGroupPoints.basePointEquiv (F := F) (G := GLG)).symm x
  have hqP : q ∈ (P).carrier (Over.mk (𝟙 (Spec RF))) :=
    (P).comp_mem (Lie.affineSelfTestIso RF).inv hx
  have hqp : q ∈ (blockParabolic (Fin n) RF (standardBlockWeight B.cuts)).carrier
      (Over.mk (𝟙 (Spec RF))) := by
    rw [standardBlockWeight_eq_blockShapeWeight B, blockParabolic_blockShapeWeight]
    exact hqP
  let e := GeneralLinearGroupPoints.adelicEquiv F n
  let f' := (GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm f.val
  have he : e (GroupSchemeFunctions.innerAdelicPoint F GLG q) = AdelicGL.rational F n p.val := by
    change e ((GLG).constantPoint q _) = _
    rw [← AdelicGroupPoints.rational_basePointEquiv, GeneralLinearGroupPoints.adelicEquiv_rational]
    simp only [q, x, MulEquiv.apply_symm_apply]
  have harg : e.symm (AdelicGL.rational F n p.val * g) =
      GroupSchemeFunctions.innerAdelicPoint F GLG q * e.symm g := by
    apply e.injective
    rw [e.apply_symm_apply, map_mul, he, e.apply_symm_apply]
  have h := GroupSchemeFunctions.normalizedBlockConstantTerm_parabolic_rational_mul
    F (standardBlockWeight B.cuts) f' q hqp (e.symm g)
  change GroupSchemeFunctions.normalizedBlockConstantTerm F (standardBlockWeight B.cuts)
      f' (e.symm (AdelicGL.rational F n p.val * g)) = _
  exact (congrArg (GroupSchemeFunctions.normalizedBlockConstantTerm F
    (standardBlockWeight B.cuts) f') harg).trans h

/-- The product Levi slice is invariant under left multiplication by the
principal image of a rational product of blocks. -/
theorem blockShapeLeviSlice_rational_mul (f : FiniteSmoothRationalFunctions F n)
    (g : AdelicGL F n) (q : B.Levi F) (m : AdelicBlockParabolic.FullLevi F B) :
    blockShapeLeviSlice F B f g
        ((fun i => AdelicGL.rational F (B.size i) (q i)) * m) =
      blockShapeLeviSlice F B f g m := by
  let p := B.leviInParabolic F q
  have hp : AdelicGL.rational F n p.val =
      B.leviEmbedding (Adeles F) (fun i => AdelicGL.rational F (B.size i) (q i)) :=
    leviEmbedding_map B (algebraMap F (Adeles F)) q
  unfold blockShapeLeviSlice
  rw [map_mul, ← hp, mul_assoc]
  exact blockShapeConstantTerm_parabolic_rational_mul B F f p _

/-- Holding all other Levi coordinates fixed gives a continuous
rational-invariant function on the specified original block group. -/
def blockShapeLeviSliceFactor (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n)
    (m : AdelicBlockParabolic.FullLevi F B) (i : Fin B.length) :
    ContinuousRationalFunctions F (B.size i) := by
  refine ⟨⟨fun x => blockShapeLeviSlice F B f g (Function.update m i x), ?_⟩, ?_⟩
  · intro a x
    let q : B.Levi F := Pi.mulSingle i a
    have hupdate : Function.update m i (AdelicGL.rational F (B.size i) a * x) =
        (fun j => AdelicGL.rational F (B.size j) (q j)) * Function.update m i x := by
      funext j
      by_cases hj : j = i
      · subst j
        simp only [q, Function.update_self, Pi.mul_apply, Pi.mulSingle_eq_same]
      · simp only [q, Pi.mul_apply, Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj, map_one, one_mul]
    change blockShapeLeviSlice F B f g (Function.update m i (AdelicGL.rational F _ a * x)) = _
    rw [hupdate]
    exact blockShapeLeviSlice_rational_mul B F f g q (Function.update m i x)
  · exact (continuous_blockShapeLeviSlice F B f g).comp
      (continuous_const.update i continuous_id)

private def finiteBlockEmbedding (i : Fin B.length) :
    FiniteAdelicGL F (B.size i) →ₜ* FiniteAdelicGL F n where
  toMonoidHom := (B.leviEmbedding (FiniteAdeleRing (𝓞 F) F)).comp
    (MonoidHom.mulSingle (fun j => FiniteAdelicGL F (B.size j)) i)
  continuous_toFun := (B.leviEmbeddingContinuous (FiniteAdeleRing (𝓞 F) F)).continuous.comp
    (continuous_mulSingle (A := fun j => FiniteAdelicGL F (B.size j)) i)

private theorem fullLeviEmbedding_mulSingle_ofFinite (i : Fin B.length)
    (d : FiniteAdelicGL F (B.size i)) :
    B.leviEmbedding (Adeles F) (Pi.mulSingle i (AdelicGL.ofFinite F (B.size i) d)) =
      AdelicGL.ofFinite F n (finiteBlockEmbedding B F i d) := by
  let v : AdelicBlockParabolic.FullLevi F B := Pi.mulSingle i (AdelicGL.ofFinite F (B.size i) d)
  have hInf : (fun j => AdelicGL.infinite F (B.size j) (v j)) = 1 := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [v, Pi.mulSingle_eq_same, AdelicGL.infinite_ofFinite, Pi.one_apply]
    · simp only [v, Pi.mulSingle_eq_of_ne hj, map_one, Pi.one_apply]
  have hf : (fun j => AdelicGL.finite F (B.size j) (v j)) = Pi.mulSingle i d := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [v, Pi.mulSingle_eq_same, AdelicGL.finite_ofFinite]
    · simp only [v, Pi.mulSingle_eq_of_ne hj, map_one]
  apply AdelicGL.ext_infinite_finite F n
  · change AdelicGL.infinite F n (B.leviEmbedding (Adeles F) v) = _
    rw [show AdelicGL.infinite F n (B.leviEmbedding (Adeles F) v) =
      B.leviEmbedding (InfiniteAdeleRing F) (fun j => AdelicGL.infinite F (B.size j) (v j)) from
      leviEmbedding_map B (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) v]
    rw [hInf, map_one, AdelicGL.infinite_ofFinite]
  · change AdelicGL.finite F n (B.leviEmbedding (Adeles F) v) = _
    rw [show AdelicGL.finite F n (B.leviEmbedding (Adeles F) v) =
      B.leviEmbedding (FiniteAdeleRing (𝓞 F) F) (fun j => AdelicGL.finite F (B.size j) (v j)) from
      leviEmbedding_map B (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) v]
    rw [hf, AdelicGL.finite_ofFinite]
    rfl

private theorem blockShapeLeviSlice_single_finite_mul
    (f : FiniteSmoothRationalFunctions F n) (m : AdelicBlockParabolic.FullLevi F B)
    (i : Fin B.length) (x : AdelicGL F (B.size i)) (d : FiniteAdelicGL F (B.size i)) :
    blockShapeLeviSlice F B f 1 (Function.update m i (x * AdelicGL.ofFinite F (B.size i) d)) =
      blockShapeLeviSlice F B (finiteSmoothRightAction F n
        (AdelicGL.ofFinite F n (finiteBlockEmbedding B F i d)) f) 1 (Function.update m i x) := by
  let a := AdelicGL.ofFinite F (B.size i) d
  let y := B.leviEmbedding (Adeles F) (Function.update m i x)
  have hcoord : Function.update m i (x * a) = Function.update m i x * Pi.mulSingle i a := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Pi.mul_apply, Function.update_self, Pi.mulSingle_eq_same]
    · simp only [Pi.mul_apply, Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj, mul_one]
  let b := AdelicGL.ofFinite F n (finiteBlockEmbedding B F i d)
  let f' := finiteSmoothRightAction F n b f
  have harg : B.leviEmbedding (Adeles F) (Function.update m i (x * a)) = y * b :=
    (congrArg (B.leviEmbedding (Adeles F)) hcoord).trans
      (((B.leviEmbedding (Adeles F)).map_mul _ _).trans
        (congrArg (y * ·) (fullLeviEmbedding_mulSingle_ofFinite B F i d)))
  change blockShapeConstantTerm B F f
      (B.leviEmbedding (Adeles F) (Function.update m i (x * a)) * 1) =
    blockShapeConstantTerm B F f' (y * 1)
  calc
    _ = blockShapeConstantTerm B F f (y * b) :=
      congrArg (blockShapeConstantTerm B F f) ((mul_one _).trans harg)
    _ = blockShapeConstantTerm B F f' y := (blockShapeConstantTerm_rightAction B F f b y).symm
    _ = _ := (congrArg (blockShapeConstantTerm B F f') (mul_one y)).symm

/-- Each individual block slice has a common open finite stabilizer. -/
theorem blockShapeLeviSliceFactor_mem_finiteSmoothSubrepresentation
    (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n)
    (m : AdelicBlockParabolic.FullLevi F B) (i : Fin B.length) :
    blockShapeLeviSliceFactor B F f g m i ∈ finiteSmoothSubrepresentation F (B.size i) := by
  let f' := finiteSmoothRightAction F n g f
  have hfin : f'.val ∈ finiteSmoothSubrepresentation F n := f'.property.2
  obtain ⟨L, hL⟩ := hfin
  let e := finiteBlockEmbedding B F i
  refine ⟨L.comap e.toMonoidHom e.continuous, ?_⟩
  intro d
  have hd := hL ⟨e d.val, d.property⟩
  have hf' : finiteSmoothRightAction F n (AdelicGL.ofFinite F n (e d.val)) f' = f' :=
    Subtype.ext hd
  have hslice (y : AdelicBlockParabolic.FullLevi F B) :
      blockShapeLeviSlice F B f' 1 y = blockShapeLeviSlice F B f g y := by
    rw [blockShapeLeviSlice_rightAction F B f g 1 y, one_mul]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  let a := AdelicGL.ofFinite F (B.size i) d.val
  change blockShapeLeviSlice F B f g (Function.update m i (x * a)) =
    blockShapeLeviSlice F B f g (Function.update m i x)
  exact (hslice _).symm.trans ((blockShapeLeviSlice_single_finite_mul B F f' m i x d.val).trans
    ((congrArg (fun v => blockShapeLeviSlice F B v 1 (Function.update m i x)) hf').trans
      (hslice _)))

end Langlands.Automorphic
