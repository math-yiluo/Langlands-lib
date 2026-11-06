import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeTrivialityDescent
import Langlands.AlgebraicGeometry.Picard.LocalTwoAxisTrivialityProof
import Langlands.AlgebraicGeometry.Picard.TranslationInvariantPullbackIdentitiesProof
import Langlands.AbelianScheme.KernelBaseChange

/-! # The locus where the Mumford bundle of a line bundle is trivial on fibres -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

local notation "cl" => LineBundle.isoClass pullbackTensorComparisonIsIso
local notation "pb" => LineBundle.pullbackHom pullbackTensorComparisonIsIso

namespace MumfordTrivialLocus

/-- A pulled-back class is trivial exactly when the pulled-back sheaf is the structure sheaf. -/
lemma pullbackHom_isoClass_eq_one_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) :
    pb f (cl L) = 1 ↔
      Nonempty ((Scheme.Modules.pullback f).obj L.obj ≅ structureSheaf X) := by
  rw [LineBundle.pullbackHom_isoClass,
    ← LineBundle.isoClass_trivial pullbackTensorComparisonIsIso, LineBundle.isoClass_eq_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨(LineBundle.forget X).mapIso e⟩, fun ⟨e⟩ ↦ ⟨ObjectProperty.isoMk _ e⟩⟩

/-- Every isomorphism class of line bundles has a representative. -/
lemma exists_isoClass_eq {X : Scheme.{u}}
    (q : LineBundle.IsoClasses pullbackTensorComparisonIsIso X) :
    ∃ L : LineBundle X, cl L = q := by
  induction q using LineBundle.IsoClasses.ind with | h L => exact ⟨L, rfl⟩

/-- A morphism from the spectrum of a field has image the image of the closed point. -/
lemma range_subset_iff {K : Type u} [Field K] {B : Scheme.{u}}
    (t : Spec (CommRingCat.of K) ⟶ B) (U : Set B) :
    Set.range t ⊆ U ↔ t (IsLocalRing.closedPoint K) ∈ U := by
  constructor
  · intro h
    exact h ⟨_, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x (IsLocalRing.closedPoint K)]

end MumfordTrivialLocus

open MumfordTrivialLocus

variable {B : Scheme.{u}} (G : AbelianScheme B) (M : LineBundle G.X.left)

/-- The isomorphism class of the Mumford bundle
`m^*M ⊗ p₁^*M⁻¹ ⊗ p₂^*M⁻¹ ⊗ (e ∘ q)^*M` on `X ×_B X`, where `m` is the group law,
`p₁, p₂` are the projections, `q` is the structure morphism and `e` is the unit section. -/
def mumfordClass : LineBundle.IsoClasses pullbackTensorComparisonIsIso (G.X ⨯ G.X).left :=
  pb ((Limits.prod.fst : G.X ⨯ G.X ⟶ G.X) * Limits.prod.snd).left (cl M) *
    (pb (Limits.prod.fst : G.X ⨯ G.X ⟶ G.X).left (cl M))⁻¹ *
    (pb (Limits.prod.snd : G.X ⨯ G.X ⟶ G.X).left (cl M))⁻¹ *
    pb ((G.X ⨯ G.X).hom ≫ (1 : Over.mk (𝟙 B) ⟶ G.X).left) (cl M)

/-- The Mumford class pulled back along a pair of points. -/
lemma pullbackHom_mumfordClass {T : Over B} (a c : T ⟶ G.X) :
    pb (prod.lift a c).left (mumfordClass G M) =
      pb (a * c).left (cl M) * (pb a.left (cl M))⁻¹ * (pb c.left (cl M))⁻¹ *
        pb (T.hom ≫ (1 : Over.mk (𝟙 B) ⟶ G.X).left) (cl M) := by
  have hm : (prod.lift a c).left ≫
      ((Limits.prod.fst : G.X ⨯ G.X ⟶ G.X) * Limits.prod.snd).left = (a * c).left := by
    rw [← Over.comp_left, MonObj.comp_mul, prod.lift_fst, prod.lift_snd]
  have h1 : (prod.lift a c).left ≫ (Limits.prod.fst : G.X ⨯ G.X ⟶ G.X).left = a.left := by
    rw [← Over.comp_left, prod.lift_fst]
  have h2 : (prod.lift a c).left ≫ (Limits.prod.snd : G.X ⨯ G.X ⟶ G.X).left = c.left := by
    rw [← Over.comp_left, prod.lift_snd]
  have hq : (prod.lift a c).left ≫ (G.X ⨯ G.X).hom ≫ (1 : Over.mk (𝟙 B) ⟶ G.X).left =
      T.hom ≫ (1 : Over.mk (𝟙 B) ⟶ G.X).left := by
    rw [← Category.assoc, Over.w]
  simp only [mumfordClass, map_mul, map_inv]
  rw [LineBundle.pullbackHom_comp_eq _ _ _ hm, LineBundle.pullbackHom_comp_eq _ _ _ h1,
    LineBundle.pullbackHom_comp_eq _ _ _ h2, LineBundle.pullbackHom_comp_eq _ _ _ hq]

/-- The unit section composed with the structure morphism is the identity point. -/
lemma mkIdTerminal_from_comp_one :
    Over.mkIdTerminal.from G.X ≫ (1 : Over.mk (𝟙 B) ⟶ G.X) = (1 : G.X ⟶ G.X) := by
  simp

lemma mkIdTerminal_from_comp_one_left :
    (Over.mkIdTerminal.from G.X ≫ (1 : Over.mk (𝟙 B) ⟶ G.X)).left =
      G.X.hom ≫ (1 : Over.mk (𝟙 B) ⟶ G.X).left := by
  rw [Over.comp_left, Over.mkIdTerminal_from_left]

/-- The Mumford class is trivial on the first section axis. -/
lemma mumfordClass_firstAxis :
    pb (prod.lift (𝟙 G.X) (Over.mkIdTerminal.from G.X ≫ (1 : Over.mk (𝟙 B) ⟶ G.X))).left
      (mumfordClass G M) = 1 := by
  rw [pullbackHom_mumfordClass, mkIdTerminal_from_comp_one_left]
  rw [mkIdTerminal_from_comp_one, mul_one, Over.id_left, LineBundle.pullbackHom_id]
  simp

/-- The Mumford class is trivial on the second section axis. -/
lemma mumfordClass_secondAxis :
    pb (prod.lift (Over.mkIdTerminal.from G.X ≫ (1 : Over.mk (𝟙 B) ⟶ G.X)) (𝟙 G.X)).left
      (mumfordClass G M) = 1 := by
  rw [pullbackHom_mumfordClass, mkIdTerminal_from_comp_one_left]
  rw [mkIdTerminal_from_comp_one, one_mul, Over.id_left, LineBundle.pullbackHom_id,
    mul_right_comm (cl M), mul_inv_cancel, one_mul, inv_mul_cancel]

/-- The set of points of the base over whose fibre the Mumford class is trivial. -/
def mumfordTrivialSet : Set B :=
  {b | pb ((G.X ⨯ G.X).hom.fiberι b) (mumfordClass G M) = 1}

/-- The fibrewise triviality set of the Mumford class is open. -/
theorem isOpen_mumfordTrivialSet : IsOpen (mumfordTrivialSet G M) := by
  rw [isOpen_iff_forall_mem_open]
  intro b hb
  obtain ⟨Λ, hΛ⟩ := exists_isoClass_eq (mumfordClass G M)
  have h1 := (pullbackHom_isoClass_eq_one_iff _ Λ).mp
    (hΛ.symm ▸ mumfordClass_firstAxis G M)
  have h2 := (pullbackHom_isoClass_eq_one_iff _ Λ).mp
    (hΛ.symm ▸ mumfordClass_secondAxis G M)
  have h3 := (pullbackHom_isoClass_eq_one_iff ((G.X ⨯ G.X).hom.fiberι b) Λ).mp
    (hΛ.symm ▸ hb)
  obtain ⟨V, hbV, hV⟩ := localTwoAxisTriviality B G.X G.X inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance 1 1 Λ b h1 h2 h3
  have hV' := (pullbackHom_isoClass_eq_one_iff _ Λ).mpr hV
  rw [hΛ] at hV'
  refine ⟨V, fun b' hb' ↦ ?_, V.isOpen, hbV⟩
  have hr : Set.range (B.fromSpecResidueField b') ⊆ Set.range V.ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    exact Set.singleton_subset_iff.mpr hb'
  let l := IsOpenImmersion.lift V.ι (B.fromSpecResidueField b') hr
  let k : pullback (G.X ⨯ G.X).hom (B.fromSpecResidueField b') ⟶
      pullback (G.X ⨯ G.X).hom V.ι :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ l) (by
      rw [Category.assoc, IsOpenImmersion.lift_fac]
      exact pullback.condition)
  have hk : k ≫ pullback.fst (G.X ⨯ G.X).hom V.ι =
      pullback.fst (G.X ⨯ G.X).hom (B.fromSpecResidueField b') :=
    pullback.lift_fst _ _ _
  show pb (pullback.fst (G.X ⨯ G.X).hom (B.fromSpecResidueField b')) (mumfordClass G M) = 1
  rw [← LineBundle.pullbackHom_comp_eq _ _ _ hk, hV', map_one]

/-- The open locus of the base over whose fibres the Mumford bundle of `M` is trivial. -/
def mumfordTrivialLocus : B.Opens :=
  ⟨mumfordTrivialSet G M, isOpen_mumfordTrivialSet G M⟩

lemma mem_mumfordTrivialLocus_iff (b : B) :
    b ∈ mumfordTrivialLocus G M ↔
      pb ((G.X ⨯ G.X).hom.fiberι b) (mumfordClass G M) = 1 :=
  Iff.rfl

section Field

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
  (L : LineBundle A.X.left)

/-- Over a field, triviality of the Mumford class gives translation invariance. -/
lemma isTranslationInvariant_of_mumfordClass_eq_one (h : mumfordClass A L = 1) :
    GroupScheme.IsTranslationInvariant A.toGrp L := by
  intro x
  have hj := pullbackHom_mumfordClass A L (Over.mkIdTerminal.from A.X ≫ x) (𝟙 A.X)
  rw [h, map_one] at hj
  have h0 : pb (Over.mkIdTerminal.from A.X ≫ x).left (cl L) = 1 :=
    LineBundle.pullbackHom_eq_one_of_factor _ A.X.hom x.left (by simp) _
  have h1 : pb (A.X.hom ≫ (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X).left) (cl L) = 1 :=
    LineBundle.pullbackHom_eq_one_of_factor _ A.X.hom _ rfl _
  rw [h0, h1, Over.id_left, LineBundle.pullbackHom_id, inv_one, mul_one, mul_one] at hj
  have ht : pb (GroupScheme.translation A.toGrp x).left (cl L) = cl L :=
    mul_inv_eq_one.mp hj.symm
  rw [LineBundle.pullbackHom_isoClass] at ht
  exact LineBundle.isoClass_eq_iff.mp ht

/-- Over an algebraically closed field, translation invariance trivializes the Mumford
class. -/
lemma mumfordClass_eq_one_of_isTranslationInvariant [IsAlgClosed K]
    (h : GroupScheme.IsTranslationInvariant A.toGrp L) : mumfordClass A L = 1 := by
  have hm := TranslationInvariantIdentities.categorical_multiplication_class A L h
  have h1 : pb ((A.X ⨯ A.X).hom ≫
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X).left) (cl L) = 1 :=
    LineBundle.pullbackHom_eq_one_of_factor _ (A.X ⨯ A.X).hom _ rfl _
  rw [mumfordClass, h1, mul_one]
  rw [hm, mul_right_comm, mul_inv_cancel_right, mul_inv_cancel]

/-- Over an algebraically closed field, translation invariance is triviality of the
Mumford class. -/
lemma isTranslationInvariant_iff_mumfordClass_eq_one [IsAlgClosed K] :
    GroupScheme.IsTranslationInvariant A.toGrp L ↔ mumfordClass A L = 1 :=
  ⟨mumfordClass_eq_one_of_isTranslationInvariant A L,
    isTranslationInvariant_of_mumfordClass_eq_one A L⟩

end Field

section BaseChange

variable {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ B)

/-- The comparison morphism from the self-product of the base change along `t` to the
self-product of `G`, as a morphism over `B`. -/
def baseChangeProductMap :
    (Over.map t).obj (((Over.pullback t).mapGrp.obj G.toGrp).X ⨯
      ((Over.pullback t).mapGrp.obj G.toGrp).X) ⟶ G.X ⨯ G.X :=
  prod.lift
    (GroupScheme.baseChangePointsEquiv t G.toGrp _
      (Limits.prod.fst (X := ((Over.pullback t).mapGrp.obj G.toGrp).X)
        (Y := ((Over.pullback t).mapGrp.obj G.toGrp).X)))
    (GroupScheme.baseChangePointsEquiv t G.toGrp _
      (Limits.prod.snd (X := ((Over.pullback t).mapGrp.obj G.toGrp).X)
        (Y := ((Over.pullback t).mapGrp.obj G.toGrp).X)))

/-- The Mumford class pulls back to the Mumford class of the base change. -/
lemma pullbackHom_mumfordClass_baseChange :
    pb (baseChangeProductMap G t).left (mumfordClass G M) =
      mumfordClass ((baseChange t).obj G) (fibreLineBundle G M t) := by
  let T := ((baseChange t).obj G).X ⨯ ((baseChange t).obj G).X
  have hc : cl (fibreLineBundle G M t) = pb (pullback.fst G.X.hom t) (cl M) := rfl
  have h0 : pb (((Over.map t).obj (((Over.pullback t).mapGrp.obj G.toGrp).X ⨯
      ((Over.pullback t).mapGrp.obj G.toGrp).X)).hom ≫
        (1 : Over.mk (𝟙 B) ⟶ G.X).left) (cl M) = 1 :=
    LineBundle.pullbackHom_eq_one_of_factor _
      (((Over.pullback t).mapGrp.obj G.toGrp).X ⨯ ((Over.pullback t).mapGrp.obj G.toGrp).X).hom
      (t ≫ (1 : Over.mk (𝟙 B) ⟶ G.X).left) rfl _
  have h1 : pb (T.hom ≫ (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      ((baseChange t).obj G).X).left) (cl (fibreLineBundle G M t)) = 1 :=
    LineBundle.pullbackHom_eq_one_of_factor _ T.hom _ rfl _
  rw [baseChangeProductMap, pullbackHom_mumfordClass, ← map_mul, h0, mumfordClass, h1, hc]
  simp only [GroupScheme.baseChangePointsEquiv_left]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ (congrArg Inv.inv ?_))
    (congrArg Inv.inv ?_)) rfl <;>
    exact (LineBundle.pullbackHom_comp _ _ _ _).symm

/-- The comparison morphism lands in the fibre over the image of the closed point. -/
lemma pullbackHom_baseChangeProductMap_eq_one
    (h : t (IsLocalRing.closedPoint K) ∈ mumfordTrivialSet G M) :
    pb (baseChangeProductMap G t).left (mumfordClass G M) = 1 := by
  set b := t (IsLocalRing.closedPoint K)
  let g : Spec (CommRingCat.of K) ⟶ Spec (B.residueField b) :=
    Spec.map (B.descResidueField (Scheme.stalkClosedPointTo t))
  have hg : g ≫ B.fromSpecResidueField b = t :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K B t
  let T := ((Over.pullback t).mapGrp.obj G.toGrp).X ⨯ ((Over.pullback t).mapGrp.obj G.toGrp).X
  have w : (baseChangeProductMap G t).left ≫ (G.X ⨯ G.X).hom =
      (T.hom ≫ g) ≫ B.fromSpecResidueField b := by
    rw [Over.w, Category.assoc, hg]
    rfl
  let k : _ ⟶ pullback (G.X ⨯ G.X).hom (B.fromSpecResidueField b) :=
    pullback.lift (baseChangeProductMap G t).left (T.hom ≫ g) w
  have hk : k ≫ pullback.fst (G.X ⨯ G.X).hom (B.fromSpecResidueField b) =
      (baseChangeProductMap G t).left :=
    pullback.lift_fst _ _ _
  have h' : pb (pullback.fst (G.X ⨯ G.X).hom (B.fromSpecResidueField b))
      (mumfordClass G M) = 1 := h
  rw [← LineBundle.pullbackHom_comp_eq _ _ _ hk, h', map_one]

/-- Conversely, triviality after base change along `t` descends to the fibre over the
image of the closed point. -/
lemma mem_mumfordTrivialSet_of_pullbackHom_eq_one
    (h : pb (baseChangeProductMap G t).left (mumfordClass G M) = 1) :
    t (IsLocalRing.closedPoint K) ∈ mumfordTrivialSet G M := by
  set b := t (IsLocalRing.closedPoint K)
  obtain ⟨hs, hp, hgc⟩ := Langlands.AlgebraicGeometry.Picard.product_geometry G.X G.X
  let g : Spec (CommRingCat.of K) ⟶ Spec (B.residueField b) :=
    Spec.map (B.descResidueField (Scheme.stalkClosedPointTo t))
  have hg : g ≫ B.fromSpecResidueField b = t :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K B t
  let f := (G.X ⨯ G.X).hom.fiberToSpecResidueField b
  have hsm : Smooth f := by
    change Smooth (pullback.snd (G.X ⨯ G.X).hom (B.fromSpecResidueField b))
    infer_instance
  have hpr : IsProper f := by
    change IsProper (pullback.snd (G.X ⨯ G.X).hom (B.fromSpecResidueField b))
    infer_instance
  have hco : GeometricallyConnected f := by
    change GeometricallyConnected (pullback.snd (G.X ⨯ G.X).hom (B.fromSpecResidueField b))
    infer_instance
  obtain ⟨Λ, hΛ⟩ := exists_isoClass_eq (mumfordClass G M)
  let W : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd f g)
  have hW : pullback.fst f g ≫ (G.X ⨯ G.X).hom.fiberι b ≫ (G.X ⨯ G.X).hom =
      ((Over.map t).obj W).hom := by
    rw [Scheme.Hom.fiber_fac, ← Category.assoc, pullback.condition, Category.assoc, hg]
    rfl
  let a : (Over.map t).obj W ⟶ G.X ⨯ G.X :=
    Over.homMk (pullback.fst f g ≫ (G.X ⨯ G.X).hom.fiberι b) (by
      rw [Category.assoc]
      exact hW)
  let e := GroupScheme.baseChangePointsEquiv t G.toGrp W
  let θ : W ⟶ ((Over.pullback t).mapGrp.obj G.toGrp).X ⨯
      ((Over.pullback t).mapGrp.obj G.toGrp).X :=
    prod.lift (e.symm (a ≫ Limits.prod.fst)) (e.symm (a ≫ Limits.prod.snd))
  have hθ : (Over.map t).map θ ≫ baseChangeProductMap G t = a := by
    apply prod.hom_ext
    · rw [Category.assoc, baseChangeProductMap, prod.lift_fst,
        ← GroupScheme.baseChangePointsEquiv_naturality, prod.lift_fst]
      exact e.apply_symm_apply _
    · rw [Category.assoc, baseChangeProductMap, prod.lift_snd,
        ← GroupScheme.baseChangePointsEquiv_naturality, prod.lift_snd]
      exact e.apply_symm_apply _
  have hθ' : θ.left ≫ (baseChangeProductMap G t).left =
      pullback.fst f g ≫ (G.X ⨯ G.X).hom.fiberι b :=
    congrArg CommaMorphism.left hθ
  have hK : pb (pullback.fst f g) (pb ((G.X ⨯ G.X).hom.fiberι b) (cl Λ)) = 1 := by
    rw [LineBundle.pullbackHom_comp, ← hθ', ← LineBundle.pullbackHom_comp, hΛ, h, map_one]
  obtain ⟨eF⟩ := @fieldBaseChangeTrivialityDescent _ K _ _ g _ f hsm hpr hco
    ((LineBundle.pullback ((G.X ⨯ G.X).hom.fiberι b)).obj Λ).obj
    ((LineBundle.pullback ((G.X ⨯ G.X).hom.fiberι b)).obj Λ).property
    ((pullbackHom_isoClass_eq_one_iff (pullback.fst f g)
      ((LineBundle.pullback ((G.X ⨯ G.X).hom.fiberι b)).obj Λ)).mp hK)
  show pb ((G.X ⨯ G.X).hom.fiberι b) (mumfordClass G M) = 1
  rw [← hΛ]
  exact (pullbackHom_isoClass_eq_one_iff _ Λ).mpr ⟨eF⟩

end BaseChange

/-- A geometric fibre of `M` is translation invariant exactly when the geometric point lies
in the Mumford-triviality locus. -/
theorem isTranslationInvariant_fibreLineBundle_iff
    (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ B) :
    GroupScheme.IsTranslationInvariant ((baseChange t).obj G).toGrp (fibreLineBundle G M t) ↔
      Set.range t ⊆ (mumfordTrivialLocus G M : Set B) := by
  rw [isTranslationInvariant_iff_mumfordClass_eq_one, ← pullbackHom_mumfordClass_baseChange,
    range_subset_iff]
  exact ⟨mem_mumfordTrivialSet_of_pullbackHom_eq_one G M t,
    pullbackHom_baseChangeProductMap_eq_one G M t⟩

end Langlands.AbelianScheme
