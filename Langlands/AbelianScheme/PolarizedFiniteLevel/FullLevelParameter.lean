import Langlands.AbelianScheme.PolarizedFiniteLevel.TupleParameter
import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevelLocusBaseChange

/-! # The actual full-level parameter scheme in a supplied family -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {S S' : Scheme.{u}} (A : AbelianScheme S) (g n : ℕ)

/-- Restricting a tuple before or after the original actual torsion comparison
has the same result at every field-valued point. -/
theorem sectionTupleBaseChangeEquiv_fibre (b : S' ⟶ S)
    (v : SectionTuple ((baseChange b).obj A) g n)
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ S')
    (i : Fin (2 * g)) :
    levelBaseChangeLinear A.toGrp b (Over.mk s) n (fibreTuple v s i) =
      levelRestrict A.toGrp
        (Over.homMk s (by simp) : Over.mk (s ≫ b) ⟶ Over.mk b) n
        (sectionTupleBaseChangeEquiv A g n b v i) := by
  apply toSection_injective A.toGrp (Over.mk (s ≫ b)) n
  apply Over.OverMorphism.ext
  change (s ≫ (Additive.toMul (v i)).val.left) ≫ pullback.fst A.X.hom b =
    s ≫ ((𝟙 S' ≫ (Additive.toMul (v i)).val.left) ≫ pullback.fst A.X.hom b)
  rw [Category.id_comp, Category.assoc]

private def torsionTuplePointIso (b : S' ⟶ S)
    (f : Over.mk b ⟶ torsionTupleScheme A g n)
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ S') :
    Over.mk ((s ≫ f.left) ≫ (torsionTupleScheme A g n).hom) ≅ Over.mk (s ≫ b) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (s ≫ b) = (s ≫ f.left) ≫ (torsionTupleScheme A g n).hom
    rw [Category.id_comp, Category.assoc, f.w]
    rfl)

/-- The two actual iterated pullbacks have canonically equivalent torsion
modules at a field-valued point of a test scheme over the tuple parameter. -/
def torsionTupleFibreComparison (b : S' ⟶ S)
    (f : Over.mk b ⟶ torsionTupleScheme A g n)
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ S') :
    Level ((baseChange f.left).obj
      ((baseChange (torsionTupleScheme A g n).hom).obj A)).toGrp (Over.mk s) n ≃ₗ[ZMod n]
      Level ((baseChange b).obj A).toGrp (Over.mk s) n :=
  (levelBaseChangeLinear ((baseChange (torsionTupleScheme A g n).hom).obj A).toGrp
    f.left (Over.mk s) n).trans
    ((levelBaseChangeLinear A.toGrp (torsionTupleScheme A g n).hom
      (Over.mk (s ≫ f.left)) n).trans
      ((levelTestIsoLinear A.toGrp
        (torsionTuplePointIso A g n b f s) n).trans
        (levelBaseChangeLinear A.toGrp b (Over.mk s) n).symm))

/-- The comparison preserves every prescribed coordinate, rather than only
the abstract isomorphism class of the fibre module. -/
theorem torsionTupleFibreComparison_apply (b : S' ⟶ S)
    (f : Over.mk b ⟶ torsionTupleScheme A g n)
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ S')
    (i : Fin (2 * g)) :
    torsionTupleFibreComparison A g n b f s
        (fibreTuple (pullbackTuple f.left (tautologicalTorsionTuple A g n)) s i) =
      fibreTuple (torsionTupleSectionEquiv A g n b f) s i := by
  apply (levelBaseChangeLinear A.toGrp b (Over.mk s) n).injective
  change (levelBaseChangeLinear A.toGrp b (Over.mk s) n)
    ((levelBaseChangeLinear A.toGrp b (Over.mk s) n).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  have hpb := fibreTuple_pullback f.left (tautologicalTorsionTuple A g n) s i
  change (levelBaseChangeLinear _ f.left (Over.mk s) n)
    (fibreTuple (pullbackTuple f.left (tautologicalTorsionTuple A g n)) s i) = _ at hpb
  have h1 := congrArg
    (fun x : Level ((baseChange (torsionTupleScheme A g n).hom).obj A).toGrp
        (Over.mk (s ≫ f.left)) n =>
      (levelTestIsoLinear A.toGrp (torsionTuplePointIso A g n b f s) n)
        (levelBaseChangeLinear A.toGrp (torsionTupleScheme A g n).hom
          (Over.mk (s ≫ f.left)) n x)) hpb
  refine h1.trans ?_
  have h2 := congrArg
    (levelTestIsoLinear A.toGrp (torsionTuplePointIso A g n b f s) n)
    (sectionTupleBaseChangeEquiv_fibre A g n (torsionTupleScheme A g n).hom
      (tautologicalTorsionTuple A g n) (s ≫ f.left) i)
  refine h2.trans ?_
  rw [sectionTupleBaseChangeEquiv_tautological]
  refine Eq.trans ?_ (sectionTupleBaseChangeEquiv_fibre A g n b
    (torsionTupleSectionEquiv A g n b f) s i).symm
  have hv :
      sectionTupleBaseChangeEquiv A g n b (torsionTupleSectionEquiv A g n b f) i =
        torsionTupleHomEquiv A g n (Over.mk b) f i := by
    exact congrFun ((sectionTupleBaseChangeEquiv A g n b).apply_symm_apply
      (torsionTupleHomEquiv A g n (Over.mk b) f)) i
  rw [hv]
  apply toSection_injective A.toGrp (Over.mk (s ≫ b)) n
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ ((s ≫ f.left) ≫ ((Pi.π (fun _ : Fin (2 * g) =>
      (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X) i).left ≫
      (GroupScheme.kernelι (GroupScheme.multiplication A.toGrp (n : ℤ))).hom.hom.left)) =
    s ≫ ((f.left ≫ (Pi.π (fun _ : Fin (2 * g) =>
      (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X) i).left) ≫
      (GroupScheme.kernelι (GroupScheme.multiplication A.toGrp (n : ℤ))).hom.hom.left)
  simp only [Category.id_comp, Category.assoc]

/-- A decoded tuple is full exactly when the corresponding pullback of the
tautological tuple is full. -/
theorem isFull_torsionTupleSectionEquiv_iff (b : S' ⟶ S)
    (f : Over.mk b ⟶ torsionTupleScheme A g n) :
    IsFull (torsionTupleSectionEquiv A g n b f) ↔
      IsFull (pullbackTuple f.left (tautologicalTorsionTuple A g n)) := by
  constructor
  · intro h K _ _ s
    obtain ⟨bs, hbs⟩ := h K s
    refine ⟨bs.map (torsionTupleFibreComparison A g n b f s).symm, ?_⟩
    intro i
    apply (torsionTupleFibreComparison A g n b f s).injective
    change (torsionTupleFibreComparison A g n b f s)
      ((torsionTupleFibreComparison A g n b f s).symm (bs i)) = _
    rw [LinearEquiv.apply_symm_apply, hbs i]
    exact (torsionTupleFibreComparison_apply A g n b f s i).symm
  · intro h K _ _ s
    obtain ⟨bs, hbs⟩ := h K s
    refine ⟨bs.map (torsionTupleFibreComparison A g n b f s), ?_⟩
    intro i
    change torsionTupleFibreComparison A g n b f s (bs i) = _
    rw [hbs i]
    exact torsionTupleFibreComparison_apply A g n b f s i

/-- The full-level open subscheme of the actual ordered-tuple parameter. -/
def fullLevelParameterLocus (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    (torsionTupleScheme A g n).left.Opens :=
  fullLevelLocus (tautologicalTorsionTuple A g n) hn
    (Tate.isUnit_natCast_pullback (torsionTupleScheme A g n).hom n hunit)

/-- The actual full-level parameter scheme over the original base. -/
def fullLevelParameterScheme (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) : Over S :=
  Over.mk ((fullLevelParameterLocus A g n hn hunit).ι ≫ (torsionTupleScheme A g n).hom)

/-- The actual inclusion into the scheme of all ordered tuples. -/
def fullLevelParameterInclusion (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    fullLevelParameterScheme A g n hn hunit ⟶ torsionTupleScheme A g n :=
  Over.homMk (fullLevelParameterLocus A g n hn hunit).ι rfl

/-- Maps to the parameter scheme are exactly maps to the tuple scheme whose
decoded ordered tuple is full. -/
def fullLevelParameterHomTupleEquiv (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (T : Over S) :
    (T ⟶ fullLevelParameterScheme A g n hn hunit) ≃
      {f : T ⟶ torsionTupleScheme A g n //
        IsFull (torsionTupleSectionEquiv A g n T.hom f)} where
  toFun f := ⟨f ≫ fullLevelParameterInclusion A g n hn hunit,
    (isFull_torsionTupleSectionEquiv_iff A g n T.hom _).mpr
      ((fullLevelLocusHomEquiv (tautologicalTorsionTuple A g n) hn
        (Tate.isUnit_natCast_pullback (torsionTupleScheme A g n).hom n hunit)
        T.left f.left).property)⟩
  invFun f := Over.homMk
    (fullLevelLocusLift (tautologicalTorsionTuple A g n) hn
      (Tate.isUnit_natCast_pullback (torsionTupleScheme A g n).hom n hunit) f.val.left
      ((isFull_torsionTupleSectionEquiv_iff A g n T.hom f.val).mp f.property)) (by
        change (_ ≫ (fullLevelParameterLocus A g n hn hunit).ι) ≫
          (torsionTupleScheme A g n).hom = T.hom
        dsimp only [fullLevelParameterLocus]
        rw [fullLevelLocusLift_fac]
        exact f.val.w)
  left_inv f := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (fullLevelParameterLocus A g n hn hunit).ι).mp
    dsimp only [fullLevelParameterInclusion, Over.homMk, Over.comp_left]
    apply fullLevelLocusLift_fac
    exact (fullLevelLocusHomEquiv (tautologicalTorsionTuple A g n) hn
      (Tate.isUnit_natCast_pullback (torsionTupleScheme A g n).hom n hunit)
      T.left f.left).property
  right_inv f := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    dsimp only [fullLevelParameterInclusion, Over.homMk, Over.comp_left]
    apply fullLevelLocusLift_fac
    exact (isFull_torsionTupleSectionEquiv_iff A g n T.hom f.val).mp f.property

/-- For every actual test scheme over S, maps to the parameter scheme
classify exactly the unchanged full levels on the actual pulled-back family. -/
def fullLevelParameterHomEquiv (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (T : Over S) :
    (T ⟶ fullLevelParameterScheme A g n hn hunit) ≃
      FullLevel ((baseChange T.hom).obj A) g n :=
  (fullLevelParameterHomTupleEquiv A g n hn hunit T).trans
    (((torsionTupleSectionEquiv A g n T.hom).subtypeEquivOfSubtype).trans
      { toFun := fun v => ⟨v.val, v.property⟩
        invFun := fun v => ⟨v.sections, v.full⟩
        left_inv := fun _ => rfl
        right_inv := fun v => by cases v; rfl })

/-- The classifying map retains its exact decoded ordered sections. -/
@[simp]
theorem fullLevelParameterHomEquiv_sections
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (T : Over S)
    (f : T ⟶ fullLevelParameterScheme A g n hn hunit) :
    (fullLevelParameterHomEquiv A g n hn hunit T f).sections =
      torsionTupleSectionEquiv A g n T.hom
        (f ≫ fullLevelParameterInclusion A g n hn hunit) :=
  rfl

/-- In the original actual torsion modules, classification commutes with every
actual map of test schemes over S. -/
theorem fullLevelParameterHomEquiv_comp
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) {T T' : Over S} (a : T' ⟶ T)
    (f : T ⟶ fullLevelParameterScheme A g n hn hunit) (i : Fin (2 * g)) :
    sectionTupleBaseChangeEquiv A g n T'.hom
        (fullLevelParameterHomEquiv A g n hn hunit T' (a ≫ f)).sections i =
      levelRestrict A.toGrp a n
        (sectionTupleBaseChangeEquiv A g n T.hom
          (fullLevelParameterHomEquiv A g n hn hunit T f).sections i) := by
  have heq (U : Over S) (l : U ⟶ fullLevelParameterScheme A g n hn hunit) :
      sectionTupleBaseChangeEquiv A g n U.hom
          (fullLevelParameterHomEquiv A g n hn hunit U l).sections =
        torsionTupleHomEquiv A g n U
          (l ≫ fullLevelParameterInclusion A g n hn hunit) :=
    (sectionTupleBaseChangeEquiv A g n U.hom).apply_symm_apply _
  rw [heq T' (a ≫ f), heq T f, Category.assoc]
  exact torsionTupleHomEquiv_comp A g n a _ i

/-- The universal full level on the family over its actual full-level parameter. -/
def fullLevelParameterUniversalLevel (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    FullLevel ((baseChange (fullLevelParameterScheme A g n hn hunit).hom).obj A) g n :=
  fullLevelParameterHomEquiv A g n hn hunit
    (fullLevelParameterScheme A g n hn hunit) (𝟙 _)

end Langlands.AbelianScheme.PolarizedFiniteLevel
