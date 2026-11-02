import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevelParameter
import Mathlib.CategoryTheory.Yoneda

/-! # Isomorphisms of supplied families and their full-level parameters -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {S S' : Scheme.{u}} {A B C : AbelianScheme S} (g n : ℕ)

/-- An actual isomorphism of supplied abelian schemes transports all
actual maps into their tuple parameters. -/
def torsionTupleIsoHomEquiv (e : A ≅ B) (T : Over S) :
    (T ⟶ torsionTupleScheme A g n) ≃ (T ⟶ torsionTupleScheme B g n) :=
  (torsionTupleHomEquiv A g n T).trans
    ((Equiv.piCongrRight fun _ : Fin (2 * g) => (levelIsoLinear e T n).toEquiv).trans
      (torsionTupleHomEquiv B g n T).symm)

/-- The comparison is the prescribed actual torsion isomorphism on
every coordinate. -/
@[simp]
theorem torsionTupleIsoHomEquiv_apply (e : A ≅ B) (T : Over S)
    (f : T ⟶ torsionTupleScheme A g n) (i : Fin (2 * g)) :
    torsionTupleHomEquiv B g n T (torsionTupleIsoHomEquiv g n e T f) i =
      levelIsoLinear e T n (torsionTupleHomEquiv A g n T f i) := by
  exact congrFun ((torsionTupleHomEquiv B g n T).apply_symm_apply _) i

/-- Isomorphism transport commutes with every actual test-scheme morphism. -/
theorem torsionTupleIsoHomEquiv_comp (e : A ≅ B)
    {T T' : Over S} (a : T' ⟶ T) (f : T ⟶ torsionTupleScheme A g n) :
    torsionTupleIsoHomEquiv g n e T' (a ≫ f) =
      a ≫ torsionTupleIsoHomEquiv g n e T f := by
  apply (torsionTupleHomEquiv B g n T').injective
  funext i
  rw [torsionTupleIsoHomEquiv_apply, torsionTupleHomEquiv_comp,
    torsionTupleHomEquiv_comp, torsionTupleIsoHomEquiv_apply]
  apply toSection_injective B.toGrp T' n
  exact Category.assoc a
    (Additive.toMul (torsionTupleHomEquiv A g n T f i)).val
    (groupHom e.hom).hom.hom

/-- Identity transport fixes every actual tuple-parameter map. -/
@[simp]
theorem torsionTupleIsoHomEquiv_refl (T : Over S)
    (f : T ⟶ torsionTupleScheme A g n) :
    torsionTupleIsoHomEquiv g n (Iso.refl A) T f = f := by
  apply (torsionTupleHomEquiv A g n T).injective
  funext i
  rw [torsionTupleIsoHomEquiv_apply]
  apply toSection_injective A.toGrp T n
  change (Additive.toMul (torsionTupleHomEquiv A g n T f i)).val ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Successive family isomorphisms transport the same prescribed tuple
as their composite. -/
theorem torsionTupleIsoHomEquiv_trans (e : A ≅ B) (d : B ≅ C) (T : Over S)
    (f : T ⟶ torsionTupleScheme A g n) :
    torsionTupleIsoHomEquiv g n (e ≪≫ d) T f =
      torsionTupleIsoHomEquiv g n d T (torsionTupleIsoHomEquiv g n e T f) := by
  apply (torsionTupleHomEquiv C g n T).injective
  funext i
  rw [torsionTupleIsoHomEquiv_apply, torsionTupleIsoHomEquiv_apply,
    torsionTupleIsoHomEquiv_apply]
  apply toSection_injective C.toGrp T n
  exact (Category.assoc (Additive.toMul (torsionTupleHomEquiv A g n T f i)).val
    (groupHom e.hom).hom.hom (groupHom d.hom).hom.hom).symm

/-- The tuple-section comparison commutes with the actual pulled-back
family isomorphism. -/
theorem sectionTupleBaseChangeEquiv_mapIso (e : A ≅ B) (b : S' ⟶ S)
    (v : SectionTuple ((baseChange b).obj A) g n) (i : Fin (2 * g)) :
    sectionTupleBaseChangeEquiv B g n b
        (mapTuple ((baseChange b).mapIso e).hom v) i =
      levelIsoLinear e (Over.mk b) n (sectionTupleBaseChangeEquiv A g n b v i) := by
  apply toSection_injective B.toGrp (Over.mk b) n
  apply Over.OverMorphism.ext
  change (𝟙 _ ≫ ((Additive.toMul (v i)).val.left ≫
      (pullback.lift (pullback.fst A.X.hom b ≫ (groupHom e.hom).hom.hom.left)
        (pullback.snd A.X.hom b) _))) ≫ pullback.fst B.X.hom b =
    ((𝟙 _ ≫ (Additive.toMul (v i)).val.left) ≫ pullback.fst A.X.hom b) ≫
      (groupHom e.hom).hom.hom.left
  simp only [Category.id_comp, Category.assoc, pullback.lift_fst]

/-- Decoded ordered sections are transported by the actual isomorphism
of pulled-back abelian schemes. -/
theorem torsionTupleIsoHomEquiv_sections (e : A ≅ B) (T : Over S)
    (f : T ⟶ torsionTupleScheme A g n) :
    torsionTupleSectionEquiv B g n T.hom (torsionTupleIsoHomEquiv g n e T f) =
      mapTuple ((baseChange T.hom).mapIso e).hom
        (torsionTupleSectionEquiv A g n T.hom f) := by
  apply (sectionTupleBaseChangeEquiv B g n T.hom).injective
  funext i
  rw [sectionTupleBaseChangeEquiv_mapIso]
  change (sectionTupleBaseChangeEquiv B g n T.hom)
    ((sectionTupleBaseChangeEquiv B g n T.hom).symm _) i = _
  rw [Equiv.apply_symm_apply]
  erw [torsionTupleIsoHomEquiv_apply]
  congr 1
  exact (congrFun ((sectionTupleBaseChangeEquiv A g n T.hom).apply_symm_apply _) i).symm

private theorem mapTuple_inv_hom (e : A ≅ B) (v : SectionTuple A g n) :
    mapTuple e.inv (mapTuple e.hom v) = v := by
  funext i
  apply toSection_injective A.toGrp (Over.mk (𝟙 S)) n
  change ((Additive.toMul (v i)).val ≫ (groupHom e.hom).hom.hom) ≫
    (groupHom e.inv).hom.hom = (Additive.toMul (v i)).val
  rw [Category.assoc]
  change (Additive.toMul (v i)).val ≫ (groupHom (e.hom ≫ e.inv)).hom.hom = _
  rw [e.hom_inv_id]
  exact Category.comp_id _

/-- Fullness is invariant under isomorphism transport of actual parameter maps. -/
theorem isFull_torsionTupleIsoHomEquiv_iff (e : A ≅ B) (T : Over S)
    (f : T ⟶ torsionTupleScheme A g n) :
    IsFull (torsionTupleSectionEquiv A g n T.hom f) ↔
      IsFull (torsionTupleSectionEquiv B g n T.hom
        (torsionTupleIsoHomEquiv g n e T f)) := by
  rw [torsionTupleIsoHomEquiv_sections]
  constructor
  · intro h
    exact h.mapIso ((baseChange T.hom).mapIso e)
  · intro h
    have h' := h.mapIso ((baseChange T.hom).mapIso e).symm
    change IsFull (mapTuple ((baseChange T.hom).mapIso e).inv
      (mapTuple ((baseChange T.hom).mapIso e).hom
        (torsionTupleSectionEquiv A g n T.hom f))) at h'
    rwa [mapTuple_inv_hom] at h'

/-- An actual family isomorphism transports maps into the full-level
parameter schemes. -/
def fullLevelParameterIsoHomEquiv
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (e : A ≅ B) (T : Over S) :
    (T ⟶ fullLevelParameterScheme A g n hn hunit) ≃
      (T ⟶ fullLevelParameterScheme B g n hn hunit) :=
  (fullLevelParameterHomTupleEquiv A g n hn hunit T).trans
    (((torsionTupleIsoHomEquiv g n e T).subtypeEquiv
      (fun f => isFull_torsionTupleIsoHomEquiv_iff g n e T f)).trans
      (fullLevelParameterHomTupleEquiv B g n hn hunit T).symm)

/-- The full-level comparison retains the actual tuple comparison. -/
@[simp]
theorem fullLevelParameterIsoHomEquiv_inclusion
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (e : A ≅ B) (T : Over S)
    (f : T ⟶ fullLevelParameterScheme A g n hn hunit) :
    fullLevelParameterIsoHomEquiv g n hn hunit e T f ≫
        fullLevelParameterInclusion B g n hn hunit =
      torsionTupleIsoHomEquiv g n e T
        (f ≫ fullLevelParameterInclusion A g n hn hunit) := by
  exact congrArg Subtype.val
    ((fullLevelParameterHomTupleEquiv B g n hn hunit T).apply_symm_apply _)

/-- Full-level transport commutes with every actual test-scheme map. -/
theorem fullLevelParameterIsoHomEquiv_comp
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (e : A ≅ B) {T T' : Over S} (a : T' ⟶ T)
    (f : T ⟶ fullLevelParameterScheme A g n hn hunit) :
    fullLevelParameterIsoHomEquiv g n hn hunit e T' (a ≫ f) =
      a ≫ fullLevelParameterIsoHomEquiv g n hn hunit e T f := by
  apply (fullLevelParameterHomTupleEquiv B g n hn hunit T').injective
  apply Subtype.ext
  change fullLevelParameterIsoHomEquiv g n hn hunit e T' (a ≫ f) ≫
      fullLevelParameterInclusion B g n hn hunit =
    (a ≫ fullLevelParameterIsoHomEquiv g n hn hunit e T f) ≫
      fullLevelParameterInclusion B g n hn hunit
  simp only [fullLevelParameterIsoHomEquiv_inclusion, Category.assoc]
  exact torsionTupleIsoHomEquiv_comp g n e a _

/-- Identity transport fixes every actual full-level parameter map. -/
@[simp]
theorem fullLevelParameterIsoHomEquiv_refl
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (T : Over S)
    (f : T ⟶ fullLevelParameterScheme A g n hn hunit) :
    fullLevelParameterIsoHomEquiv g n hn hunit (Iso.refl A) T f = f := by
  apply (fullLevelParameterHomTupleEquiv A g n hn hunit T).injective
  apply Subtype.ext
  change fullLevelParameterIsoHomEquiv g n hn hunit (Iso.refl A) T f ≫
      fullLevelParameterInclusion A g n hn hunit =
    f ≫ fullLevelParameterInclusion A g n hn hunit
  rw [fullLevelParameterIsoHomEquiv_inclusion, torsionTupleIsoHomEquiv_refl]

/-- Full-level parameter-map transport respects composition of actual
family isomorphisms. -/
theorem fullLevelParameterIsoHomEquiv_trans
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (e : A ≅ B) (d : B ≅ C) (T : Over S)
    (f : T ⟶ fullLevelParameterScheme A g n hn hunit) :
    fullLevelParameterIsoHomEquiv g n hn hunit (e ≪≫ d) T f =
      fullLevelParameterIsoHomEquiv g n hn hunit d T
        (fullLevelParameterIsoHomEquiv g n hn hunit e T f) := by
  apply (fullLevelParameterHomTupleEquiv C g n hn hunit T).injective
  apply Subtype.ext
  change fullLevelParameterIsoHomEquiv g n hn hunit (e ≪≫ d) T f ≫
      fullLevelParameterInclusion C g n hn hunit =
    fullLevelParameterIsoHomEquiv g n hn hunit d T
      (fullLevelParameterIsoHomEquiv g n hn hunit e T f) ≫
        fullLevelParameterInclusion C g n hn hunit
  simp only [fullLevelParameterIsoHomEquiv_inclusion, torsionTupleIsoHomEquiv_trans]

/-- Classified full levels retain the exact ordered sections through the
pulled-back family isomorphism. -/
theorem fullLevelParameterIsoHomEquiv_sections
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (e : A ≅ B) (T : Over S)
    (f : T ⟶ fullLevelParameterScheme A g n hn hunit) :
    (fullLevelParameterHomEquiv B g n hn hunit T
        (fullLevelParameterIsoHomEquiv g n hn hunit e T f)).sections =
      mapTuple ((baseChange T.hom).mapIso e).hom
        (fullLevelParameterHomEquiv A g n hn hunit T f).sections := by
  change torsionTupleSectionEquiv B g n T.hom
      (fullLevelParameterIsoHomEquiv g n hn hunit e T f ≫
        fullLevelParameterInclusion B g n hn hunit) =
    mapTuple ((baseChange T.hom).mapIso e).hom
      (torsionTupleSectionEquiv A g n T.hom
        (f ≫ fullLevelParameterInclusion A g n hn hunit))
  erw [fullLevelParameterIsoHomEquiv_inclusion]
  exact torsionTupleIsoHomEquiv_sections g n e T
    (f ≫ fullLevelParameterInclusion A g n hn hunit)

/-- The actual full-level parameters of isomorphic supplied families are
isomorphic over the original base scheme. -/
def fullLevelParameterIso
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (e : A ≅ B) :
    fullLevelParameterScheme A g n hn hunit ≅
      fullLevelParameterScheme B g n hn hunit :=
  Yoneda.ext _ _ (fun {T} => fullLevelParameterIsoHomEquiv g n hn hunit e T)
    (fun {T} => (fullLevelParameterIsoHomEquiv g n hn hunit e T).symm)
    (fun f => (fullLevelParameterIsoHomEquiv g n hn hunit e _).symm_apply_apply f)
    (fun f => (fullLevelParameterIsoHomEquiv g n hn hunit e _).apply_symm_apply f)
    (fun a f => fullLevelParameterIsoHomEquiv_comp g n hn hunit e a f)

/-- On every actual test scheme the parameter isomorphism realizes the
prescribed coordinatewise full-level transport. -/
theorem fullLevelParameterIso_hom_comp
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (e : A ≅ B) (T : Over S)
    (f : T ⟶ fullLevelParameterScheme A g n hn hunit) :
    f ≫ (fullLevelParameterIso g n hn hunit e).hom =
      fullLevelParameterIsoHomEquiv g n hn hunit e T f := by
  change f ≫ fullLevelParameterIsoHomEquiv g n hn hunit e _ (𝟙 _) = _
  rw [← fullLevelParameterIsoHomEquiv_comp, Category.comp_id]

/-- The parameter isomorphism carries each classified ordered section
through the actual pulled-back family isomorphism. -/
theorem fullLevelParameterIso_hom_sections
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (e : A ≅ B) (T : Over S)
    (f : T ⟶ fullLevelParameterScheme A g n hn hunit) :
    (fullLevelParameterHomEquiv B g n hn hunit T
        (f ≫ (fullLevelParameterIso g n hn hunit e).hom)).sections =
      mapTuple ((baseChange T.hom).mapIso e).hom
        (fullLevelParameterHomEquiv A g n hn hunit T f).sections := by
  rw [fullLevelParameterIso_hom_comp]
  exact fullLevelParameterIsoHomEquiv_sections g n hn hunit e T f

/-- The identity family isomorphism induces the identity parameter
isomorphism. -/
@[simp]
theorem fullLevelParameterIso_refl
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    fullLevelParameterIso g n hn hunit (Iso.refl A) = Iso.refl _ := by
  apply Iso.ext
  exact fullLevelParameterIsoHomEquiv_refl g n hn hunit _ (𝟙 _)

/-- Parameter isomorphisms respect composition of actual family
isomorphisms. -/
theorem fullLevelParameterIso_trans
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (e : A ≅ B) (d : B ≅ C) :
    fullLevelParameterIso g n hn hunit (e ≪≫ d) =
      fullLevelParameterIso g n hn hunit e ≪≫ fullLevelParameterIso g n hn hunit d := by
  apply Iso.ext
  change fullLevelParameterIsoHomEquiv g n hn hunit (e ≪≫ d) _ (𝟙 _) = _
  rw [fullLevelParameterIsoHomEquiv_trans]
  exact (fullLevelParameterIso_hom_comp g n hn hunit d _
    (fullLevelParameterIso g n hn hunit e).hom).symm

end Langlands.AbelianScheme.PolarizedFiniteLevel
