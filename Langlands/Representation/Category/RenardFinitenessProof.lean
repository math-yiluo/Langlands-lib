import Langlands.Representation.Category.RenardFinitenessStatement
import Langlands.CategoryTheory.RenardModuleFiniteTypeProof
import Langlands.CategoryTheory.Renard.SubobjectSimpleCokernel
import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Source categorical finiteness for smooth representations

The actual smooth subobject order is the actual group-algebra submodule
order. This transports Renard's finite-type condition and composition chains.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra

namespace Langlands.SmoothRep

universe uR uG uV

variable {R : Type uR} {G : Type uG}
variable [CommRing R] [Group G] [TopologicalSpace G]

section Subobjects

variable (A : SmoothRep.{uR, uG, uV} R G)

private local instance mono_hom {B : SmoothRep.{uR, uG, uV} R G}
    (f : B ⟶ A) [Mono f] : Mono f.hom :=
  toRep.map_mono f

private def subobjectToRep : Subobject A → Subobject A.obj :=
  Subobject.lift (fun {_} f _ => Subobject.mk f.hom) (by
    intro B C f g _ _ e w
    exact Subobject.mk_eq_mk_of_comm f.hom g.hom (toRep.mapIso e)
      (congrArg (fun k : B ⟶ A => k.hom) w))

private theorem subobjectToRep_le_iff (P Q : Subobject A) :
    subobjectToRep A P ≤ subobjectToRep A Q ↔ P ≤ Q := by
  induction P, Q using Subobject.ind₂ with
  | _ f g =>
    change Subobject.mk f.hom ≤ Subobject.mk g.hom ↔
      Subobject.mk f ≤ Subobject.mk g
    constructor
    · intro h
      exact Subobject.mk_le_mk_of_comm
        (ObjectProperty.homMk (Subobject.ofMkLEMk f.hom g.hom h))
        (ObjectProperty.hom_ext _ (Subobject.ofMkLEMk_comp h))
    · intro h
      exact Subobject.mk_le_mk_of_comm (Subobject.ofMkLEMk f g h).hom
        (congrArg (fun k => k.hom) (Subobject.ofMkLEMk_comp h))

private theorem subobjectToRep_surjective :
    Function.Surjective (subobjectToRep A) := by
  intro P
  let B : SmoothRep.{uR, uG, uV} R G :=
    ⟨(P : Rep.{uV} R G), (smoothRepProperty R G).prop_of_mono P.arrow A.property⟩
  let f : B ⟶ A := ObjectProperty.homMk P.arrow
  let : Mono f := toRep.mono_of_mono_map
    (f := f) (inferInstance : Mono P.arrow)
  exact ⟨Subobject.mk f, Subobject.mk_arrow P⟩

/-- Forgetting the smoothness certificate preserves and reflects all actual
subobjects; every ambient subrepresentation is smooth. -/
def repSubobjectOrderIso : Subobject A ≃o Subobject A.obj where
  toFun := subobjectToRep A
  invFun := fun P => (subobjectToRep_surjective A P).choose
  left_inv P := by
    apply le_antisymm
    · exact (subobjectToRep_le_iff A _ _).1
        (le_of_eq (subobjectToRep_surjective A _).choose_spec)
    · exact (subobjectToRep_le_iff A _ _).1
        (le_of_eq (subobjectToRep_surjective A _).choose_spec.symm)
  right_inv P := (subobjectToRep_surjective A P).choose_spec
  map_rel_iff' := subobjectToRep_le_iff A _ _

/-- The actual representation/group-algebra functor identifies subobjects in
the smooth category with subobjects of its actual group-algebra module. -/
def moduleSubobjectOrderIso :
    Subobject A ≃o Subobject (ModuleCat.of R[G] A.representation.asModule) :=
  (repSubobjectOrderIso A).trans
    (Subobject.lowerEquivalence
      (MonoOver.congr A.obj Rep.equivalenceModuleMonoidAlgebra)).toOrderIso

/-- All smooth categorical subobjects are the actual group-algebra submodules. -/
def groupAlgebraSubobjectOrderIso :
    Subobject A ≃o Submodule R[G] A.representation.asModule :=
  (moduleSubobjectOrderIso A).trans (ModuleCat.subobjectModule _)

end Subobjects

section FiniteType

private theorem finiteType_of_subobjectOrderIso
    {C D : Type*} [Category C] [Category D] {X : C} {Y : D}
    (e : Subobject X ≃o Subobject Y)
    (hY : Langlands.Renard.IsFiniteTypeObject Y) :
    Langlands.Renard.IsFiniteTypeObject X := by
  constructor
  · intro S
    obtain ⟨U, hU⟩ := hY.1 (e '' S)
    exact ⟨e.symm U, e.isLUB_image.mp hU⟩
  · intro S hn hc hp htop
    apply hY.2 (e '' S) (hn.image e)
    · rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ hne
      rcases hc hP hQ (fun heq => hne (congrArg e heq)) with h | h
      · exact Or.inl (e.monotone h)
      · exact Or.inr (e.monotone h)
    · rintro _ ⟨P, hP, rfl⟩ h
      exact hp P hP (e.injective (by simpa using h))
    · simpa using e.isLUB_image'.mpr htop

/-- Source finite type is finite generation for the actual group-algebra action. -/
theorem renardFiniteType_iff (A : SmoothRep.{uR, uG, uV} R G) :
    Langlands.Renard.IsFiniteTypeObject A ↔
      Module.Finite R[G] A.representation.asModule := by
  let e := moduleSubobjectOrderIso A
  exact (show Langlands.Renard.IsFiniteTypeObject A ↔
      Langlands.Renard.IsFiniteTypeObject
        (ModuleCat.of R[G] A.representation.asModule) from
    ⟨finiteType_of_subobjectOrderIso e.symm,
      finiteType_of_subobjectOrderIso e⟩).trans
        (Langlands.Renard.ModuleFiniteType.finiteType_iff_finite _)

end FiniteType

section FiniteLength

/-- Source composition chains are exactly finite composition series of the
actual group-algebra module. -/
theorem renardFiniteLength_iff (A : SmoothRep.{uR, uG, uV} R G) :
    Langlands.Renard.IsFiniteLength A ↔ A.HasFiniteLength := by
  let e := groupAlgebraSubobjectOrderIso A
  rw [HasFiniteLength, isFiniteLength_iff_exists_compositionSeries]
  constructor
  · rintro ⟨n, ⟨c⟩⟩
    let s : CompositionSeries (Submodule R[G] A.representation.asModule) :=
      { length := n
        toFun := fun i => e (c.subobject i)
        step := fun i => (apply_covBy_apply_iff e).mpr
          (Langlands.Renard.covBy_of_simple_cokernel (c.le_succ i) (c.simple_factor i)) }
    refine ⟨s, ?_, ?_⟩
    · change e (c.subobject 0) = ⊥
      rw [c.subobject_zero, e.map_bot]
    · change e (c.subobject (Fin.last n)) = ⊤
      rw [c.subobject_last, e.map_top]
  · rintro ⟨s, hs0, hsn⟩
    refine ⟨s.length, ⟨{
      subobject := fun i => e.symm (s i)
      strictMono := e.symm.strictMono.comp s.strictMono
      subobject_zero := ?_
      subobject_last := ?_
      simple_factor := ?_ }⟩⟩
    · change e.symm s.head = ⊥
      rw [hs0, e.symm.map_bot]
    · change e.symm s.last = ⊤
      rw [hsn, e.symm.map_top]
    · intro i
      exact Langlands.Renard.simple_cokernel_of_covBy _
        ((apply_covBy_apply_iff e.symm).mpr (s.step i))

end FiniteLength

/-- Both exact published finiteness comparisons, with independent coefficient,
group and carrier universes and including zero objects. -/
theorem renardFinitenessStatement :
    RenardFinitenessStatement.{uR, uG, uV} (R := R) (G := G) := by
  constructor
  · intro _ A
    exact renardFiniteType_iff A
  · intro _ A
    exact renardFiniteLength_iff A

end Langlands.SmoothRep
